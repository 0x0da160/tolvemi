import json, re, copy, csv, hashlib, sys, platform
from pathlib import Path
from collections import Counter
import importlib.metadata
import jsonschema

class Cutoff(Exception):
    pass

class TypeTraceModel:
    def __init__(self, limit=2000000):
        self.limit=limit; self.events=[]; self.diagnostics=[]
    def event(self, name):
        if len(self.events)+1>self.limit:
            self.diagnostics.append('E-LIMIT-STATIC-SEMANTIC-WORK'); raise Cutoff()
        self.events.append(name)
    def eq(self,a,b):
        if a is None or b is None: return True
        self.event('CompareType')
        if a[0]!=b[0]: return False
        return all(self.eq(x,y) for x,y in zip(a[1:],b[1:]))
    def expr(self,e,env):
        self.event('VisitExpr'); tag=e['tag']
        if tag=='var': return env[e['name']]
        if tag in ('int','bool','unit'):
            self.event('BuildType'); return (tag,)
        if tag=='none': self.event('BuildType'); return ('option',('int',))
        if tag=='some':
            a=self.expr(e['value'],env)
            if a is None: return None
            self.event('BuildType'); return ('option',a)
        if tag=='list':
            types=[self.expr(x,env) for x in e['items']]
            good=True
            for a in types:
                if not self.eq(a,('int',)): good=False
                if a is None: good=False
            if not good: return None
            self.event('BuildType'); return ('list',('int',))
        if tag=='call' and e['callee']=='add':
            arity=len(e['args'])==2
            if not arity: self.diagnostics.append('E-ARITY-BUILTIN')
            types=[self.expr(x,env) for x in e['args']]
            if not arity: return None
            good=True
            for a in types:
                if not self.eq(a,('int',)): good=False
                if a is None: good=False
            if not good: return None
            self.event('BuildType'); return ('int',)
        raise NotImplementedError(tag)
    def check(self,e,ret,env=None):
        try:
            ty=self.expr(e,env or {'x':('int',)})
            self.eq(ty,ret)
            status='finished'
        except Cutoff: status='cutoff'
        counts=Counter(self.events)
        return {'status':status,'counts':[counts[x] for x in ('VisitExpr','BuildType','CompareType')], 'total':len(self.events),'diagnostics':self.diagnostics}

def identifier(s, reserved):
    return isinstance(s,str) and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',s) is not None and s not in reserved

def ast_shape_model(v, spec, schema):
    def resolve(s):
        if '$ref' in s: return schema['$defs'][s['$ref'].split('/')[-1]]
        return s
    def shallow(x,s):
        s=resolve(s)
        if 'oneOf' in s: return isinstance(x,dict)
        if 'anyOf' in s: return isinstance(x,str)
        t=s.get('type')
        return {'object':isinstance(x,dict),'array':isinstance(x,list),'string':isinstance(x,str),'boolean':type(x) is bool}.get(t,True)
    def content(x,s):
        s=resolve(s)
        if s is schema['$defs']['identifier']:
            return None if identifier(x,s['not']['enum']) else 'E-AST-IDENTIFIER'
        if s.get('type')=='array':
            for a in x:
                r=content(a,s['items'])
                if r: return r
            return None
        if 'anyOf' in s:
            builtins=s['anyOf'][0]['enum']
            return None if x in builtins or identifier(x,schema['$defs']['identifier']['not']['enum']) else 'E-AST-IDENTIFIER'
        if 'oneOf' in s or s.get('type')=='object': return node(x,s)
        if 'pattern' in s: return None if re.fullmatch(r'0|-?[1-9][0-9]*',x) else 'E-AST-INTEGER'
        return None
    def node(x,s):
        if not isinstance(x,dict): return 'E-AST-FIELD-TYPE'
        if 'oneOf' in s:
            if 'tag' not in x: return 'E-AST-MISSING-FIELD'
            if not isinstance(x['tag'],str): return 'E-AST-TAG'
            matches=[z for z in s['oneOf'] if z['properties']['tag']['const']==x['tag']]
            if not matches: return 'E-AST-TAG'
            s=matches[0]
        elif 'codec' in s.get('properties',{}):
            if x.get('codec')!='ast_codec_v1': return 'E-AST-CODEC'
        props=s['properties']
        for k in props:
            if k in s['required'] and k not in x: return 'E-AST-MISSING-FIELD'
        if sorted(set(x)-set(props)): return 'E-AST-UNKNOWN-FIELD'
        for k,sub in props.items():
            if not shallow(x[k],sub): return 'E-AST-FIELD-TYPE'
        for k,sub in props.items():
            r=content(x[k],sub)
            if r: return r
        return None
    return node(v,resolve(spec))

def admission_model(events,limit):
    seen=[]
    for kind in events:
        if len(seen)+1>limit: return {'admitted':len(seen),'next':kind,'cutoff':'AST-NODES'}
        seen.append(kind)
    return {'admitted':len(seen),'next':None,'cutoff':None}

def recovery_model(tokens,s,p,count,guard=False):
    if guard: return {'result':'structural_cutoff','count':count,'q':None}
    if tokens[p]=='EOF': return {'result':'stop_eof','count':count,'q':p}
    if count==8: return {'result':'recovery_limit','count':count,'q':None}
    q=next(i for i in range(max(p,s+1),len(tokens)) if tokens[i] in ('fn','entry','EOF'))
    return {'result':'stop_eof' if tokens[q]=='EOF' else 'resume_keep_token','count':count+1,'q':q}


class JObject(list):
    pass

def parse_json_stage_model(raw):
    try:
        tree=json.loads(raw, object_pairs_hook=JObject)
    except (ValueError, TypeError):
        return None, 'E-INPUT-JSON-SYNTAX'
    def scalar_bad(x):
        if isinstance(x,str): return any(0xD800<=ord(ch)<=0xDFFF for ch in x)
        if isinstance(x,JObject): return any(scalar_bad(k) or scalar_bad(v) for k,v in x)
        if isinstance(x,list): return any(scalar_bad(v) for v in x)
        return False
    def duplicate(x):
        if isinstance(x,JObject):
            seen=set()
            for k,v in x:
                if k in seen: return True
                seen.add(k)
                if duplicate(v): return True
        elif isinstance(x,list):
            return any(duplicate(v) for v in x)
        return False
    if scalar_bad(tree): return None,'E-INPUT-STRING-SCALAR'
    if duplicate(tree): return None,'E-INPUT-DUPLICATE-KEY'
    return tree,None

def input_admission_model(arg):
    tree,code=parse_json_stage_model(arg['json'])
    state={'status':'invalid' if code else 'decoded','code':code,'admitted':0,'depths':[]}
    if code: return state
    class Invalid(Exception): pass
    def fail(code):
        state['status']='invalid';state['code']=code;raise Invalid()
    def decode(x,ty,depth):
        if not isinstance(x,JObject): fail('E-INPUT-FIELD-TYPE')
        d=dict(x)
        if 'tag' not in d: fail('E-INPUT-MISSING-FIELD')
        kind=ty[0] if isinstance(ty,list) else ty
        tags=('some','none') if kind=='option' else (kind,)
        if not isinstance(d['tag'],str) or d['tag'] not in tags: fail('E-INPUT-TAG')
        tag=d['tag']
        keys={'int':['tag','value'],'bool':['tag','value'],'unit':['tag'],
              'none':['tag'],'some':['tag','value'],'pair':['tag','left','right'],
              'list':['tag','items']}[tag]
        if any(k not in d for k in keys): fail('E-INPUT-MISSING-FIELD')
        if set(d)-set(keys): fail('E-INPUT-UNKNOWN-FIELD')
        for k in keys:
            if k=='tag': ok=isinstance(d[k],str)
            elif tag=='int': ok=isinstance(d[k],str)
            elif tag=='bool': ok=type(d[k]) is bool
            elif tag=='list': ok=isinstance(d[k],list) and not isinstance(d[k],JObject)
            else: ok=isinstance(d[k],JObject)
            if not ok: fail('E-INPUT-FIELD-TYPE')
        if depth>arg['depth_limit']: fail('E-LIMIT-INPUT-VALUE-DEPTH')
        if state['admitted']+1>arg['node_limit']: fail('E-LIMIT-INPUT-VALUE-NODES')
        state['admitted']+=1;state['depths'].append(depth)
        if tag=='int':
            v=d['value']
            if re.fullmatch(r'0|-?[1-9][0-9]*',v) is None: fail('E-INPUT-INTEGER')
            if len(v.lstrip('-'))>arg['digit_limit']: fail('E-LIMIT-INPUT-INTEGER-DIGITS')
        elif tag=='some': decode(d['value'],ty[1],depth+1)
        elif tag=='pair':
            decode(d['left'],ty[1],depth+1);decode(d['right'],ty[2],depth+1)
        elif tag=='list':
            for v in d['items']: decode(v,ty[1],depth+1)
    try: decode(tree,arg['type'],1)
    except Invalid: pass
    return state

def strict_budget_vector(observed,limit):
    return (isinstance(observed,list) and isinstance(limit,list) and len(observed)==len(limit)==4
            and all(type(v) is int and v>=0 for v in observed+limit)
            and all(a<=b for a,b in zip(observed,limit)))

def budget_end_model(arg):
    valid_vectors=(len(arg['observed'])==len(arg['limit'])==4
                   and all(type(v) is int and v>=0 for v in arg['observed']+arg['limit']))
    if not valid_vectors:
        return {'reason':'invalid_budget_measurement','budget_ok':False,'selected':None,'success':0}
    selected=next((i for i in range(len(arg['candidates'])-1,-1,-1)
                   if arg['candidates'][i]['accepted']),None)
    budget_ok=strict_budget_vector(arg['observed'],arg['limit'])
    if not budget_ok: reason='budget_exceeded'
    elif selected is None: reason='no_accepted_candidate'
    else: reason=arg['stop_reason']
    success=int(budget_ok and selected is not None and arg['candidates'][selected]['hidden_pass'])
    return {'reason':reason,'budget_ok':budget_ok,'selected':selected,'success':success}

def spec_bound_preimage_model(arg):
    version=arg['spec_version']
    if not isinstance(version,str) or not version or not version.isascii(): return None
    digest=arg['structural_hash']
    if re.fullmatch('[0-9a-f]{64}',digest) is None: raise ValueError('structural hash must be lowercase hex')
    payload=json.dumps([version,'ast_codec_v1',digest],ensure_ascii=False,separators=(',',':'))
    return ('LPTL-spec-bound-syntax-v1\0'+payload).encode().hex()


def run_case(c,schema):
    kind=c['kind']; arg=c['input']
    if kind=='input_admission_model': return input_admission_model(arg)
    if kind=='json_scalar_stage_model': return parse_json_stage_model(arg)[1]
    if kind=='budget_end_model': return budget_end_model(arg)
    if kind=='spec_bound_preimage_model': return spec_bound_preimage_model(arg)
    if kind=='spec_bound_version_separation':
        a=dict(arg); a['spec_version']=arg['version_a']
        b=dict(arg); b['spec_version']=arg['version_b']
        return spec_bound_preimage_model(a)!=spec_bound_preimage_model(b)
    if kind=='schema':
        s=copy.deepcopy(schema)
        if c.get('alternative_anchor_fixture'):
            s['$defs']['identifier']['pattern']=r'^[A-Za-z_][A-Za-z0-9_]*$'
            for z in s['$defs']['expr']['oneOf']:
                if z['properties']['tag']['const']=='int': z['properties']['value']['pattern']=r'^(0|-?[1-9][0-9]*)$'
        return jsonschema.Draft202012Validator(s).is_valid(arg)
    if kind=='ast_shape_model': return ast_shape_model(arg,schema,schema)
    if kind=='type_trace_model':
        def ty(x): return tuple(ty(v) if isinstance(v,list) else v for v in x)
        return TypeTraceModel(arg['limit']).check(arg['expr'],ty(arg['return_type']))
    if kind=='admission_model': return admission_model(arg['events'],arg['limit'])
    if kind=='recovery_model': return recovery_model(**arg)
    if kind=='source_boundary':
        n='f'*arg['name_length']
        s=f'fn {n}(x:Int)->Int=x entry {n}'
        f=f'fn {n}(x: Int) -> Int = x'+chr(10)+'entry '+n+chr(10)
        return [len(s.encode()),len(f.encode())]
    if kind=='int_boundary':
        n=10**arg['exponent']; return {'digits':arg['exponent']+1,'bits':n.bit_length()}
    if kind=='episode_aggregation':
        candidates=arg['candidates']; selected=next((i for i in range(len(candidates)-1,-1,-1) if candidates[i]['accepted']),None)
        success=int(selected is not None and arg['budget_ok'] and candidates[selected]['hidden_pass'])
        return {'episodes':1,'successes':success,'selected':selected,'candidate_count':len(candidates)}
    if kind=='budget_vector': return strict_budget_vector(arg['observed'],arg['limit'])
    if kind=='decoded_duplicate_demo':
        pairs=json.loads(arg,object_pairs_hook=lambda pairs:pairs)
        keys=[p[0] for p in pairs]; return len(keys)!=len(set(keys))
    raise ValueError(kind)

def main(root):
    schema=json.loads((root/'ast_codec_v1.schema.json').read_text())
    jsonschema.Draft202012Validator.check_schema(schema)
    fixture=json.loads((root/'v1_check_inputs.json').read_text())
    results=[]
    for c in fixture['cases']:
        actual=run_case(c,schema)
        results.append({'case':c['id'],'kind':c['kind'],'expected':json.dumps(c['expected'],ensure_ascii=False),'actual':json.dumps(actual,ensure_ascii=False),'pass':actual==c['expected']})
    with (root/'v1_checks.csv').open('w',newline='',encoding='utf-8') as f:
        w=csv.DictWriter(f,fieldnames=list(results[0]));w.writeheader();w.writerows(results)
    print(json.dumps({'cases':len(results),'passed':sum(x['pass'] for x in results),'scope':fixture['scope'],'python':sys.version,'jsonschema':importlib.metadata.version('jsonschema')},ensure_ascii=False))
    assert all(x['pass'] for x in results)

if __name__=='__main__': main(Path(__file__).parent)
