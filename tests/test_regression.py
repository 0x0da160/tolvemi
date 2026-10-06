"""設計書 §20.1 の必須回帰テストと §18 の trace fixture の照合。"""

from __future__ import annotations

import json
import unittest
from dataclasses import replace

from tolvemi import api
from tolvemi.checker import check_program
from tolvemi.formatter import encode_ast, format_program
from tolvemi.profiles import ExecutionProfile, InputProfile, StaticProfile
from tolvemi.syntax import INT, Ty
from tolvemi.values import Decoded, Invalid

S = StaticProfile()


def codes(result):
    if isinstance(result, api.Rejected):
        return [d.code for d in result.errors]
    if isinstance(result, api.Accepted):
        return []
    if hasattr(result, "diagnostics"):
        return [d.code for d in result.diagnostics]
    return [type(result).__name__]


def wcodes(result):
    return [d.code for d in result.warnings]


def ilist(*xs):
    return json.dumps({"tag": "list", "items": [{"tag": "int", "value": str(x)} for x in xs]})


def run_src(src, input_json, profile=ExecutionProfile()):
    r = api.compile(src)
    assert isinstance(r, api.Accepted), codes(r)
    d = api.decode_input(r.program.input_type, input_json)
    assert isinstance(d, Decoded), d
    return api.run(r.program, d, profile)


class EntryAndParse(unittest.TestCase):
    def test_entry_missing(self):
        self.assertEqual(codes(api.compile("fn f(x: Int) -> Int = x")), ["E-ENTRY-MISSING"])

    def test_entry_unknown_no_duplicate(self):
        r = api.compile("fn f(x: Int) -> Int = x entry missing entry f")
        self.assertEqual(codes(r), ["E-ENTRY-UNKNOWN"])
        self.assertEqual(r.errors[0].phase, "name")

    def test_entry_duplicate_once(self):
        r = api.compile("fn f(x: Int) -> Int = x entry f entry f")
        self.assertEqual(codes(r), ["E-ENTRY-DUPLICATE"])
        self.assertEqual(r.errors[0].span, (32, 39))  # 二番目の entry 宣言全体

    def test_entry_arity(self):
        self.assertEqual(codes(api.compile("fn f() -> Int = 0 entry f")), ["E-ENTRY-ARITY"])

    def test_unused_function_warning(self):
        r = api.compile("fn f(x: Int) -> Int = x fn g(y: Int) -> Int = y entry f")
        self.assertIsInstance(r, api.Accepted)
        self.assertEqual(wcodes(r), ["W-UNUSED-FUNCTION"])
        self.assertEqual(r.warnings[0].span, (27, 28))

    def test_unexpected_token_after_expr(self):
        self.assertEqual(codes(api.compile("fn f(x: Int) -> Int = x 1 entry f")),
                         ["E-PARSE-UNEXPECTED-TOKEN"])

    def test_none_foo(self):
        self.assertEqual(codes(api.compile("fn f(x: Int) -> Option<Int> = none[Foo] entry f")),
                         ["E-PARSE-EXPECTED-TYPE"])

    def test_reserved_word_as_name(self):
        self.assertEqual(codes(api.compile("fn if(x: Int) -> Int = x entry if")),
                         ["E-PARSE-EXPECTED-IDENT"] * 2)

    def test_no_newline_needed(self):
        r = api.compile("fn f(x: Int) -> Int = x fn g(y: Int) -> Int = y entry f")
        self.assertEqual(format_program(r.program.program),
                         "fn f(x: Int) -> Int = x\nfn g(y: Int) -> Int = y\nentry f\n")

    def test_recovery_limit(self):
        bad = "fn f(x: Int) -> Int = ) "
        src = bad * 9 + "fn g(x: Int) -> Int = ) entry g"
        r = api.compile(src)
        self.assertEqual(codes(r), ["E-PARSE-EXPECTED-EXPR"] * 9 + ["E-PARSE-RECOVERY-LIMIT"])

    def test_recovery_eight_then_ok(self):
        src = "fn f(x: Int) -> Int = ) " * 8 + "fn g(x: Int) -> Int = x entry g"
        r = api.compile(src)
        self.assertEqual(codes(r), ["E-PARSE-EXPECTED-EXPR"] * 8)

    def test_sync_keeps_fn_in_expr_position(self):
        r = api.compile("fn f(x: Int) -> Int = fn g(y: Int) -> Int = ) entry g")
        self.assertEqual(codes(r), ["E-PARSE-EXPECTED-EXPR", "E-PARSE-EXPECTED-EXPR"])
        self.assertEqual(r.errors[0].span, (22, 24))

    def test_parse_error_at_eof_stops(self):
        r = api.compile("fn f(x: Int) -> Int = add(1,")
        self.assertEqual(codes(r), ["E-PARSE-EXPECTED-EXPR"])

    def test_special_form_missing_part_is_parse_error(self):
        self.assertEqual(codes(api.compile("fn f(x: Int) -> Int = if(true, 1) entry f")),
                         ["E-PARSE-EXPECTED-TOKEN"])


class Lexical(unittest.TestCase):
    def test_numeric_boundary(self):
        self.assertEqual(codes(api.compile("fn f(x: Int) -> Int = 12x entry f")),
                         ["E-LEX-INVALID-NUMERIC-BOUNDARY"])

    def test_minus_forms(self):
        for body in ("1-2", "- 2", "--2"):
            r = api.compile(f"fn f(x: Int) -> Int = {body} entry f")
            self.assertTrue(codes(r)[0].startswith("E-LEX-"), (body, codes(r)))

    def test_negative_literal_ok(self):
        self.assertIsInstance(api.compile("fn f(x: Int) -> Int = sub(1,-2) entry f"), api.Accepted)

    def test_bad_integers(self):
        for lit in ("-0", "+1", "01"):
            r = api.compile(f"fn f(x: Int) -> Int = {lit} entry f")
            self.assertEqual(codes(r), ["E-LEX-INVALID-INTEGER"], lit)

    def test_non_ascii_and_comment(self):
        self.assertEqual(codes(api.compile("fn f(x: Int) -> Int = x entry f // 日本語")), [])
        self.assertEqual(codes(api.compile("fn f(x: Int) -> Int = é entry f")),
                         ["E-LEX-NON-ASCII"])
        self.assertEqual(codes(api.compile(b"\xef\xbb\xbffn f(x: Int) -> Int = x entry f")),
                         ["E-LEX-NON-ASCII"])

    def test_token_limit(self):
        src = "fn f(x: Int) -> Int = x entry f"  # 13 tokens
        p = replace(S, tokens=13)
        self.assertIsInstance(api.compile(src.encode(), p), api.Accepted)
        p = replace(S, tokens=12)
        self.assertEqual(codes(api.compile(src.encode(), p)), ["E-LIMIT-STATIC-TOKENS"])

    def test_source_bytes_before_utf8(self):
        p = replace(S, source_bytes=4)
        self.assertEqual(codes(api.compile(b"\xff\xff\xff\xff\xff", p)),
                         ["E-LIMIT-STATIC-SOURCE-BYTES"])
        self.assertIsInstance(api.compile(b"\xff"), api.SourceBoundaryFailure)

    def test_integer_digits_after_form(self):
        p = replace(S, integer_digits=3)
        self.assertEqual(codes(api.compile(b"fn f(x: Int) -> Int = 1234 entry f", p)),
                         ["E-LIMIT-STATIC-INTEGER-DIGITS"])
        self.assertEqual(codes(api.compile(b"fn f(x: Int) -> Int = 01234 entry f", p)),
                         ["E-LEX-INVALID-INTEGER"])


class TypesArityDag(unittest.TestCase):
    PRE = "fn f(x: Int) -> Int = x "

    def test_arity_user(self):
        r = api.compile(self.PRE + "fn g(u: Unit) -> Int = f(1, true) entry g")
        self.assertEqual(codes(r), ["E-ARITY-USER"])

    def test_arity_builtin(self):
        r = api.compile("fn g(u: Unit) -> Int = add(1, true, 0) entry g")
        self.assertEqual(codes(r), ["E-ARITY-BUILTIN"])

    def test_arity_and_independent_type_error(self):
        r = api.compile(self.PRE + "fn g(u: Unit) -> Int = f(1, fst(unit)) entry g")
        self.assertEqual(sorted(codes(r)), ["E-ARITY-USER", "E-TYPE-FST-ARG"])

    def test_cycle_in_fold(self):
        r = api.compile("fn f(xs: List<Int>) -> Int = fold(xs, 0, |a, x| f(xs)) entry f")
        self.assertEqual(codes(r), ["E-CYCLE-CALL"])

    def test_mutual_recursion_rejected(self):
        r = api.compile("fn f(x: Int) -> Int = g(x) fn g(x: Int) -> Int = f(x) entry f")
        self.assertEqual(codes(r), ["E-CYCLE-CALL"])

    def test_nested_fst_reports_once(self):
        r = api.compile("fn g(u: Option<Pair<Int, List<Int>>>) -> Int = fst(fst(u)) entry g")
        self.assertEqual(codes(r), ["E-TYPE-FST-ARG"])

    def test_if_branch(self):
        r = api.compile("fn g(u: Unit) -> Int = if(true, 1, none[Int]) entry g")
        self.assertEqual(codes(r), ["E-TYPE-IF-BRANCH"])
        self.assertEqual((r.errors[0].expected, r.errors[0].actual), ("Int", "Option<Int>"))

    def test_static_eq_and_concat(self):
        self.assertEqual(codes(api.compile("fn g(u: Unit) -> Bool = eq(1, true) entry g")),
                         ["E-TYPE-EQ-OPERANDS"])
        r = api.compile("fn g(u: Unit) -> List<Int> = concat(list[Int](), list[Bool]()) entry g")
        self.assertEqual(codes(r), ["E-TYPE-ARG"])

    def test_names(self):
        r = api.compile("fn g(x: Int) -> Int = let x = 1 in x entry g")
        self.assertEqual(codes(r), ["E-NAME-SHADOW"])
        r = api.compile("fn g(xs: List<Int>) -> Int = fold(xs, 0, |a, a| a) entry g")
        self.assertEqual(codes(r), ["E-NAME-DUPLICATE-BINDER"])
        r = api.compile("fn g(x: Int) -> Int = let y = y in y entry g")
        self.assertEqual(codes(r), ["E-NAME-UNBOUND-VARIABLE"])
        r = api.compile("fn g(x: Int) -> Int = uncons(x) entry g")
        self.assertEqual(codes(r), ["E-NAME-UNKNOWN-FUNCTION"])

    def test_forward_reference(self):
        r = api.compile("fn g(x: Int) -> Int = h(x) fn h(x: Int) -> Int = x entry g")
        self.assertIsInstance(r, api.Accepted)
        self.assertEqual(r.program.rank, {"h": 0, "g": 1})


class SemanticWork(unittest.TestCase):
    CASES = [
        ("fn f(x: Int) -> Int = x", (1, 0, 1)),
        ("fn f(x: Unit) -> Int = 0", (1, 1, 1)),
        ("fn f(x: Unit) -> Int = add(1, 2)", (3, 3, 3)),
        ("fn f(x: Unit) -> Option<Int> = some(0)", (2, 2, 2)),
        ("fn f(x: Unit) -> List<Int> = list[Int](1, 2)", (3, 3, 4)),
        ("fn f(x: Unit) -> Option<Int> = none[Int]", (1, 1, 2)),
    ]

    def test_trace_fixtures(self):
        for src, (v, b, c) in self.CASES:
            r = api.compile(src + " entry f")
            self.assertIsInstance(r, api.Accepted, src)
            self.assertEqual((r.work.visit, r.work.build, r.work.compare), (v, b, c), src)

    def test_add_work_limit(self):
        src = b"fn f(x: Unit) -> Int = add(1, 2) entry f"
        self.assertIsInstance(api.compile(src, replace(S, semantic_work=9)), api.Accepted)
        r = api.compile(src, replace(S, semantic_work=8))
        self.assertEqual(codes(r), ["E-LIMIT-STATIC-SEMANTIC-WORK"])

    def test_arity_cutoff_ordering(self):
        src = b"fn f(x: Unit) -> Int = add(1, true, 0) entry f"
        self.assertEqual(codes(api.compile(src, replace(S, semantic_work=0))),
                         ["E-LIMIT-STATIC-SEMANTIC-WORK"])
        self.assertEqual(codes(api.compile(src, replace(S, semantic_work=1))),
                         ["E-ARITY-BUILTIN", "E-LIMIT-STATIC-SEMANTIC-WORK"])

    def test_semantic_cutoff_skips_entry_and_warnings(self):
        src = b"fn f(x: Unit) -> Int = add(1, 2) fn g(y: Int) -> Int = y"
        r = api.compile(src, replace(S, semantic_work=3))
        self.assertEqual(codes(r), ["E-LIMIT-STATIC-SEMANTIC-WORK"])
        self.assertEqual(r.warnings, [])

    def test_type_depth_beats_work(self):
        src = b"fn f(x: Unit) -> Option<Int> = some(0) entry f"
        r = api.compile(src, replace(S, semantic_type_depth=1, semantic_work=3))
        self.assertEqual(codes(r), ["E-LIMIT-STATIC-SEMANTIC-TYPE-DEPTH"])


class StructuralLimits(unittest.TestCase):
    def test_admitted_some_child_over_budget(self):
        # program, fn, param, Int, Int, some = 6 → unit が 7 番目
        r = api.compile(b"fn f(x: Int) -> Int = some(unit", replace(S, ast_nodes=6))
        self.assertEqual(codes(r), ["E-LIMIT-STATIC-AST-NODES"])

    def test_depth_limits(self):
        src = b"fn f(x: Int) -> Int = let a = 1 in let b = 2 in a entry f"
        self.assertEqual(codes(api.compile(src, replace(S, let_depth=1))),
                         ["E-LIMIT-STATIC-LET-DEPTH"])
        self.assertIsInstance(api.compile(src, replace(S, let_depth=2)), api.Accepted)
        src = b"fn f(x: List<List<Int>>) -> Int = 0 entry f"
        self.assertEqual(codes(api.compile(src, replace(S, type_depth=2))),
                         ["E-LIMIT-STATIC-TYPE-DEPTH"])

    def test_error_limit(self):
        body = ", ".join(["fst(unit)"] * 40)
        r = api.compile(f"fn f(x: Unit) -> List<Int> = list[Int]({body}) entry f")
        self.assertEqual(len(r.errors), 32)
        self.assertEqual(r.errors[-1].code, "E-DIAG-LIMIT")

    def test_formatter_boundary_fixture(self):
        name = "f" * 524_276
        src = f"fn {name}(x:Int)->Int=x entry {name}".encode()
        self.assertEqual(len(src), 1_048_576)
        r = api.compile(src)
        self.assertIsInstance(r, api.Accepted)
        out = format_program(r.program.program).encode()
        self.assertEqual(len(out), 1_048_582)
        self.assertEqual(codes(api.compile(out)), ["E-LIMIT-STATIC-SOURCE-BYTES"])


class AstTransport(unittest.TestCase):
    IDENT = ('{"codec":"ast_codec_v1","declarations":[{"tag":"fn","name":"identity","params":'
             '[{"name":"x","type":{"tag":"int"}}],"return_type":{"tag":"int"},"body":'
             '{"tag":"var","name":"%s"}},{"tag":"entry","name":"identity"}]}')

    def ast(self, s):
        return api.compile_ast(s.encode())

    def test_identity(self):
        r = self.ast(self.IDENT % "x")
        self.assertIsInstance(r, api.Accepted)
        self.assertEqual(encode_ast(r.program.program), self.IDENT % "x")

    def test_duplicate_key(self):
        self.assertEqual(codes(self.ast('{"codec":"ast_codec_v1","codec":"ast_codec_v1",'
                                        '"declarations":[]}')), ["E-AST-DUPLICATE-KEY"])
        self.assertEqual(codes(self.ast('{"codec":"ast_codec_v1","\\u0063odec":"x",'
                                        '"declarations":[]}')), ["E-AST-DUPLICATE-KEY"])

    def test_inferred_type_field(self):
        s = self.IDENT.replace('"name":"%s"}', '"name":"x","inferred_type":{"tag":"int"}}')
        self.assertEqual(codes(self.ast(s)), ["E-AST-UNKNOWN-FIELD"])

    def test_identifiers(self):
        self.assertEqual(codes(self.ast(self.IDENT % "if")), ["E-AST-IDENTIFIER"])
        self.assertIsInstance(self.ast(self.IDENT % "\\u0078"), api.Accepted)
        for bad in ("x\\n", "x\\r", "x\\r\\n", "x\\t", " x", "\\u00e9", "x\\u2028"):
            self.assertEqual(codes(self.ast(self.IDENT % bad)), ["E-AST-IDENTIFIER"], bad)

    def test_integers(self):
        base = self.IDENT.replace('{"tag":"var","name":"%s"}', '{"tag":"int","value":%s}')
        for bad in ('"-0"', '"01"', '"+1"'):
            self.assertEqual(codes(self.ast(base % bad)), ["E-AST-INTEGER"], bad)
        self.assertEqual(codes(self.ast(base % "1")), ["E-AST-FIELD-TYPE"])

    def test_empty_declarations(self):
        self.assertEqual(codes(self.ast('{"codec":"ast_codec_v1","declarations":[]}')),
                         ["E-ENTRY-MISSING"])

    def test_uncons(self):
        call = self.IDENT.replace('{"tag":"var","name":"%s"}',
                                  '{"tag":"call","callee":"uncons","args":[{"tag":"var",'
                                  '"name":"x"}]}')
        self.assertEqual(codes(self.ast(call)), ["E-NAME-UNKNOWN-FUNCTION"])
        decl = ('{"tag":"fn","name":"uncons","params":[{"name":"y","type":{"tag":"int"}}],'
                '"return_type":{"tag":"int"},"body":{"tag":"var","name":"y"}},')
        with_fn = call.replace('"declarations":[', '"declarations":[' + decl)
        r = self.ast(with_fn)
        self.assertIsInstance(r, api.Accepted, codes(r))

    def test_some_without_value(self):
        s = self.IDENT.replace('{"tag":"var","name":"%s"}', '{"tag":"some"}')
        self.assertEqual(codes(self.ast(s)), ["E-AST-MISSING-FIELD"])

    def test_param_with_tag(self):
        s = (self.IDENT % "x").replace('{"name":"x","type"', '{"tag":"param","name":"x","type"')
        self.assertEqual(codes(self.ast(s)), ["E-AST-UNKNOWN-FIELD"])

    def test_shallow_type_before_content(self):
        s = (self.IDENT % "x").replace('"name":"identity","params"', '"name":"if","params"')
        s = s.replace('"body":{"tag":"var","name":"x"}', '"body":1')
        self.assertEqual(codes(self.ast(s)), ["E-AST-FIELD-TYPE"])

    def test_bytes_before_utf8(self):
        from tolvemi.profiles import AstTransportProfile
        r = api.compile_ast(b"\xff\xff", S, AstTransportProfile(json_bytes=1))
        self.assertEqual(codes(r), ["E-AST-LIMIT-BYTES"])
        self.assertEqual(codes(api.compile_ast(b"\xff")), ["AstBoundaryFailure"])

    def test_lone_surrogate(self):
        self.assertEqual(codes(self.ast(self.IDENT % "\\ud800")), ["E-AST-STRING-SCALAR"])

    def test_surface_and_ast_roundtrip(self):
        src = open("examples/sum_even.tlvm", "rb").read()
        r = api.compile(src)
        enc = encode_ast(r.program.program)
        r2 = api.compile_ast(enc.encode())
        self.assertEqual(r2.program.program, r.program.program)
        self.assertEqual(encode_ast(api.compile(format_program(r2.program.program)).program
                                    .program), enc)


class InputDecode(unittest.TestCase):
    PU = Ty("Pair", Ty("Unit"), Ty("Unit"))

    def dec(self, t, s, **kw):
        return api.decode_input(t, s.encode(), InputProfile(**kw))

    def test_member_order_free(self):
        self.assertIsInstance(self.dec(INT, '{"value":"5","tag":"int"}'), Decoded)

    def test_json_number_rejected(self):
        self.assertEqual(codes(self.dec(INT, '{"tag":"int","value":5}')), ["E-INPUT-FIELD-TYPE"])

    def test_escaped_duplicate(self):
        self.assertEqual(codes(self.dec(INT, '{"tag":"int","t\\u0061g":"int","value":"1"}')),
                         ["E-INPUT-DUPLICATE-KEY"])

    def test_child_key_before_child_admission(self):
        s = '{"tag":"pair","left":{"tag":"unit","x":1},"right":{"tag":"unit"}}'
        self.assertEqual(codes(self.dec(self.PU, s, value_depth=1)), ["E-INPUT-UNKNOWN-FIELD"])
        s = '{"tag":"pair","left":{"tag":"unit"},"right":{"tag":"unit"}}'
        self.assertEqual(codes(self.dec(self.PU, s, value_depth=1)),
                         ["E-LIMIT-INPUT-VALUE-DEPTH"])

    def test_nodes_before_integer_form(self):
        self.assertEqual(codes(self.dec(INT, '{"tag":"int","value":"01"}', value_nodes=0)),
                         ["E-LIMIT-INPUT-VALUE-NODES"])
        self.assertEqual(codes(self.dec(INT, '{"tag":"int","value":"0123"}', integer_digits=2)),
                         ["E-INPUT-INTEGER"])
        self.assertEqual(codes(self.dec(INT, '{"tag":"int","value":5}', value_nodes=0)),
                         ["E-INPUT-FIELD-TYPE"])

    def test_duplicate_before_tag(self):
        self.assertEqual(codes(self.dec(INT, '{"tag":"bool","tag":"bool"}')),
                         ["E-INPUT-DUPLICATE-KEY"])

    def test_int_10_pow_4096(self):
        n = 10 ** 4096
        self.assertEqual(codes(self.dec(INT, '{"tag":"int","value":"%d"}' % n)),
                         ["E-LIMIT-INPUT-INTEGER-DIGITS"])
        self.assertEqual(n.bit_length(), 13_607)


class Execution(unittest.TestCase):
    def test_examples(self):
        out = run_src(open("examples/sum_even.tlvm", "rb").read(), ilist(1, 2, -4, 7))
        self.assertEqual(out.output, '{"tag":"int","value":"-2"}')
        out = run_src(open("examples/positive_values.tlvm", "rb").read(), ilist(3, -2, 5))
        self.assertEqual(json.loads(out.output)["items"],
                         [{"tag": "int", "value": "3"}, {"tag": "int", "value": "5"}])

    def test_mod(self):
        src = "fn f(p: Pair<Int, Int>) -> Option<Int> = mod(fst(p), snd(p)) entry f"
        pair = '{"tag":"pair","left":{"tag":"int","value":"%d"},"right":{"tag":"int","value":"%d"}}'
        self.assertEqual(run_src(src, pair % (-3, 2)).output,
                         '{"tag":"some","value":{"tag":"int","value":"1"}}')
        self.assertEqual(run_src(src, pair % (1, 0)).output, '{"tag":"none"}')

    def test_concat_allocates_m(self):
        src = "fn f(p: Pair<List<Int>, List<Int>>) -> List<Int> = concat(fst(p), snd(p)) entry f"
        inp = '{"tag":"pair","left":%s,"right":%s}' % (ilist(1, 2, 3), ilist(4, 5))
        out = run_src(src, inp)
        self.assertEqual(out.allocated_nodes, 3)
        self.assertEqual(len(json.loads(out.output)["items"]), 5)

    def test_none_and_let_sharing(self):
        out = run_src("fn f(u: Unit) -> List<Option<Int>> = list[Option<Int>](none[Int], "
                      "none[Int]) entry f", '{"tag":"unit"}')
        self.assertEqual(out.allocated_nodes, 2)  # cons セル2つ、none は割当0
        out = run_src("fn f(u: Unit) -> Pair<Int, Int> = let x = 7 in pair(x, x) entry f",
                      '{"tag":"unit"}')
        self.assertEqual(out.allocated_nodes, 2)  # 整数1つと pair 1つ

    def test_step_trace_identity(self):
        out = run_src("fn f(x: Int) -> Int = x entry f", '{"tag":"int","value":"1"}')
        self.assertEqual((out.steps, out.allocated_nodes), (2, 0))  # 入場 + var

    def test_resource_exhausted(self):
        src = "fn f(xs: List<Int>) -> Int = fold(xs, 0, |a, x| add(a, x)) entry f"
        r = run_src(src, ilist(*range(100)), ExecutionProfile(steps=50))
        self.assertEqual((r.kind, r.observed, r.limit), ("Steps", 51, 50))
        r = run_src(src, ilist(*range(100)), ExecutionProfile(allocated_nodes=10))
        self.assertEqual((r.kind, r.observed), ("AllocatedNodes", 11))
        r = run_src("fn f(x: Int) -> Int = mul(x, x) entry f", '{"tag":"int","value":"%d"}'
                    % (2 ** 40), ExecutionProfile(integer_bits=64))
        self.assertEqual((r.kind, r.observed), ("IntegerBits", 81))
        r = run_src("fn f(x: Int) -> Int = 0 entry f", '{"tag":"int","value":"%d"}' % (2 ** 70),
                    ExecutionProfile(integer_bits=64))
        self.assertEqual((r.kind, r.observed), ("IntegerBits", 71))
        r = run_src("fn f(x: Int) -> Int = x entry f", '{"tag":"int","value":"12345"}',
                    ExecutionProfile(output_bytes=10))
        self.assertEqual((r.kind, r.observed), ("OutputBytes", 11))

    def test_eq_structural(self):
        src = ("fn f(p: Pair<List<Int>, List<Int>>) -> Bool = eq(fst(p), snd(p)) entry f")
        inp = '{"tag":"pair","left":%s,"right":%s}'
        self.assertEqual(run_src(src, inp % (ilist(1, 2), ilist(1, 2))).output,
                         '{"tag":"bool","value":true}')
        self.assertEqual(run_src(src, inp % (ilist(1, 2), ilist(1))).output,
                         '{"tag":"bool","value":false}')


if __name__ == "__main__":
    unittest.main()
