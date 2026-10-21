## Output format: the abstract syntax tree as JSON

Do not write the program as source text. Give its abstract syntax tree in the JSON format `ast_codec_v1`, defined by
the JSON Schema at the end of this section. The checker reads the JSON instead of source text and applies the same
name, type and entry checks as to source text.

{{AST_ANSWER}}

The format has no nodes for `type` declarations, records (`Name { ... }`, `e.field`), sum-type constructors, `match`
or `import`. Write those parts with `pair`, `Option`, `Result`, `match_option`, `match_result` and helper functions
instead. Everything else above has a node: a `rec fn` is a `fn` declaration with `"rec": true`, and type parameters
go in `"type_params"`.

- Each object is one node: `"tag"` says which kind, and the object has exactly the keys the schema lists for that
  kind. The program is `{"codec": "ast_codec_v1", "declarations": [...]}` with the `fn` declarations and one `entry`.
- An integer is a decimal string (`{"tag": "int", "value": "-7"}`), a char is its code point as a decimal string
  (`{"tag": "char", "value": "97"}` is `'a'`), and a string is a JSON string (`{"tag": "string", "value": "hi"}`).
- A call of a builtin or of one of your functions is `{"tag": "call", "callee": "add", "args": [...], "type_args": []}`;
  `type_args` holds explicitly written type arguments (`f<Int>(xs)`) and is usually empty. `list<T>(...)`, `some`,
  `none<T>()`, `pair`, `ok`, `err`, `if`, `fold`, `map`, `filter`, `any`, `all`, `find`, `sort_by`, `loop`,
  `match_option`, `match_result`, `let` and `dict<K, V>()` have nodes of their own and are never written as a call.
- No name (function, parameter, binder or type parameter) may be a reserved word or a builtin name, even where source
  text would allow it: `length`, `entry` and `pair` are not valid names here.

For example, the program

```tlvm
fn positive_squares(xs: List<Int>) -> List<Int> = map(filter(xs, |x| lt(0, x)), |x| mul(x, x))
entry positive_squares
```

is this JSON:

```json
{
 "codec": "ast_codec_v1",
 "declarations": [
  {
   "tag": "fn",
   "name": "positive_squares",
   "params": [
    {
     "name": "xs",
     "type": {
      "tag": "list",
      "element": {
       "tag": "int"
      }
     }
    }
   ],
   "return_type": {
    "tag": "list",
    "element": {
     "tag": "int"
    }
   },
   "body": {
    "tag": "map",
    "list": {
     "tag": "filter",
     "list": {
      "tag": "var",
      "name": "xs"
     },
     "binder": "x",
     "body": {
      "tag": "call",
      "callee": "lt",
      "args": [
       {
        "tag": "int",
        "value": "0"
       },
       {
        "tag": "var",
        "name": "x"
       }
      ],
      "type_args": []
     }
    },
    "binder": "x",
    "body": {
     "tag": "call",
     "callee": "mul",
     "args": [
      {
       "tag": "var",
       "name": "x"
      },
      {
       "tag": "var",
       "name": "x"
      }
     ],
     "type_args": []
    }
   }
  },
  {
   "tag": "entry",
   "name": "positive_squares"
  }
 ]
}
```

The JSON Schema of `ast_codec_v1` (draft 2020-12):

```json
{{AST_CODEC_V1_SCHEMA}}
```
