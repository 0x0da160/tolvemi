---
name: tolvemi-lptl
description: Write programs in Tolvemi (LPTL v1.6), a small pure, total, statically typed language over finite data. Use when asked to write or fix a .tlvm program.
---

# Tolvemi (LPTL v1.6)

Tolvemi is a small language for pure, total, deterministic computation over finite data. Every accepted program
terminates and returns exactly one value of its declared type. Programs do no I/O themselves (a command-line runner feeds them text, below), and there is no mutation, no general
recursion and no exceptions. The language is deliberately small: if something is not listed here, it does not exist.

## Program shape

A program is a list of top-level functions plus exactly one `entry` declaration naming a one-parameter function.

```tlvm
// Sum of the even numbers in a list.
fn sum_even(xs: List<Int>) -> Int =
  fold(xs, 0, |acc, x|
    let r = mod(x, 2) in
    if(eq(r, some(0)), add(acc, x), acc))
entry sum_even
```

- `fn name(p1: T1, p2: T2, ...) -> R = expr`. A function body is a single expression.
- Functions may call other functions, but the call graph must be acyclic: no recursion, direct or mutual.
- The entry function takes exactly one parameter. Several inputs arrive packed in `Pair`s.
- Comments start with `//` and run to the end of the line. Outside comments and string or char literals, the source must be ASCII.

## Types and values

| Type | Values (as written in source) |
|---|---|
| `Int` | arbitrary-precision integers: `0`, `42`, `-7` (a negative literal is one token: write `-7`, never `- 7`) |
| `Bool` | `true`, `false` |
| `Unit` | `unit` |
| `List<T>` | `list<T>(e1, e2, ...)`; the empty list is `list<T>()` (the element type is always written) |
| `Option<T>` | `some(e)`, `none<T>()` (the payload type is always written) |
| `Pair<A, B>` | `pair(a, b)` |
| `Result<T, E>` | `ok<T, E>(e)` (success), `err<T, E>(e)` (failure); both type arguments are always written |
| `Char` | a Unicode character: `'a'`, `'"'`, `'\''`, `'\n'` |
| `String` | text: `"hello"`, `""`, `"say \"hi\"\n"`. A `String` **is** a `List<Char>`, but the type is always written `String` (`List<Char>` is rejected) |

Escapes in literals: `\\`, `\n`, `\t`, `\r`, and the literal's own quote (`\"` in strings, `\'` in chars). Nothing else.
In JSON inputs and outputs, a `String` is a JSON string and a `Char` is a one-character JSON string.
There are no floats, type variables or generics. Records and sum types (below) are the only user-defined types.
Type arguments are always written in angle brackets, as in types; square brackets `[` `]` never appear in source.

## Expressions

| Form | Meaning |
|---|---|
| `let x = e1 in e2` | bind `x` to the value of `e1` inside `e2` |
| `if(c, e_then, e_else)` | `c` must be `Bool`; both branches must have the same type |
| `fold(xs, init, \|acc, x\| body)` | left fold over list `xs`: `acc` starts as `init`; for each element `x`, the new `acc` is `body`. The result is the final `acc`. `body` must have the same type as `init` |
| `match_option(o, e_none, \|v\| e_some)` | `o` must be an `Option<T>`. If `o` is `none`, the result is `e_none`; if it is `some(x)`, the result is `e_some` with `v` bound to `x`. Only the chosen branch is evaluated; both branches must have the same type |
| `match_result(r, \|v\| e_ok, \|e\| e_err)` | `r` must be a `Result<T, E>`. If it is `ok(x)`, the result is `e_ok` with `v` bound to `x`; if it is `err(y)`, `e_err` with `e` bound to `y`. Only the chosen branch is evaluated; both branches must have the same type |
| `match e { P => e1, ... }` | case analysis on a sum type, a `Result` or an `Option` (below) |
| `f(e1, ..., en)` | call a builtin or a user function (all arguments are evaluated first) |

`|acc, x| body` is only allowed as the third argument of `fold`, `|x| e` only as the second argument of `map`, `filter`,
`any`, `all`, `find` and `sort_by` (below), as the third argument of `loop` (`|s| e`, below) and of `match_option`, and as the
second and third arguments of `match_result`. There are no lambdas, closures or first-class functions anywhere else: write `map(xs, |x| f(x))`, never `map(xs, f)`.

## Builtins (the complete list)

| Builtin | Type | Meaning |
|---|---|---|
| `add(a, b)`, `sub(a, b)`, `mul(a, b)` | `Int, Int -> Int` | a+b, a-b, a*b |
| `neg(a)` | `Int -> Int` | -a |
| `lt(a, b)`, `le(a, b)` | `Int, Int -> Bool` | a < b, a <= b |
| `eq(a, b)` | `A, A -> Bool` | structural equality on any type (both sides must have the same type) |
| `mod(a, b)` | `Int, Int -> Option<Int>` | `some(r)` with `0 <= r < b` when `b > 0`, otherwise `none<Int>()`. `mod(-3, 2) = some(1)` |
| `fst(p)`, `snd(p)` | `Pair<A, B> -> A` / `B` | components of a pair |
| `cons(x, xs)` | `A, List<A> -> List<A>` | prepend |
| `concat(xs, ys)` | `List<A>, List<A> -> List<A>` | append |
| `reverse(xs)` | `List<A> -> List<A>` | reverse |
| `length(xs)` | `List<A> -> Int` | number of elements |
| `uncons(xs)` | `List<A> -> Option<Pair<A, List<A>>>` | `none<Pair<A, List<A>>>()` for the empty list, otherwise `some(pair(first, rest))` |
| `min(a, b)`, `max(a, b)` | `Int, Int -> Int` | the smaller / larger of two integers |
| `range(a, b)` | `Int, Int -> List<Int>` | `[a, a+1, ..., b-1]`; empty when `b <= a`. `range(0, length(xs))` gives the indices of `xs` |
| `contains(xs, x)` | `List<A>, A -> Bool` | whether some element equals `x` (structural equality) |
| `sort(xs)` | `List<Int> -> List<Int>` | ascending order, duplicates kept |
| `code(c)` | `Char -> Int` | the character's code point: `code('A') = 65` |
| `char(n)` | `Int -> Option<Char>` | `some(c)` if `n` is a valid code point, otherwise `none<Char>()` |
| `to_string(n)` | `Int -> String` | decimal text: `to_string(-12) = "-12"` |
| `parse_int(s)` | `String -> Option<Int>` | `some(n)` if `s` is an optional `-` followed by one or more digits, otherwise `none<Int>()` |
| `map(xs, \|x\| e)` | `List<A> -> List<B>` | `e` applied to each element, in order |
| `filter(xs, \|x\| p)` | `List<A> -> List<A>` | the elements for which `p` (a `Bool`) is true, in order |
| `any(xs, \|x\| p)`, `all(xs, \|x\| p)` | `List<A> -> Bool` | some / every element satisfies `p` (`all` of an empty list is true); stop at the answer |
| `find(xs, \|x\| p)` | `List<A> -> Option<A>` | the first element satisfying `p`, or `none` |
| `sort_by(xs, \|x\| k)` | `List<A> -> List<A>` | ascending by the `Int` key `k`; equal keys keep their order (descending: `\|x\| neg(k)`) |
| `loop(init, max, \|s\| e)` | `S, Int -> Option<S>` | repeat a step on a state: start with `s = init`; `e : Option<S>` returns `some(next)` to continue or `none<S>()` to stop. Result: `some(s)` with the state at the stop, or `none<S>()` if `e` was evaluated `max` times without stopping (`max <= 0`: `none`, `e` never evaluated) |

Strings are lists of characters, so the list builtins and `fold` work on them directly: `concat("ab", "c")`,
`length(s)`, `reverse(s)`, `eq(s, "yes")`, `contains(s, ' ')`, `uncons(s)`, `fold(s, 0, |n, c| ...)`, `filter(s, |c| ...)`.

There are no operators (`+`, `<`, `==`, `&&`, ...): write `add(a, b)`, `lt(a, b)`, `eq(a, b)`, `if(a, b, false)`.
There is no division, `head`, `tail`, indexing, `abs`, `not`, `and` or `or`; build
them from `fold`, `if`, `match_option` and the builtins above (`uncons` plus `match_option` gives head and tail).

## Option: unwrap it with match_option

`match_option` is the only way to get the payload out of a `some`. A few patterns:

- First element with a default: `match_option(uncons(xs), 0, |c| fst(c))`.
- Use a `mod` result: `match_option(mod(x, k), 0, |r| add(r, 1))`. Divisibility still works by comparison:
  `eq(mod(x, k), some(0))`.
- Remember a value seen during a fold: keep an `Option<T>` in the accumulator (`none<Int>()` at the start, `some(x)`
  once found) and unwrap it with `match_option` when you need it.

## Records: name the parts of a tuple

Declare a record type at the top level, before its first use, and use it instead of nested `pair`s:

```tlvm
type Stats = { count: Int, total: Int, best: Option<Int> }

fn step(s: Stats, x: Int) -> Stats =
  Stats { count: add(s.count, 1), total: add(s.total, x), ..s }

fn solve(xs: List<Int>) -> Int =
  fold(xs, Stats { count: 0, total: 0, best: none<Int>() }, |acc, x| step(acc, x)).total
entry solve
```

- Build with `Name { field: e, ... }`, giving every field; or give some fields and copy the rest with `..e` at the end.
- Read a field with `e.field`. Field names must be unique across all record types in the program.
- A record type may use record types declared above it (no recursive types).
- Record inputs and outputs are JSON objects keyed by field name.

## Sum types and match: one of several shapes

Declare a sum type at the top level, before its first use. Each variant is a constructor name starting with an
uppercase letter, with or without fields. Build a value by calling the constructor (`Circle(5)`, `Rect(2, 3)`, and
plain `Empty` without parentheses), and take it apart with `match`:

```tlvm
type Shape = Circle(Int) | Rect(Int, Int) | Empty

fn area(s: Shape) -> Int =
  match s { Circle(r) => mul(3, mul(r, r)), Rect(w, h) => mul(w, h), Empty => 0 }

fn square(n: Int) -> Shape = if(lt(0, n), Rect(n, n), Empty)

// The largest shape; a failure is a value too.
fn largest(xs: List<Shape>) -> Result<Shape, String> =
  match uncons(xs) {
    none => err<Shape, String>("no shapes"),
    some(h) => ok<Shape, String>(fold(snd(h), fst(h), |best, s| if(lt(area(best), area(s)), s, best)))
  }

fn solve(sizes: List<Int>) -> Result<Int, String> =
  let shapes = fold(sizes, list<Shape>(), |acc, n| cons(square(n), acc)) in
  match_result(largest(shapes), |s| ok<Int, String>(area(s)), |e| err<Int, String>(e))
entry solve
```

- `match` patterns: `Ctor`, `Ctor(a, b)` (one name or `_` per field), `ok(v)`, `err(e)`, `some(v)`, `none`, and `_`.
  All arms of one `match` are for the same type; every arm must have the same result type.
- Cover every case exactly once, or end with `_ => e` for the rest. A missing case, a repeated case, or an arm after
  `_` is an error. The names bound by a pattern are visible only in that arm and must not shadow other names.
- Constructor names are unique in the program and differ from function, variable and type names. A sum type may
  use types declared above it (no recursive types).
- `match` works on `Result` and `Option` too; `match_result` and `match_option` are the same thing written as calls.
- In JSON inputs and outputs a `Result` is `{"ok": v}` or `{"err": e}`, and a sum value is the constructor name
  with its fields in an array: `{"Rect": [2, 3]}`, `{"Empty": []}`.

## Names and scoping

- All names are ASCII identifiers. Reserved words, never usable as names: `fn Int Bool Unit List Option
  Pair Char String Result true false unit let in if fold match_option match_result`.
- `entry` and the builtin and constructor names `list some none pair ok err add sub mul neg lt le eq mod fst snd cons concat reverse
  length uncons min max range contains sort code char to_string parse_int map filter any all find sort_by loop` may be used as variable, parameter, binder and field names (`|pair| fst(pair)`, `length: Int`).
  `|acc, entry|` is fine. Followed by `(` or `<` they are always the builtin, so they cannot be function names.
  `match` and `type` are ordinary names except at the start of a `match` expression or a type declaration.
- No shadowing: a `let` name, a `fold`, `map`-style or `loop` binder, a `match_option` / `match_result` binder or a `match` pattern name must not reuse any name that is already in
  scope (including function parameters and outer binders). The two `fold` binders must differ from each other.
- Function names must be unique.

## Idioms

Transforming and selecting elements: `map` and `filter` keep the order. For any other list built in a `fold`, `cons`
onto an accumulator (which builds it backwards), then `reverse` once at the end.

```tlvm
// The squares of the positive elements of a list, in their original order.
fn positive_squares(xs: List<Int>) -> List<Int> = map(filter(xs, |x| lt(0, x)), |x| mul(x, x))
entry positive_squares
```

Carrying several values through one fold: use a `Pair` (nest pairs for more than two).

```tlvm
// pair(count, total) of a list of integers.
fn count_and_total(xs: List<Int>) -> Pair<Int, Int> =
  fold(xs, pair(0, 0), |acc, x| pair(add(fst(acc), 1), add(snd(acc), x)))
entry count_and_total
```

Several inputs: the entry receives one `Pair`, and helper functions may take several parameters.

```tlvm
fn scale(k: Int, x: Int) -> Int = mul(k, x)
fn solve(p: Pair<Int, List<Int>>) -> List<Int> = map(snd(p), |x| scale(fst(p), x))
entry solve
```

Walking two lists together: fold over one list and carry the rest of the other in the accumulator, taking its
head with `uncons`.

```tlvm
// Element-wise sum of two lists of the same length.
fn solve(p: Pair<List<Int>, List<Int>>) -> List<Int> =
  reverse(fst(fold(fst(p), pair(list<Int>(), snd(p)), |acc, x|
    match_option(uncons(snd(acc)), acc, |h|
      pair(cons(add(x, fst(h)), fst(acc)), snd(h))))))
entry solve
```

A process with several pieces of state (a machine, a simulation, a scan with a "previous" value): put the state in a
record, write one `step` function, and fold it over the input. Keep "nothing yet" as an `Option` field, not a magic
number such as `-1`.

```tlvm
// Largest change between adjacent values (0 for fewer than two values).
type Scan = { prev: Option<Int>, best: Int }

fn step(s: Scan, x: Int) -> Scan =
  let change = match_option(s.prev, 0, |p| max(sub(x, p), sub(p, x))) in
  Scan { prev: some(x), best: max(s.best, change) }

fn solve(xs: List<Int>) -> Int = fold(xs, Scan { prev: none<Int>(), best: 0 }, |s, x| step(s, x)).best
entry solve
```

Repeating until a condition holds (no list to walk): `loop` with an upper bound on the number of steps. The step
returns `none` to stop, and the result is an `Option`: `none` means the bound ran out first.

```tlvm
// The smallest power of two that is at least n, or -1 if it is above 2^64.
fn next_power(n: Int) -> Int =
  match_option(loop(1, 65, |p| if(lt(p, n), some(mul(p, 2)), none<Int>())), -1, |p| p)
entry next_power
```

Before answering, check: every `(` is closed (count them in deep nesting), every `let` has its `in`, every
`none<T>()` and `list<T>(...)` names its type, no binder reuses a name already in scope, and no name is a
reserved word (`in`, `if`, `let` and `fold` are the usual slips).

Text: a `String` is a list of characters, so scan it with `fold` and build text with `concat` (or `cons` then
`reverse`). Convert numbers with `to_string` and `parse_int`.

```tlvm
// Split a line into words separated by spaces (empty words are dropped).
type Split = { words: List<String>, cur: String }

fn flush(s: Split) -> List<String> =
  if(eq(s.cur, ""), s.words, cons(reverse(s.cur), s.words))

fn step(s: Split, c: Char) -> Split =
  if(eq(c, ' '), Split { words: flush(s), cur: "" }, Split { cur: cons(c, s.cur), ..s })

fn words(line: String) -> List<String> =
  reverse(flush(fold(line, Split { words: list<String>(), cur: "" }, |s, c| step(s, c))))
entry words
```

## Programs as commands

`tlvm exec prog.tlvm ARGS...` runs a program as a command. The entry's input type says what it receives:
`String` gets all of standard input, `List<String>` gets the command-line arguments, and
`Pair<List<String>, String>` gets both. If the output type is `String` it is written to standard output exactly
(add `"\n"` yourself where you want line breaks). If it is `Result<String, String>`, `ok(s)` writes `s` to standard
output (exit code 0) and `err(s)` writes `s` to standard error (exit code 1). Any other output is printed as JSON.

```tlvm
// Number each line of standard input: "1: first", "2: second", ...
type Acc = { out: String, n: Int, line: String }

fn emit(a: Acc) -> String = concat(a.out, concat(to_string(a.n), concat(": ", concat(reverse(a.line), "\n"))))

fn solve(text: String) -> String =
  let a = fold(text, Acc { out: "", n: 1, line: "" }, |a, c|
    if(eq(c, '\n'), Acc { out: emit(a), n: add(a.n, 1), line: "" }, Acc { line: cons(c, a.line), ..a })) in
  if(eq(a.line, ""), a.out, emit(a))
entry solve
```

## Diagnostics

The checker reports errors as `file:line:col: error[CODE]: message (expected ..., found ...)`, often followed by a
`repair` hint. Common codes:

| Code | Usual cause |
|---|---|
| `E-LEX-UNEXPECTED-CHARACTER` | an operator such as `+`, `-`, `*`, `/` (operators do not exist) |
| `E-PARSE-UNEXPECTED-TOKEN` | extra tokens after a complete expression, such as `x == 1` |
| `E-PARSE-EXPECTED-TOKEN` / `E-PARSE-EXPECTED-EXPR` | missing `,` or `)`, or a malformed special form |
| `E-PARSE-EXPECTED-IDENT` | a reserved word used as a name, or a builtin name used as a function name |
| `E-PARSE-EXPECTED-TYPE` | a missing or invalid type in `list<T>(...)` / `none<T>()` |
| `E-NAME-UNBOUND-VARIABLE` / `E-NAME-UNKNOWN-FUNCTION` | a typo, or a function that does not exist (e.g. `head`, `abs`) |
| `E-NAME-SHADOW` | a `let` / `fold` binder reuses a name already in scope |
| `E-CYCLE-CALL` | recursion |
| `E-ARITY-BUILTIN` / `E-ARITY-USER` | wrong number of arguments |
| `E-TYPE-MATCH-SCRUTINEE` / `E-TYPE-MATCH-BRANCH` | `match_option` on a non-Option (`match_result` on a non-Result, `match` on a value of another type), or branches of different types |
| `E-MATCH-MISSING` / `E-MATCH-DUPLICATE` / `E-MATCH-UNREACHABLE` | a `match` without an arm for some case (the repair lists them), a case twice, or an arm after `_` |
| `E-MATCH-MIXED` | patterns of different types in one `match` (e.g. `Circle(r)` and `ok(v)`) |
| `E-SUM-UNKNOWN-CTOR` / `E-SUM-CTOR-ARITY` | a misspelt constructor, or the wrong number of fields (`Empty()` for a constructor without fields) |
| `E-SUM-DUPLICATE-CTOR` / `E-SUM-NAME-CONFLICT` | a constructor declared twice, or also used as a function, variable or type name |
| `E-PARSE-EXPECTED-LAMBDA` | the second argument of `map` / `filter` / `any` / `all` / `find` / `sort_by`, or the third argument of `loop`, is not `\|x\| e` (e.g. a bare function name, or `\|acc, x\|`) |
| `E-TYPE-LOOP-MAX` / `E-TYPE-LOOP-BODY` | the bound of `loop` is not an `Int`, or its step is not `Option<S>` where `S` is the type of `init` (return `some(next)` / `none<S>()`, not the bare state) |
| `E-PARSE-EXPECTED-PATTERN` | something other than a pattern before `=>` in a `match` arm |
| `E-TYPE-*` | a type mismatch; `expected` and `found` show both types |
| `E-PARSE-STRING-TYPE` | `List<Char>` written as a type; write `String` |
| `E-LEX-INVALID-ESCAPE` / `E-LEX-UNTERMINATED-STRING` / `E-LEX-INVALID-CHAR-LITERAL` | a bad escape, a string without its closing `"`, or a char literal that is not exactly one character |
| `E-ENTRY-MISSING` / `E-ENTRY-ARITY` | no `entry` line, or the entry function does not take exactly one parameter |

## Output format

Answer with the complete program in a single fenced code block tagged `tlvm`. Include every helper function and the
`entry` line.
