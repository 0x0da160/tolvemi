---
name: tolvemi-lptl
description: Write programs in Tolvemi (LPTL v1), a small pure, total, statically typed language over finite data. Use when asked to write or fix a .tlvm program.
---

# Tolvemi (LPTL v1)

Tolvemi is a small language for pure, total, deterministic computation over finite data. Every accepted program
terminates and returns exactly one value of its declared type. There is no I/O, no mutation, no general
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
- Comments start with `//` and run to the end of the line. Outside comments, the source must be ASCII.

## Types and values

| Type | Values (as written in source) |
|---|---|
| `Int` | arbitrary-precision integers: `0`, `42`, `-7` (a negative literal is one token: write `-7`, never `- 7`) |
| `Bool` | `true`, `false` |
| `Unit` | `unit` |
| `List<T>` | `list[T](e1, e2, ...)`; the empty list is `list[T]()` (the element type is always written) |
| `Option<T>` | `some(e)`, `none[T]` (the payload type is always written) |
| `Pair<A, B>` | `pair(a, b)` |

There are no strings, floats, records, user-defined types, type variables or generics. Type equality is syntactic.

## Expressions

| Form | Meaning |
|---|---|
| `let x = e1 in e2` | bind `x` to the value of `e1` inside `e2` |
| `if(c, e_then, e_else)` | `c` must be `Bool`; both branches must have the same type |
| `fold(xs, init, \|acc, x\| body)` | left fold over list `xs`: `acc` starts as `init`; for each element `x`, the new `acc` is `body`. The result is the final `acc`. `body` must have the same type as `init` |
| `f(e1, ..., en)` | call a builtin or a user function (all arguments are evaluated first) |

`|acc, x| body` is only allowed as the third argument of `fold`. There are no lambdas, closures or
first-class functions anywhere else.

## Builtins (the complete list)

| Builtin | Type | Meaning |
|---|---|---|
| `add(a, b)`, `sub(a, b)`, `mul(a, b)` | `Int, Int -> Int` | a+b, a-b, a*b |
| `neg(a)` | `Int -> Int` | -a |
| `lt(a, b)`, `le(a, b)` | `Int, Int -> Bool` | a < b, a <= b |
| `eq(a, b)` | `A, A -> Bool` | structural equality on any type (both sides must have the same type) |
| `mod(a, b)` | `Int, Int -> Option<Int>` | `some(r)` with `0 <= r < b` when `b > 0`, otherwise `none[Int]`. `mod(-3, 2) = some(1)` |
| `fst(p)`, `snd(p)` | `Pair<A, B> -> A` / `B` | components of a pair |
| `cons(x, xs)` | `A, List<A> -> List<A>` | prepend |
| `concat(xs, ys)` | `List<A>, List<A> -> List<A>` | append |
| `reverse(xs)` | `List<A> -> List<A>` | reverse |
| `length(xs)` | `List<A> -> Int` | number of elements |

There are no operators (`+`, `<`, `==`, `&&`, ...): write `add(a, b)`, `lt(a, b)`, `eq(a, b)`, `if(a, b, false)`.
There is no division, `head`, `tail`, indexing, `map`, `filter`, `min`, `max`, `abs`, `not`, `and` or `or`; build
them from `fold`, `if` and the builtins above.

## Option: you can build and compare it, but not unwrap it

There is no `match`, `match_option`, `uncons` or `unwrap`. You can create `some(e)` / `none[T]`, pass them around,
return them, and compare them with `eq` against `none[T]` or a known value such as `some(0)`. You can never get
the unknown payload out of a `some`. Consequences:

- Divisibility and parity work by comparison: `eq(mod(x, k), some(0))`.
- To remember an element seen during a fold and use it later, keep it as a plain `Int` next to a `Bool` flag in a
  `Pair` (for example `pair(true, x)`), not inside an `Option`. Build the `Option` only at the end, if the result type
  needs one: `if(fst(st), some(snd(st)), none[Int])`.

## Names and scoping

- All names are ASCII identifiers that are not reserved words. Reserved words: `fn entry Int Bool Unit List Option
  Pair true false unit list some none pair let in if fold add sub mul neg lt le eq mod fst snd cons concat reverse
  length`. For example, `list`, `pair`, `fold` and `length` cannot be used as variable or function names.
- No shadowing: a `let` name or a `fold` binder must not reuse any name that is already in scope (including function
  parameters and outer binders). The two `fold` binders must differ from each other.
- Function names must be unique.

## Idioms

Building a list in order: `cons` onto an accumulator (which builds it backwards), then `reverse` once at the end.

```tlvm
// The positive elements of a list, in their original order.
fn positive_values(xs: List<Int>) -> List<Int> =
  let reversed = fold(xs, list[Int](), |acc, x|
    if(lt(0, x), cons(x, acc), acc)) in
  reverse(reversed)
entry positive_values
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
fn solve(p: Pair<Int, List<Int>>) -> List<Int> =
  reverse(fold(snd(p), list[Int](), |acc, x| cons(scale(fst(p), x), acc)))
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
| `E-PARSE-EXPECTED-IDENT` | a reserved word used as a name |
| `E-PARSE-EXPECTED-TYPE` | a missing or invalid type in `list[T]` / `none[T]` |
| `E-NAME-UNBOUND-VARIABLE` / `E-NAME-UNKNOWN-FUNCTION` | a typo, or a function that does not exist (e.g. `head`, `max`) |
| `E-NAME-SHADOW` | a `let` / `fold` binder reuses a name already in scope |
| `E-CYCLE-CALL` | recursion |
| `E-ARITY-BUILTIN` / `E-ARITY-USER` | wrong number of arguments |
| `E-TYPE-*` | a type mismatch; `expected` and `found` show both types |
| `E-ENTRY-MISSING` / `E-ENTRY-ARITY` | no `entry` line, or the entry function does not take exactly one parameter |

## Output format

Answer with the complete program in a single fenced code block tagged `tlvm`. Include every helper function and the
`entry` line.
