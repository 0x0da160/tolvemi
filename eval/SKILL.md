---
name: tolvemi-lptl
description: Write programs in Tolvemi (LPTL v1.1), a small pure, total, statically typed language over finite data. Use when asked to write or fix a .tlvm program.
---

# Tolvemi (LPTL v1.1)

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
| `match_option(o, e_none, \|v\| e_some)` | `o` must be an `Option<T>`. If `o` is `none`, the result is `e_none`; if it is `some(x)`, the result is `e_some` with `v` bound to `x`. Only the chosen branch is evaluated; both branches must have the same type |
| `f(e1, ..., en)` | call a builtin or a user function (all arguments are evaluated first) |

`|acc, x| body` is only allowed as the third argument of `fold`, and `|v| e` only as the third argument of
`match_option`. There are no lambdas, closures or first-class functions anywhere else.

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
| `uncons(xs)` | `List<A> -> Option<Pair<A, List<A>>>` | `none[Pair<A, List<A>>]` for the empty list, otherwise `some(pair(first, rest))` |

There are no operators (`+`, `<`, `==`, `&&`, ...): write `add(a, b)`, `lt(a, b)`, `eq(a, b)`, `if(a, b, false)`.
There is no division, `head`, `tail`, indexing, `map`, `filter`, `min`, `max`, `abs`, `not`, `and` or `or`; build
them from `fold`, `if`, `match_option` and the builtins above (`uncons` plus `match_option` gives head and tail).

## Option: unwrap it with match_option

`match_option` is the only way to get the payload out of a `some`. A few patterns:

- First element with a default: `match_option(uncons(xs), 0, |c| fst(c))`.
- Use a `mod` result: `match_option(mod(x, k), 0, |r| add(r, 1))`. Divisibility still works by comparison:
  `eq(mod(x, k), some(0))`.
- Remember a value seen during a fold: keep an `Option<T>` in the accumulator (`none[Int]` at the start, `some(x)`
  once found) and unwrap it with `match_option` when you need it.

## Names and scoping

- All names are ASCII identifiers that are not reserved words. Reserved words: `fn entry Int Bool Unit List Option
  Pair true false unit list some none pair let in if fold match_option add sub mul neg lt le eq mod fst snd cons
  concat reverse length uncons`. For example, `list`, `pair`, `fold`, `entry` and `length` cannot be used as
  variable or function names.
- No shadowing: a `let` name, a `fold` binder or a `match_option` binder must not reuse any name that is already in
  scope (including function parameters and outer binders). The two `fold` binders must differ from each other.
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

Walking two lists together: fold over one list and carry the rest of the other in the accumulator, taking its
head with `uncons`.

```tlvm
// Element-wise sum of two lists of the same length.
fn solve(p: Pair<List<Int>, List<Int>>) -> List<Int> =
  reverse(fst(fold(fst(p), pair(list[Int](), snd(p)), |acc, x|
    match_option(uncons(snd(acc)), acc, |h|
      pair(cons(add(x, fst(h)), fst(acc)), snd(h))))))
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
| `E-TYPE-MATCH-SCRUTINEE` / `E-TYPE-MATCH-BRANCH` | `match_option` on a non-Option, or branches of different types |
| `E-TYPE-*` | a type mismatch; `expected` and `found` show both types |
| `E-ENTRY-MISSING` / `E-ENTRY-ARITY` | no `entry` line, or the entry function does not take exactly one parameter |

## Output format

Answer with the complete program in a single fenced code block tagged `tlvm`. Include every helper function and the
`entry` line.
