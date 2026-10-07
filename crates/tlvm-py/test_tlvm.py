"""Python binding（tlvm 拡張モジュール）のテスト。

build.sh で tlvm.abi3.so をこのディレクトリに置いてから実行する：

    crates/tlvm-py/build.sh
    python3 -m unittest discover -s crates/tlvm-py -p 'test_*.py'
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import tlvm  # noqa: E402

SUM = "fn solve(xs: List<Int>) -> Int = fold(xs, 0, |acc, x| add(acc, x))\nentry solve\n"


class RecordTest(unittest.TestCase):
    def test_record_is_dict(self):
        src = (
            "type Stats = { count: Int, total: Int }\n"
            "fn solve(xs: List<Int>) -> Stats =\n"
            "  fold(xs, Stats { count: 0, total: 0 }, |s, x| Stats { count: add(s.count, 1), total: add(s.total, x) })\n"
            "entry solve\n"
        )
        p = tlvm.compile(src)
        self.assertEqual(p.output_type, "Stats")
        self.assertEqual(p.run([1, 2**80]), {"count": 2, "total": 2**80 + 1})


class CompileTest(unittest.TestCase):
    def test_types(self):
        p = tlvm.compile(SUM)
        self.assertEqual(p.entry, "solve")
        self.assertEqual(p.input_type, "List<Int>")
        self.assertEqual(p.output_type, "Int")
        self.assertEqual(p.warnings, [])
        self.assertIn("List<Int> -> Int", repr(p))

    def test_compile_error(self):
        with self.assertRaises(tlvm.CompileError) as cm:
            tlvm.compile("fn solve(xs: List<Int>) -> Int = add(xs, 1)\nentry solve\n")
        ds = cm.exception.diagnostics
        self.assertTrue(ds)
        for d in ds:
            self.assertEqual(d["severity"], "error")
            self.assertIn("code", d)
            self.assertIn("start", d["span"])
        self.assertIsInstance(cm.exception, tlvm.TlvmError)

    def test_parse_error(self):
        with self.assertRaises(tlvm.CompileError) as cm:
            tlvm.compile("fn solve(xs: List<Int>) -> Int = \nentry solve\n")
        self.assertTrue(any(d["phase"] == "parse" for d in cm.exception.diagnostics))


class RunTest(unittest.TestCase):
    def test_sum(self):
        p = tlvm.compile(SUM)
        self.assertEqual(p.run([1, 2, 3]), 6)
        self.assertEqual(p.run([]), 0)
        self.assertEqual(p.run_json("[1, 2, 3]"), "6")

    def test_big_int(self):
        p = tlvm.compile(SUM)
        big = 2**80
        self.assertEqual(p.run([big, 1, -(2**53)]), big + 1 - 2**53)
        self.assertEqual(p.run([10**100, 10**100]), 2 * 10**100)

    def test_pair_and_list(self):
        p = tlvm.compile(
            "fn f(xs: List<Int>) -> Pair<Int, List<Int>> = pair(length(xs), reverse(xs))\nentry f\n"
        )
        self.assertEqual(p.run([1, 2, 3]), [3, [3, 2, 1]])
        self.assertEqual(p.run((1, 2)), [2, [2, 1]])

    def test_option(self):
        p = tlvm.compile("fn m(p: Pair<Int, Int>) -> Option<Int> = mod(fst(p), snd(p))\nentry m\n")
        self.assertEqual(p.output_type, "Option<Int>")
        self.assertEqual(p.run([7, 3]), 1)
        self.assertIsNone(p.run([7, 0]))

    def test_input_error(self):
        p = tlvm.compile(SUM)
        for bad in ([1, True], {"a": 1}, 1.5, "x"):
            with self.subTest(bad=bad):
                with self.assertRaises(tlvm.InputError) as cm:
                    p.run(bad)
                self.assertTrue(cm.exception.diagnostics)
        with self.assertRaises(tlvm.InputError):
            p.run_json("[1,")

    def test_resource_exhausted(self):
        # 入れ子の fold で既定の資源上限（steps か allocated nodes）を超える
        p = tlvm.compile(
            "fn f(xs: List<Int>) -> Int = fold(xs, 0, |a, x| fold(xs, a, |b, y| add(b, y)))\nentry f\n"
        )
        with self.assertRaises(tlvm.ResourceExhausted) as cm:
            p.run(list(range(3000)))
        e = cm.exception
        self.assertIn(e.kind, ("Steps", "AllocatedNodes"))
        self.assertGreater(e.observed, e.limit)


if __name__ == "__main__":
    unittest.main()
