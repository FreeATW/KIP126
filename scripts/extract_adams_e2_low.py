#!/usr/bin/env python3
"""Reproduce the small Lean table from Lin's pinned, published CSV archive.

Download (not performed by this script):
https://zenodo.org/records/7865526/files/S0_AdamsE2_csv.zip

This checks data extraction, not the external theorem identifying the table
with the sphere's Adams page. Output is a Lean literal block on stdout;
--check compares that block with the marked block in a checked-in Lean file.
"""

import argparse
import csv
import hashlib
import io
from collections import Counter
from functools import lru_cache
from pathlib import Path
from zipfile import ZipFile

SHA256 = "bb53d84a3450d58535f7119d3a4fa2123688f9574c396d592763c37be89de470"
BEGIN = "-- 林氏 CSV 提取数据开始"
END = "-- 林氏 CSV 提取数据结束"


def monomial(text):
    numbers = list(map(int, text.split(","))) if text else []
    assert len(numbers) % 2 == 0
    result = tuple(zip(numbers[::2], numbers[1::2]))
    assert all(e > 0 for _, e in result)
    assert list(result) == sorted(set(result))
    assert len(dict(result)) == len(result)
    return result


def multiply(a, b):
    result = Counter(dict(a))
    result.update(dict(b))
    return tuple(sorted(result.items()))


def divide(a, b):
    result = dict(a)
    for g, e in b:
        if result.get(g, 0) < e:
            return None
        result[g] -= e
    return tuple((g, e) for g, e in sorted(result.items()) if e)


def extract(path, extra):
    assert hashlib.sha256(path.read_bytes()).hexdigest() == SHA256, "wrong archive"
    with ZipFile(path) as archive:
        assert archive.testzip() is None

        def read(name):
            with archive.open(f"csv/S0_AdamsE2_{name}.csv") as stream:
                return list(csv.DictReader(io.TextIOWrapper(stream)))

        generators = {int(r["id"]): r for r in read("generators")}
        basis = read("basis")
        relations = read("relations")

    region = {(s, s + n) for s in range(9) for n in range(9)}
    region |= {(1, 64), (2, 128)}
    if extra:
        region |= {(1, 16), (4, 18), (5, 20)}

    def degree(mon):
        return tuple(sum(int(generators[g][c]) * e for g, e in mon) for c in ("s", "t"))

    selected = []
    for row in basis:
        p = (int(row["s"]), int(row["t"]))
        if p in region:
            m = monomial(row["mon"])
            assert degree(m) == p
            selected.append((int(row["id"]), p, m))
    selected.sort(key=lambda row: row[0])
    by_mon = {m: i for i, _, m in selected}
    assert len(by_mon) == len(selected)
    assert len({i for i, _, _ in selected}) == len(selected)

    # CSV relations list the leading monomial first. We only need rules
    # dividing one of the products under consideration, all in degree <= 128.
    rules = []
    for row in relations:
        if int(row["t"]) <= 128 and int(row["s"]) <= 8:
            terms = tuple(monomial(t) for t in row["rel"].split(";"))
            assert all(degree(m) == (int(row["s"]), int(row["t"])) for m in terms)
            rules.append(terms)

    @lru_cache(None)
    def reduce(m):
        for terms in rules:
            quotient = divide(m, terms[0])
            if quotient is not None:
                result = set()
                for term in terms[1:]:
                    result.symmetric_difference_update(reduce(multiply(quotient, term)))
                return frozenset(result)
        return frozenset({m})

    products = []
    checked = 0
    for _, _, m in selected:
        assert reduce(m) == frozenset({m}), "a listed additive basis monomial was reduced"
    for left, p, a in selected:
        for right, q, b in selected:
            target = (p[0] + q[0], p[1] + q[1])
            if left > right or target not in region:
                continue
            checked += 1
            reduced = reduce(multiply(a, b))
            assert all(m in by_mon and degree(m) == target for m in reduced), (left, right)
            result = sorted(by_mon[m] for m in reduced)
            # Unit products are handled separately by the Lean lookup.
            if left == 0:
                assert result == [right]
            elif result:
                products.append((left, right, result))

    def label(mon):
        return " * ".join(generators[g]["name"] + (f"^{e}" if e != 1 else "")
                          for g, e in mon) or "1"

    lines = [BEGIN, "/-- CSV 中的基编号、内部双次数和便于阅读的单项式名称。 -/",
             "def basisRows : List (Nat × Degree × String) :=", "  ["]
    lines += [f'    ({i}, ({p[0]}, {p[1]}), "{label(m)}")' +
              ("," if k + 1 < len(selected) else "")
              for k, (i, p, m) in enumerate(selected)]
    lines += ["  ]", "", "/-- 目标在覆盖范围内且不含单位因子的全部非零乘积；编号对应 basisRows。 -/",
              "def productRows : List (Nat × Nat × List Nat) :=", "  ["]
    lines += [f"    ({i}, {j}, {out})" + ("," if k + 1 < len(products) else "")
              for k, (i, j, out) in enumerate(products)]
    dimensions = Counter(p for _, p, _ in selected)
    counts = Counter(dimensions.get(p, 0) for p in region)
    lines += ["  ]", f"-- 共覆盖 {len(region)} 个格点；各维数的格点数量为 {dict(sorted(counts.items()))}。",
              f"-- 共 {len(selected)} 个基向量；已检查覆盖范围内的 {checked} 个无序乘积（包括单位乘积）。", END]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--include-two-dimensional-cell", action="store_true")
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    output = extract(args.archive, args.include_two_dimensional_cell)
    if args.check:
        actual = args.check.read_text()
        actual = BEGIN + actual.split(BEGIN, 1)[1].split(END, 1)[0] + END
        assert actual == output, "checked-in Lean rows differ from the pinned source extraction"
        print("OK: Lean basis/product rows exactly match the pinned Lin CSV extraction")
    else:
        print(output)


if __name__ == "__main__":
    main()
