"""Compare full ordered cell answers emitted by the two executable models."""

import argparse
from collections import Counter
from itertools import zip_longest
import json
from pathlib import Path

# The registered complete domains, including all 5² × 3 × 2² ranked cases.
EXPECTED = {
    "nussinov": (127, 2173),
    "alignment": (961, 16641),
    "local": (225, 5027),
    "matrix": (124, 1404),
    "knapsack": (155, 1935),
    "ranked": (300, 1200),
}
QUESTIONS = ("count", "enumeration", "minimum with ties", "minimum", "lexicographic")
ENUMERATION = QUESTIONS.index("enumeration")


def integer(value):
    return type(value) is int


def natural(value):
    return integer(value) and value >= 0


def count(value):
    return natural(value) and value > 0


def cost(value):
    return value is None or integer(value)


def tree(value):
    return (type(value) is list and len(value) == 2 and natural(value[0])
            and type(value[1]) is list and all(map(tree, value[1])))


def summary(value):
    if type(value) is not list or len(value) != 3:
        return False
    minimum, optimal, total = value
    return (cost(minimum) and count(optimal) and count(total) and optimal <= total
            and (minimum is not None or optimal == total))


def lexicographic(value):
    return type(value) is list and len(value) == 2 and all(map(integer, value))


def freeze(value):
    """Make validated trees hashable for the order-only check."""
    return tuple(map(freeze, value)) if type(value) is list else value


def decode(line):
    row = json.loads(line)
    if type(row) is not list or len(row) != 3:
        raise ValueError("expected a group, root and table")
    group, root, cells = row
    if type(group) is not str or type(cells) is not list or not natural(root) or root >= len(cells):
        raise ValueError("invalid group, root or table")
    validators = (count, tree, summary, cost, lexicographic)
    for rank, cell in enumerate(cells):
        if type(cell) is not list or len(cell) != len(QUESTIONS):
            raise ValueError("expected one answer bag per question per cell")
        for index, (question, valid, bag) in enumerate(zip(QUESTIONS, validators, cell, strict=True)):
            if (type(bag) is not list or (index != ENUMERATION and len(bag) > 1)
                    or not all(map(valid, bag))):
                raise ValueError(f"invalid {question} answer at rank {rank}: {bag!r}")
    return group, root, freeze(cells)


def compare(rust, lean, control=False):
    counts = Counter()
    cells = Counter()
    occurrences = Counter()
    disagreements = Counter()
    order_controls = 0
    for line_no, (r, l) in enumerate(zip_longest(rust, lean), 1):
        if r is None or l is None:
            raise ValueError(f"missing output row {line_no}")
        rg, rr, rc = decode(r)
        lg, lr, lc = decode(l)
        if (rg, rr, len(rc)) != (lg, lr, len(lc)):
            raise ValueError(f"layout disagreement at row {line_no}")
        counts[rg] += 1
        cells[rg] += len(rc)
        for rank, (rv, lv) in enumerate(zip(rc, lc, strict=True)):
            occurrences[rg] += len(rv[ENUMERATION])
            for index, (question, a, b) in enumerate(zip(QUESTIONS, rv, lv, strict=True)):
                if a == b:
                    continue
                if control:
                    if index != ENUMERATION or Counter(a) != Counter(b):
                        raise ValueError(f"non-order disagreement at row {line_no} rank {rank} {question}")
                    order_controls += 1
                else:
                    key = (rg, question)
                    if key not in disagreements:
                        print(f"first disagreement {rg} row {line_no} rank {rank} {question}")
                    disagreements[key] += 1
    if control:
        if not order_controls or sum(counts.values()) != 1:
            raise ValueError("order mutation was not isolated and detected")
        print(f"reversed-production control: {order_controls} order-only cell disagreements")
        return
    if counts.keys() != EXPECTED.keys():
        raise ValueError(f"unexpected bridge domains: {counts}")
    print("domain,charts,cells,questions,trees,disagreements")
    for key, expected in EXPECTED.items():
        if (counts[key], cells[key]) != expected:
            raise ValueError(f"unexpected coverage for {key}: {counts[key]} charts, {cells[key]} cells")
        mismatch = sum(n for (domain, _), n in disagreements.items() if domain == key)
        print(f"{key},{counts[key]},{cells[key]},{cells[key] * len(QUESTIONS)},"
              f"{occurrences[key]},{mismatch}")
    print(f"total,{sum(counts.values())},{sum(cells.values())},"
          f"{sum(cells.values()) * len(QUESTIONS)},{sum(occurrences.values())},"
          f"{sum(disagreements.values())}")
    if disagreements:
        raise ValueError(dict(disagreements))


def control_row(charts, rust, prefix):
    for chart, reference in zip(charts, rust, strict=True):
        row = json.loads(chart)
        if row["group"] != "ranked":
            continue
        leaves = row["cells"][0]
        if len(leaves) == 2 and leaves[0]["id"] != leaves[1]["id"]:
            prefix.with_suffix(".chart").write_text(chart)
            prefix.with_suffix(".rust").write_text(reference)
            return
    raise ValueError("no chart with two distinguishable leaf alternatives")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("left", type=Path)
    parser.add_argument("right", type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--make-control", type=Path)
    mode.add_argument("--control", action="store_true")
    args = parser.parse_args()
    with args.left.open() as left, args.right.open() as right:
        if args.make_control:
            control_row(left, right, args.make_control)
        else:
            compare(left, right, args.control)
