"""Outcome controls for the bridge comparator."""

from copy import deepcopy
import json
import unittest

from compare import compare


class ComparatorTests(unittest.TestCase):
    def setUp(self):
        first, second = [0, []], [1, []]
        self.original = ["ranked", 0, [
            [[2], [first, second], [[0, 1, 2]], [0], [[0, 1]]],
            [[1], [first], [[1, 1, 1]], [1], [[1, 0]]],
        ]]
        self.reversed = deepcopy(self.original)
        self.reversed[2][0][1].reverse()

    def compare(self, other, *, control=True):
        compare([json.dumps(self.original)], [json.dumps(other)], control=control)

    def test_reversal_must_change_order(self):
        self.compare(self.reversed)
        with self.assertRaisesRegex(ValueError, "not isolated and detected"):
            self.compare(self.original)

    def test_reversal_must_preserve_every_other_question(self):
        for question, value in [(0, [999]), (2, [[999, 1, 2]]), (3, [999]), (4, [[999, 1]])]:
            with self.subTest(question=question):
                corrupt = deepcopy(self.reversed)
                corrupt[2][0][question] = value
                with self.assertRaisesRegex(ValueError, "non-order disagreement"):
                    self.compare(corrupt)

    def test_reversal_must_preserve_each_enumeration_multiset(self):
        corrupt = deepcopy(self.reversed)
        first, second = self.reversed[2][0][1]
        for rank, change in [(0, [first, first]), (1, [first])]:
            with self.subTest(rank=rank):
                corrupt[2][rank][1] = change
                with self.assertRaisesRegex(ValueError, "non-order disagreement"):
                    self.compare(corrupt)
                corrupt = deepcopy(self.reversed)

    def test_schema_rejects_matching_corruptions(self):
        corruptions = (
            ("count", 0, ([None], [True], [1.0], [-1], [0], [1, 1])),
            ("enumeration", 1, ([[-1, []]], [[1, None]], [[1, [[True, []]]]])),
            ("minimum with ties", 2, ([[0, 1]], [[0, 2, 1]], [[None, 1, 2]], [[0, 0, 1]])),
            ("minimum", 3, ([[0]], [False], [1.0], [0, 1])),
            ("lexicographic", 4, ([[None, 0]], [[0, False]], [[0]])),
        )
        for question, index, invalid_bags in corruptions:
            for bag in invalid_bags:
                with self.subTest(question=question, bag=bag):
                    left, right = deepcopy(self.original), deepcopy(self.reversed)
                    # Keep the genuine reversal at rank 0, including when
                    # corrupting enumeration at the other rank.
                    left[2][1][index] = right[2][1][index] = bag
                    for control in (False, True):
                        with self.assertRaisesRegex(ValueError, f"invalid {question} answer"):
                            compare([json.dumps(left)], [json.dumps(right)], control=control)

    def test_schema_allows_absence_infinity_and_signed_scores(self):
        cell = [[1], [[0, []]], [[None, 1, 1]], [None], []]
        empty = [[], [], [], [], []]
        signed = [[1], [[1, []]], [[-1, 1, 1]], [-1], [[-1, -2]]]
        self.original[2].extend([cell, empty, signed])
        self.reversed[2].extend([cell, empty, signed])
        self.compare(self.reversed)

    def test_root_must_name_a_rank(self):
        for root in (-1, True, 2):
            with self.subTest(root=root):
                corrupt = deepcopy(self.reversed)
                corrupt[1] = root
                with self.assertRaisesRegex(ValueError, "invalid group, root or table"):
                    self.compare(corrupt)


if __name__ == "__main__":
    unittest.main()
