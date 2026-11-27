"""Emit an interval menu for reviewing every explicit raise site in a Python file."""
import ast
from bisect import bisect_left, bisect_right
from hashlib import sha256
from pathlib import Path
import sys


def cover_spans(source):
    tree = ast.parse(source)
    sites = sorted({node.lineno for node in ast.walk(tree) if isinstance(node, ast.Raise)})
    blocks = sorted(
        (node.lineno, node.end_lineno)
        for node in ast.walk(tree)
        if isinstance(node, ast.stmt) and isinstance(getattr(node, "body", None), list)
    )
    rows = []
    for first, last in blocks:
        start, end = bisect_left(sites, first), bisect_right(sites, last)
        if start < end:
            # One source-location header plus all physical lines of the excerpt.
            rows.append((start, end, 1 + (last - first + 1)))
    return len(sites), rows


if __name__ == "__main__":
    path = Path(sys.argv[1])
    source = path.read_bytes()
    points, rows = cover_spans(source)
    print(f"# {path.name} SHA-256 {sha256(source).hexdigest()}")
    print(points)
    for row in rows:
        print(*row)
