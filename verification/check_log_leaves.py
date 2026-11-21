"""Check public log leaf results against a high-precision decimal oracle."""

from decimal import Decimal, localcontext
import math
import random
import struct
import subprocess
import sys

U128_BITS = 128
MAX_WEIGHT = (1 << U128_BITS) - 1
# Binary64 has 53 significand bits, including the implicit leading digit.
FRACTION_BITS = sys.float_info.mant_dig - 1
EPSILON = Decimal.from_float(sys.float_info.epsilon)
# After cancellation in the closest-to-unit pairs (39 decimal places),
# at least 80 significant digits remain for comparison with binary64.
ORACLE_PRECISION = 120
# The documented conditional bound for the conversion alone.
EPSILON_BOUND = 4
# Fixed seed for replay. 1,500 mixed mantissas give at least 11 proposals
# per denominator bit length in addition to all the structured cast ties.
SEED = 902
MIXED_PAIRS = 1_500


def domain():
    pairs = {(0, 1), (1, 1), (MAX_WEIGHT, MAX_WEIGHT)}

    def add(n, d):
        if 0 < n <= MAX_WEIGHT and 0 < d <= MAX_WEIGHT:
            pairs.update(((n, d), (d, n)))

    for power in range(U128_BITS):
        pivot = 1 << power
        midpoint = 1 << max(0, power - FRACTION_BITS - 1)
        for distance in {1, 2, midpoint - 1, midpoint, midpoint + 1, 2 * midpoint + 1}:
            for neighbor in (pivot - distance, pivot + distance):
                for anchor in (pivot, 1, MAX_WEIGHT):
                    add(neighbor, anchor)

    rng = random.Random(SEED)
    for index in range(MIXED_PAIRS):
        n = max(1, rng.getrandbits(U128_BITS))
        top = 1 << (index % U128_BITS)
        d = top | rng.getrandbits(top.bit_length() - 1)
        add(n, d)
        add(n, n + d)
    return sorted(pairs)


def check(binary):
    pairs = domain()
    observations = subprocess.run(
        [binary], input="".join(f"{n} {d}\n" for n, d in pairs),
        text=True, capture_output=True, check=True,
    ).stdout.splitlines()
    names = ("LogSumProduct", "LogMaxProduct")
    worst = dict.fromkeys(names, Decimal(0))
    with localcontext() as context:
        context.prec = ORACLE_PRECISION
        for (n, d), row in zip(pairs, observations, strict=True):
            expected = (Decimal(n) / d).ln()
            for name, bits in zip(names, row.split(), strict=True):
                actual = struct.unpack(">d", bytes.fromhex(bits))[0]
                if n == 0:
                    valid = actual == -math.inf
                elif n == d:
                    valid = actual == 0.0
                elif math.isfinite(actual):
                    error = abs((Decimal.from_float(actual) - expected) / expected) / EPSILON
                    valid = (actual > 0 if n > d else actual < 0) and error <= EPSILON_BOUND
                    worst[name] = max(worst[name], error)
                else:
                    valid = False
                if not valid:
                    raise ValueError(f"{name} leaf {n}/{d}: {actual!r}, oracle {expected}")

    for name, error in worst.items():
        print(f"{name}: {len(pairs)} leaves, maximum relative error {error:.6f} epsilon, 0 disagreements")


if __name__ == "__main__":
    check(sys.argv[1])
