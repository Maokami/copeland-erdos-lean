#!/usr/bin/env python3
"""Finite regression checks for the paper's combinatorial contracts.

Uses only the Python standard library. These bounded checks are not proofs.
"""

from fractions import Fraction
from itertools import product
from math import comb
from time import perf_counter


def binary_words(length):
    return product((0, 1), repeat=length)


def occurrences(pattern, word):
    """Count overlapping copies fully contained in word; pattern is nonempty."""
    k = len(pattern)
    return sum(word[i : i + k] == pattern for i in range(len(word) - k + 1))


def check_words():
    patterns = [p for k in range(1, 5) for p in binary_words(k)]
    words = [w for length in range(8) for w in binary_words(length)]
    residue_cases = 0
    append_cases = 0

    for word in words:
        for pattern in patterns:
            k = len(pattern)
            direct = occurrences(pattern, word)
            assert 0 <= direct <= len(word), (pattern, word, direct)
            valid = max(len(word) - k + 1, 0)
            groups = [list(range(r, valid, k)) for r in range(k)]
            # Each residue selects disjoint length-k blocks. Together the
            # residues partition every valid starting position exactly once.
            assert sorted(i for group in groups for i in group) == list(range(valid))
            assert all(
                left + k <= right
                for group in groups
                for left, right in zip(group, group[1:])
            )
            capacities = [len(group) for group in groups]
            matches = [
                sum(
                    all(word[i + j] == pattern[j] for j in range(k))
                    for i in group
                )
                for group in groups
            ]
            assert sum(capacities) == valid, (pattern, word, capacities)
            assert sum(matches) == direct, (pattern, word, matches, direct)
            residue_cases += 1

    # Every split of every word of length <= 7 enumerates every ordered pair
    # (u, v) with total length <= 7, including either or both words empty.
    for word in words:
        for split in range(len(word) + 1):
            u, v = word[:split], word[split:]
            for pattern in patterns:
                crossing = (
                    occurrences(pattern, word)
                    - occurrences(pattern, u)
                    - occurrences(pattern, v)
                )
                assert 0 <= crossing <= len(pattern) - 1, (pattern, u, v, crossing)
                append_cases += 1

    return residue_cases, append_cases


def check_fourth_moments():
    cases = 0
    for q in (2, 3, 4, 10):
        p = Fraction(1, q)
        mu2 = p * (1 - p)
        mu4 = p * (1 - p) ** 4 + (1 - p) * p**4
        for m in range(9):
            # Exact binomial expectation of (sum B_i - m*p)^4,
            # evaluated independently of the central-moment formula.
            binomial = sum(
                comb(m, j) * p**j * (1 - p) ** (m - j) * (j - m * p) ** 4
                for j in range(m + 1)
            )
            formula = m * mu4 + 3 * m * (m - 1) * mu2**2
            assert binomial == formula, (q, m, binomial, formula)
            assert 0 <= binomial <= 3 * m**2, (q, m, binomial)
            cases += 1
    return cases


def decimal_digits(n):
    """Return the usual big-endian decimal representation, including zero."""
    if n == 0:
        return (0,)
    digits = []
    while n:
        n, digit = divmod(n, 10)
        digits.append(digit)
    return tuple(reversed(digits))


def check_digits():
    for n in range(1001):
        reconstructed = 0
        for digit in decimal_digits(n):
            reconstructed = 10 * reconstructed + digit
        assert reconstructed == n, (n, decimal_digits(n), reconstructed)
    prefix = tuple(digit for p in (2, 3, 5, 7, 11) for digit in decimal_digits(p))
    assert prefix == (2, 3, 5, 7, 1, 1), prefix
    return "".join(map(str, prefix))


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: this checker uses assertions.")
    started = perf_counter()
    residue_cases, append_cases = check_words()
    moment_cases = check_fourth_moments()
    prefix = check_digits()
    print(f"PASS: {residue_cases} occurrence/residue cases")
    print(f"PASS: {append_cases} append cases")
    print(f"PASS: {moment_cases} exact rational fourth-moment cases")
    print(f"PASS: decimal roundtrips 0..1000; prime prefix {prefix}")
    print(f"Elapsed: {perf_counter() - started:.3f} s")
    print("Finite regression only; not a general proof or Lean verification.")


if __name__ == "__main__":
    main()
