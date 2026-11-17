# Finite combinatorial regression checks

`scripts/check_combinatorics.py` is a deterministic Python standard-library
checker for the finite contracts used by the proof design. It is a finite
regression check, **not a general mathematical proof or Lean verification**.
It does not install or invoke Lean.

## Occurrences, concatenation, and residues

For a nonempty pattern `w` of length `k`, `C(w, u)` counts all overlapping
occurrences fully contained in `u`: a start `i` is counted exactly when
`0 <= i`, `i + k <= len(u)`, and the corresponding block equals `w`.

The checker exhausts all 255 binary words of lengths 0 through 7 and all 30
binary patterns of lengths 1 through 4. For every word/pattern pair it checks
`0 <= C(w, u) <= len(u)` and compares direct sliding-slice enumeration with
residue-wise block enumeration. For each `r` from 0 through `k - 1`, the group
contains the valid starting positions congruent to `r` modulo `k`. Writing
`M_r` for its size and `Y_r` for its matching-block count, it checks:

- The groups partition all valid starting positions exactly once.
- The length-`k` blocks within each group are disjoint.
- `sum(M_r) = max(len(u) - k + 1, 0)`.
- `sum(Y_r) = C(w, u)`.

These are 7,650 word/pattern cases. The direct counter uses tuple slicing;
the residue counter compares individual symbols at its selected starts.

Every split of each binary word of length at most 7 is also checked. This
exhausts all 1,793 ordered pairs `(u, v)` with `len(u) + len(v) <= 7`, including
empty and short words. Across the 30 patterns, the 53,790 cases check

```text
0 <= C(w, u ++ v) - C(w, u) - C(w, v) <= k - 1.
```

## Exact fourth central moments

For independent Bernoulli variables `B_i` with `p = 1/Q`, let
`S = sum(B_i - p)` over `M` variables. The checker uses `Fraction`, with no
floating-point arithmetic in these comparisons. For each `Q` in
`{2, 3, 4, 10}` and each `M` from 0 through 8, it computes the expectation
directly from the binomial distribution:

```text
sum over j = 0..M of binom(M,j) p^j (1-p)^(M-j) (j-Mp)^4.
```

It compares that value with

```text
mu2 = p(1-p)
mu4 = p(1-p)^4 + (1-p)p^4
E[S^4] = M mu4 + 3 M(M-1) mu2^2 <= 3 M^2.
```

All 36 rational cases include `M = 0`. This checks the moment calculation
for the specified independent Bernoulli model; it does not establish any
independence property of prime digits.

## Decimal digit convention

The optional digit check verifies decimal digit roundtrips for integers 0
through 1000. Digits are explicitly big-endian, so the words for the primes
`2, 3, 5, 7, 11` are `(2)`, `(3)`, `(5)`, `(7)`, `(1, 1)` and their
concatenation is `235711`.

## Recorded run

Run from the repository root, without Python's `-O` option (which the script
explicitly rejects):

```sh
python3 scripts/check_combinatorics.py
```

Locally executed on 2026-11-17 with Python 3.9.6; exit status 0:

```text
PASS: 7650 occurrence/residue cases
PASS: 53790 append cases
PASS: 36 exact rational fourth-moment cases
PASS: decimal roundtrips 0..1000; prime prefix 235711
Elapsed: 0.109 s
Finite regression only; not a general proof or Lean verification.
```

The elapsed time is the script's measured wall-clock duration for this run;
it will vary by machine. No random sampling is used. Cases beyond the stated
bounds, the asymptotic number-theoretic argument, and all Lean proof obligations
remain outside this check.
