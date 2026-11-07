# Readability revision

The challenge was revised at the user's explicit request. The previous challenge,
solution, frozen hashes, and successful comparator log are preserved under
`verification/previous/`. `comparator.json` is unchanged. `FROZEN.sha256` now
records the revised challenge, which is fixed for its verification run.

## What changed

The challenge has four definitions instead of nine. It retains `rademacherMean`,
`orderedUnit`, `extremizerDistance`, and `haagerupF`, each representing a recurring
mathematical concept. Internal proof files may still use the previous helper
names; they are no longer needed to read the challenge.

- `bestConstant` is replaced by the explicit real expression
  `(2 - Real.sqrt 2) ^ ((3 : ℝ) / 2) / 8`.
- `validConstant` is replaced by the displayed set of admissible coefficients.
  `IsGreatest S c` means `c ∈ S` and `∀ d ∈ S, d ≤ c`, so it states both the
  universal inequality and the optimality of the constant.
- Dimensions at least two are written as `n + 2` with `n : ℕ`. This is a bijective
  reindexing of the old dimensions, not a restriction of their range. It allows
  the first two coordinates to be written `a 0` and `a 1` directly.
- `topTwo` is replaced by `a 0 + a 1`.
- `fourEqual` and `evenEqual` are replaced by local, explicit vector formulas.
- The four-coordinate vector's `orderedUnit` conjunct is omitted because its
  formula and `4 ≤ n` imply it. The proof `fourEqual_unit` remains available.
- The even-coordinate vector's `orderedUnit` and top-two-at-most-one conjuncts
  are omitted because its formula, `2 ≤ m`, and `2*m ≤ n` imply them. The proofs
  `evenEqual_unit` and `evenEqual_topTwo_le_one` remain available.
- For that even-coordinate vector, the first two coordinates sum to
  `2 / sqrt(2*m)`, hence `4 / (a 0 + a 1)^2 = 2*m`. Its equality statement is
  therefore written `rademacherMean a = haagerupF (2 * (m : ℝ))`.

All arbitrary zero padding and every original bound, sharpness claim, and
equality case remain. The Euclidean distance definition is retained to make the
geometric quantity explicit; replacing it with a coordinate formula would make
the public statement less direct.

## Lean evidence for the reformulation

In `Solution.lean`, `theorem1_original` and `theorem2_original` retain complete
proofs of the previous statements. The revised targets are derived from those
statements using only reindexing, unfolding, and the equality-vector argument
identity. Conversely, `theorem1_recovers_original` and
`theorem2_recovers_original` derive every original conjunct from the revised
targets and the automatic normalization facts. These reverse conversions compile
and use only the permitted standard axioms.

The full revised comparator result is recorded in `comparator-revised.log`.
The previous successful log alone is not evidence for this revision.
