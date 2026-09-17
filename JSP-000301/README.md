# JSP-000301 — Consecutive powerful numbers counterexample (Golomb 1970)

Formalizes the **disproof** of: "If two consecutive positive integers are both
powerful, must at least one be a perfect square?"

Golomb's counterexample: `12167 = 23³` and `12168 = 2³·3²·13²` are consecutive
powerful numbers, and neither is a perfect square.

## Files

- `Powerful.lean` — the formalization.

## Reproduce

- Lean 4.34.0, core only (no mathlib).
- `lean Powerful.lean` → exit 0.

## Main theorems

- `JSP000301.golomb_powerful_counterexample` :
  `∃ n, IsPowerful n ∧ IsPowerful (n+1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n+1)`
- `JSP000301.golomb_disproves_claim` :
  the exact negation of "every pair of consecutive powerful numbers contains a square".

## Notes

- `IsPowerful n := ∃ a b, n = a²·b³` is the Golomb characterization of a
  powerful number (equivalent to "for every prime p, p | n ⟹ p² | n").
- No axioms are used (checked with `#print axioms`).
