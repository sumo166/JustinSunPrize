# JustinSunPrize — Lean formalizations (monorepo)

Machine-verified Lean proofs for Justin Sun Prize problems.

| Problem | Proof | Status |
| --- | --- | --- |
| JSP-001021 | [Stearns.lean](JSP-001021/Stearns.lean) — transitive subtournament lower bound | machine-verified |
| JSP-000399 | [ProofCore.lean](JSP-000399/ProofCore.lean) — (n−1)-fold sums determine the set | machine-verified |
| JSP-000725 | [Construction.lean](JSP-000725/Construction.lean) — interval construction | machine-verified |

## Toolchain

- Lean 4.34.0. JSP-000399 and JSP-001021 are core-Lean (no mathlib);
  JSP-000725 uses mathlib (v4.34.0).
