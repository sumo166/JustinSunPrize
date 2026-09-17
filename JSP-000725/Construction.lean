import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

namespace JSP000725

/-- Gauss sum over ℚ: `∑_{i<n} i = n*(n-1)/2`. -/
lemma sum_range_id_q (n : Nat) :
    (Finset.sum (Finset.range n) (fun i => (i : ℚ))) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      push_cast
      ring_nf

/-- For the interval `[m, m+k-1]`, the sum of the `t` largest elements is strictly
    less than the sum of the `(t+1)` smallest elements, whenever `m` is large enough
    relative to `k` (namely `4*m > (k-1)^2`). -/
theorem interval_sum_bound (m k t : Nat) (ht : 1 ≤ t) (htk : t < k)
    (hm : 4 * m > (k - 1) * (k - 1)) :
    (Finset.sum (Finset.range t) (fun i => ((m : ℚ) + ((k - 1 : Nat) : ℚ) - (i : ℚ)))) <
      (Finset.sum (Finset.range (t + 1)) (fun i => ((m : ℚ) + (i : ℚ)))) := by
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  rw [sum_range_id_q t, sum_range_id_q (t + 1)]
  have hmq : (4 : ℚ) * m > ((k - 1 : Nat) : ℚ) * ((k - 1 : Nat) : ℚ) := by
    exact_mod_cast hm
  have hquad : (4 : ℚ) * t * (((k - 1 : Nat) : ℚ) - t) ≤ (((k - 1 : Nat) : ℚ) * ((k - 1 : Nat) : ℚ)) := by
    nlinarith [sq_nonneg (((k - 1 : Nat) : ℚ) - 2 * t)]
  have hk : 1 ≤ k := by omega
  have hsucc : (↑(t + 1) : ℚ) = (t : ℚ) + 1 := by norm_num
  have hpredk : (↑(k - 1) : ℚ) = (k : ℚ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [hsucc, hpredk]
  rw [hpredk] at hmq hquad
  have htq : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have htkq : (t : ℚ) < k := by exact_mod_cast htk
  ring_nf at *
  nlinarith

end JSP000725

#print axioms JSP000725.interval_sum_bound
