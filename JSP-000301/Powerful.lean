/-! # JSP-000301 — 连续 powerful 数反例（Golomb 1970，core-Lean）

  问题：若两个连续正整数都是 powerful 数，是否其中至少一个是完全平方数？

  答案：**否**。Golomb (1970) 的反例：
    12167 = 23³ 与 12168 = 2³ · 3² · 13² 是两个连续的正整数，
    二者都是 powerful 数，且都不是完全平方数。

  形式化约定：powerful 数用等价的 Golomb 刻画 `∃ a b, n = a² · b³`
  （等价于标准定义「对每个素数 p，p | n ⟹ p² | n」）。
  该刻画只涉及自然数乘法和存在量词，无需 mathlib 的 `Nat.Prime`，
  因此本文件保持 core-Lean 单文件、可 `lean Powerful.lean` 直接验证。

  反例检验：
    · 12167 = 1² · 23³ （powerful）
    · 12168 = 39² · 2³ （powerful；因 39² = 1521、2³ = 8、1521 · 8 = 12168）
    · 110² = 12100 < 12167 < 12168 < 12321 = 111²，故两者都不是完全平方数。
-/

namespace JSP000301

/-- `n` 是完全平方数。 -/
def IsSquare (n : Nat) : Prop := ∃ k : Nat, k * k = n

/-- `n` 是 powerful 数（Golomb 刻画：`n = a² · b³`）。 -/
def IsPowerful (n : Nat) : Prop := ∃ a b : Nat, a * a * b * b * b = n

theorem not_square_12167 : ¬ IsSquare 12167 := by
  intro h
  rcases h with ⟨k, hk⟩
  rcases Nat.lt_or_ge k 111 with hlt | hge
  · have hk_le : k ≤ 110 := Nat.le_of_lt_succ hlt
    have hs : k * k ≤ 110 * 110 := Nat.mul_le_mul hk_le hk_le
    have h_lt : k * k < 12167 := by
      calc
        k * k ≤ 110 * 110 := hs
        _ = 12100 := by decide
        _ < 12167 := by decide
    rw [hk] at h_lt
    exact Nat.lt_irrefl 12167 h_lt
  · have hs : 111 * 111 ≤ k * k := Nat.mul_le_mul hge hge
    have h_lt : 12167 < k * k := by
      calc
        12167 < 12321 := by decide
        _ = 111 * 111 := by decide
        _ ≤ k * k := hs
    rw [hk] at h_lt
    exact Nat.lt_irrefl 12167 h_lt

theorem not_square_12168 : ¬ IsSquare 12168 := by
  intro h
  rcases h with ⟨k, hk⟩
  rcases Nat.lt_or_ge k 111 with hlt | hge
  · have hk_le : k ≤ 110 := Nat.le_of_lt_succ hlt
    have hs : k * k ≤ 110 * 110 := Nat.mul_le_mul hk_le hk_le
    have h_lt : k * k < 12168 := by
      calc
        k * k ≤ 110 * 110 := hs
        _ = 12100 := by decide
        _ < 12168 := by decide
    rw [hk] at h_lt
    exact Nat.lt_irrefl 12168 h_lt
  · have hs : 111 * 111 ≤ k * k := Nat.mul_le_mul hge hge
    have h_lt : 12168 < k * k := by
      calc
        12168 < 12321 := by decide
        _ = 111 * 111 := by decide
        _ ≤ k * k := hs
    rw [hk] at h_lt
    exact Nat.lt_irrefl 12168 h_lt

/-- 主定理：存在两个连续正整数，二者都是 powerful 数，且都不是完全平方数。 -/
theorem golomb_powerful_counterexample :
    ∃ n : Nat, IsPowerful n ∧ IsPowerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  refine ⟨12167, ?_, ?_, ?_, ?_⟩
  · exact ⟨1, 23, by decide⟩
  · have h1 : 12167 + 1 = 12168 := by decide
    rw [h1]
    exact ⟨39, 2, by decide⟩
  · exact not_square_12167
  · have h1 : 12167 + 1 = 12168 := by decide
    rw [h1]
    exact not_square_12168

/-- 原命题的否定：并非「任意两个连续 powerful 数中至少有一个是完全平方数」。 -/
theorem golomb_disproves_claim :
    ¬ (∀ n : Nat, IsPowerful n → IsPowerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  have hsq := h 12167 ⟨1, 23, by decide⟩ (by
    have h1 : 12167 + 1 = 12168 := by decide
    rw [h1]
    exact ⟨39, 2, by decide⟩)
  rcases hsq with hs | hs
  · exact not_square_12167 hs
  · have h1 : 12167 + 1 = 12168 := by decide
    rw [h1] at hs
    exact not_square_12168 hs

end JSP000301
