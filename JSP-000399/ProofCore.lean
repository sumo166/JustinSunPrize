/-! # JSP-000399（core-Lean，无 mathlib 依赖）— 可机器验证版本

  Selfridge–Straus 问题 `s = n − 1` 情形的形式化。
  只依赖 Lean 4 核心库（`List` / `Int` / `omega`），不 `import Mathlib`，
  用 `lean ProofCore.lean` 即可直接验证，无需构建 mathlib。

  主定理 `m1sums_determine_translate`：
    若两个整数列表 A、B 的 (n−1) 重和多重集相等（`m1sums A ~ m1sums B`），
    则 A 是 B 的一个平移（存在整数 t 使 `A ~ B.map (fun b => t + b)`）。
  这正是原题的答案："由 (n−1) 重和唯一还原（至多相差一个平移）"。
  证明只用线性算术（omega），无需 `ring`/`nlinarith`（避免 mathlib 依赖）。
-/

namespace JSP399

open List

/-- A 的 (n−1) 重和列表：`S_A − a`，其中 `S_A = A.sum`（去掉一个元素后其余求和）。 -/
def m1sums (A : List Int) : List Int :=
  A.map (fun a => A.sum - a)

/-- 反射：`S − (S − a) = a`，故对 (n−1) 重和再取一次 (n−1) 重和即回到原列表。 -/
theorem m1sums_m1sums (A : List Int) :
    (m1sums A).map (fun y => A.sum - y) = A := by
  unfold m1sums
  rw [map_map]
  have h : ((fun y => A.sum - y) ∘ fun a => A.sum - a) = (fun a => a) := by
    funext x
    simp
    omega
  rw [h]
  simp

/-- 主定理：若 A、B 的 (n−1) 重和多重集相等，则 A 是 B 的一个平移。 -/
theorem m1sums_determine_translate (A B : List Int) (hperm : (m1sums A).Perm (m1sums B)) :
    ∃ t : Int, A.Perm (B.map (fun b => t + b)) := by
  -- 用同一个函数 `A.sum - ·` 作用到两边
  have hmapped : ((m1sums A).map (fun y => A.sum - y)).Perm ((m1sums B).map (fun y => A.sum - y)) := by
    exact List.Perm.map (fun y => A.sum - y) hperm
  -- 左端 = A
  have hA : (m1sums A).map (fun y => A.sum - y) = A := m1sums_m1sums A
  -- 右端 = B 平移 (A.sum − B.sum)
  have hB : (m1sums B).map (fun y => A.sum - y) = B.map (fun b => (A.sum - B.sum) + b) := by
    unfold m1sums
    rw [map_map]
    congr 1
    funext b
    simp
    omega
  -- 结论：取 t = A.sum − B.sum
  refine ⟨A.sum - B.sum, ?_⟩
  calc
    A = (m1sums A).map (fun y => A.sum - y) := hA.symm
    _ ~ (m1sums B).map (fun y => A.sum - y) := hmapped
    _ = B.map (fun b => (A.sum - B.sum) + b) := hB

end JSP399

-- 公理审计：主定理与反射引理不应依赖任何额外公理
#print axioms JSP399.m1sums_determine_translate
#print axioms JSP399.m1sums_m1sums
