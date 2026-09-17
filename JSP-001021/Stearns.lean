/-! # JSP-001021 — Stearns 定理（1959）：竞赛图必含大传递子竞赛图 -/

namespace JSP001021

open List

def Tournament (n : Nat) (beats : Fin n → Fin n → Bool) : Prop :=
  ∀ i j : Fin n, i ≠ j → beats i j = ! (beats j i)

def notBeats (beats : Fin n → Fin n → Bool) (v : Fin n) (b : Fin n) : Bool :=
  ! (beats v b)

def Transitive (beats : Fin n → Fin n → Bool) : List (Fin n) → Prop
  | [] => True
  | v :: rest => Transitive beats rest ∧ ∀ b ∈ rest, beats v b = true

def greedy (beats : Fin n → Fin n → Bool) : List (Fin n) → List (Fin n)
  | [] => []
  | v :: rest =>
      if (rest.filter (beats v)).length ≥ (rest.filter (notBeats beats v)).length then
        v :: greedy beats (rest.filter (beats v))
      else
        greedy beats (rest.filter (notBeats beats v)) ++ [v]
termination_by V => V.length
decreasing_by
  · simpa [List.length_cons] using (Nat.lt_of_le_of_lt (List.length_filter_le (beats v) rest) (Nat.lt_succ_self rest.length))
  · simpa [List.length_cons] using (Nat.lt_of_le_of_lt (List.length_filter_le (notBeats beats v) rest) (Nat.lt_succ_self rest.length))

theorem nodup_filter {α : Type} (p : α → Bool) {l : List α} (h : l.Nodup) :
    (l.filter p).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
      have ha : ¬ a ∈ as := (List.nodup_cons.mp h).1
      have has : as.Nodup := (List.nodup_cons.mp h).2
      have ihas : (as.filter p).Nodup := ih has
      by_cases hpa : p a = true
      · simp [List.nodup_cons, List.mem_filter, hpa, ha, ihas]
      · simpa [hpa] using ihas

theorem length_filter_add_length_filter_not {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun a => ! p a)).length = l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
      by_cases h : p a = true
      · simp [h]; omega
      · simp [h]; omega

theorem log2_le_of_lt_pow {n k : Nat} (h : n < 2 ^ (k + 1)) : Nat.log2 n ≤ k := by
  by_cases hn : n = 0
  · subst n; simp [Nat.log2_zero]
  · have hlt : Nat.log2 n < k + 1 := (Nat.log2_lt hn).2 h
    omega

theorem log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  apply log2_le_of_lt_pow
  exact Nat.lt_of_le_of_lt h Nat.lt_log2_self

theorem log2_two_mul_add_one (m : Nat) : Nat.log2 (2 * m + 1) ≤ Nat.log2 m + 1 := by
  apply log2_le_of_lt_pow
  have hmlt : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
  have h1 : 2 * m + 1 < 2 * (m + 1) := by omega
  have h2 : 2 * (m + 1) ≤ 2 * 2 ^ (Nat.log2 m + 1) := by omega
  have h3 : 2 * 2 ^ (Nat.log2 m + 1) = 2 ^ (Nat.log2 m + 2) := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
  omega

-- ============================== 贪心性质 ==============================

theorem greedy_subset {n : Nat} (beats : Fin n → Fin n → Bool) :
    ∀ (l : List (Fin n)) (b : Fin n), b ∈ greedy beats l → b ∈ l :=
  greedy.induct beats (motive := fun l => ∀ b, b ∈ greedy beats l → b ∈ l)
    (by intro b hb; simp [greedy.eq_1] at hb)
    (by
      intro v rest hwin ih b hb
      have hwin' : (rest.filter (beats v)).length ≥ (rest.filter (notBeats beats v)).length := by
        simpa using hwin
      rw [greedy.eq_2] at hb
      simp [hwin'] at hb
      rcases hb with rfl | hb
      · simp
      · have hb' : b ∈ greedy beats ((rest.attach.filter (fun x => beats v x.val)).unattach) := by
          simpa using hb
        have hbwin' : b ∈ (rest.attach.filter (fun x => beats v x.val)).unattach := ih b hb'
        have hbwin : b ∈ (rest.filter (beats v)) := by simpa using hbwin'
        have hbrest : b ∈ rest := ((List.mem_filter (p := beats v)).1 hbwin).1
        simp [hbrest])
    (by
      intro v rest hwin ih b hb
      have hwin' : ¬ (rest.filter (beats v)).length ≥ (rest.filter (notBeats beats v)).length := by
        simpa using hwin
      rw [greedy.eq_2] at hb
      simp [hwin'] at hb
      rcases hb with hb | rfl
      · have hb' : b ∈ greedy beats ((rest.attach.filter (fun x => notBeats beats v x.val)).unattach) := by
          simpa using hb
        have hblose' : b ∈ (rest.attach.filter (fun x => notBeats beats v x.val)).unattach := ih b hb'
        have hblose : b ∈ (rest.filter (notBeats beats v)) := by simpa using hblose'
        have hbrest : b ∈ rest := ((List.mem_filter (p := notBeats beats v)).1 hblose).1
        simp [hbrest]
      · simp)

theorem transitive_append {n : Nat} (beats : Fin n → Fin n → Bool) (l : List (Fin n)) (v : Fin n) :
    Transitive beats (l ++ [v]) ↔ Transitive beats l ∧ ∀ b ∈ l, beats b v = true := by
  induction l with
  | nil => simp [Transitive]
  | cons a as ih =>
      simp [Transitive, ih, List.mem_append]
      constructor
      · rintro ⟨⟨ht, hv⟩, ha⟩
        exact ⟨⟨ht, fun b hb => ha b (Or.inl hb)⟩, ha v (Or.inr rfl), hv⟩
      · rintro ⟨⟨ht, ha⟩, hav, hv⟩
        exact ⟨⟨ht, hv⟩, fun b hb => hb.elim (fun hb' => ha b hb') (fun heq => by subst b; exact hav)⟩

theorem greedy_nodup {n : Nat} (beats : Fin n → Fin n → Bool) :
    ∀ (V : List (Fin n)), V.Nodup → (greedy beats V).Nodup :=
  greedy.induct beats (motive := fun V => V.Nodup → (greedy beats V).Nodup)
    (by intro hV; simp [greedy.eq_1])
    (by
      intro v rest hwin ih hV
      have hwin' : (rest.filter (beats v)).length ≥ (rest.filter (notBeats beats v)).length := by
        simpa using hwin
      have hrest : rest.Nodup := (List.nodup_cons.mp hV).2
      have hvnot : ¬ v ∈ rest := (List.nodup_cons.mp hV).1
      have hwinnd : (rest.filter (beats v)).Nodup := nodup_filter (beats v) hrest
      have ihnd : (greedy beats (rest.filter (beats v))).Nodup := by
        simpa using (ih (by simpa using hwinnd))
      rw [greedy.eq_2]
      simp [hwin']
      constructor
      · intro hv
        have hvwin : v ∈ rest.filter (beats v) := greedy_subset beats (rest.filter (beats v)) v hv
        exact hvnot ((List.mem_filter (p := beats v)).1 hvwin).1
      · exact ihnd)
    (by
      intro v rest hwin ih hV
      have hwin' : ¬ (rest.filter (beats v)).length ≥ (rest.filter (notBeats beats v)).length := by
        simpa using hwin
      have hrest : rest.Nodup := (List.nodup_cons.mp hV).2
      have hvnot : ¬ v ∈ rest := (List.nodup_cons.mp hV).1
      have hlosend : (rest.filter (notBeats beats v)).Nodup := nodup_filter (notBeats beats v) hrest
      have ihnd : (greedy beats (rest.filter (notBeats beats v))).Nodup := by
        simpa using (ih (by simpa using hlosend))
      rw [greedy.eq_2]
      simp [hwin']
      rw [List.nodup_append]
      constructor
      · exact ihnd
      · constructor
        · simp
        · intro x hx b hb
          have hbv : b = v := List.mem_singleton.mp hb
          subst b
          intro heq
          have hx' : v ∈ greedy beats (rest.filter (notBeats beats v)) := by simpa [heq] using hx
          have hvlose : v ∈ rest.filter (notBeats beats v) := greedy_subset beats (rest.filter (notBeats beats v)) v hx'
          exact hvnot ((List.mem_filter (p := notBeats beats v)).1 hvlose).1)

theorem greedy_transitive {n : Nat} (beats : Fin n → Fin n → Bool) (htour : Tournament n beats) :
    ∀ (V : List (Fin n)), V.Nodup → Transitive beats (greedy beats V) :=
  greedy.induct beats (motive := fun V => V.Nodup → Transitive beats (greedy beats V))
    (by intro hV; simp [greedy.eq_1, Transitive])
    (by
      intro v rest hwin ih hV
      have hwin' : (rest.filter (beats v)).length ≥ (rest.filter (notBeats beats v)).length := by
        simpa using hwin
      have hrest : rest.Nodup := (List.nodup_cons.mp hV).2
      have hwinnd : (rest.filter (beats v)).Nodup := nodup_filter (beats v) hrest
      have ihwin : Transitive beats (greedy beats (rest.filter (beats v))) := by
        simpa using (ih (by simpa using hwinnd))
      rw [greedy.eq_2]
      simp [hwin']
      constructor
      · exact ihwin
      · intro b hb
        have hbwin : b ∈ rest.filter (beats v) := greedy_subset beats (rest.filter (beats v)) b hb
        exact (List.mem_filter (p := beats v)).1 hbwin |>.2)
    (by
      intro v rest hwin ih hV
      have hwin' : ¬ (rest.filter (beats v)).length ≥ (rest.filter (notBeats beats v)).length := by
        simpa using hwin
      have hrest : rest.Nodup := (List.nodup_cons.mp hV).2
      have hvnot : ¬ v ∈ rest := (List.nodup_cons.mp hV).1
      have hlosend : (rest.filter (notBeats beats v)).Nodup := nodup_filter (notBeats beats v) hrest
      have ihlose : Transitive beats (greedy beats (rest.filter (notBeats beats v))) := by
        simpa using (ih (by simpa using hlosend))
      rw [greedy.eq_2]
      simp [hwin']
      rw [transitive_append beats (greedy beats (rest.filter (notBeats beats v))) v]
      constructor
      · exact ihlose
      · intro b hb
        have hblose : b ∈ rest.filter (notBeats beats v) := greedy_subset beats (rest.filter (notBeats beats v)) b hb
        have hbnot : notBeats beats v b = true := (List.mem_filter (p := notBeats beats v)).1 hblose |>.2
        have hbrest : b ∈ rest := (List.mem_filter (p := notBeats beats v)).1 hblose |>.1
        have hbv : b ≠ v := by
          intro heq
          exact hvnot (heq ▸ hbrest)
        have hbeat : beats v b = false := by
          unfold notBeats at hbnot
          cases h : beats v b <;> simp_all
        have htv := htour b v hbv
        simpa [htv, hbeat])

theorem greedy_length {n : Nat} (beats : Fin n → Fin n → Bool) :
    ∀ (V : List (Fin n)), V ≠ [] → Nat.log2 V.length + 1 ≤ (greedy beats V).length :=
  greedy.induct beats (motive := fun V => V ≠ [] → Nat.log2 V.length + 1 ≤ (greedy beats V).length)
    (by intro h; cases h rfl)
    (by
      intro v rest hwin ih hVne
      have hwin' : (rest.filter (beats v)).length ≥ (rest.filter (notBeats beats v)).length := by
        simpa using hwin
      have ih' : (rest.filter (beats v)) ≠ [] → Nat.log2 (rest.filter (beats v)).length + 1 ≤ (greedy beats (rest.filter (beats v))).length := by
        simpa using ih
      have hpart : (rest.filter (beats v)).length + (rest.filter (notBeats beats v)).length = rest.length :=
        length_filter_add_length_filter_not (beats v) rest
      by_cases hw0 : (rest.filter (beats v)) = []
      · have hwinlen : (rest.filter (beats v)).length = 0 := by simp [hw0]
        have hrestlen : rest.length = 0 := by omega
        have hrestnil : rest = [] := List.eq_nil_of_length_eq_zero hrestlen
        subst rest
        simp [greedy.eq_1, greedy.eq_2, Nat.log2_def]
      · have ihwin := ih' hw0
        have h2win : 2 * (rest.filter (beats v)).length ≥ rest.length := by omega
        have hlen : rest.length + 1 ≤ 2 * (rest.filter (beats v)).length + 1 := by omega
        have hlog : Nat.log2 (rest.length + 1) ≤ Nat.log2 (rest.filter (beats v)).length + 1 :=
          Nat.le_trans (log2_mono hlen) (log2_two_mul_add_one (rest.filter (beats v)).length)
        rw [greedy.eq_2]
        simp [hwin']
        omega)
    (by
      intro v rest hwin ih hVne
      have hwin' : ¬ (rest.filter (beats v)).length ≥ (rest.filter (notBeats beats v)).length := by
        simpa using hwin
      have ih' : (rest.filter (notBeats beats v)) ≠ [] → Nat.log2 (rest.filter (notBeats beats v)).length + 1 ≤ (greedy beats (rest.filter (notBeats beats v))).length := by
        simpa using ih
      have hpart : (rest.filter (beats v)).length + (rest.filter (notBeats beats v)).length = rest.length :=
        length_filter_add_length_filter_not (beats v) rest
      have hl0 : (rest.filter (notBeats beats v)) ≠ [] := by
        intro h
        have hllen : (rest.filter (notBeats beats v)).length = 0 := by simp [h]
        have hwinlt : (rest.filter (beats v)).length < (rest.filter (notBeats beats v)).length := by
          omega
        omega
      have ihlose := ih' hl0
      have h2lose : 2 * (rest.filter (notBeats beats v)).length ≥ rest.length := by omega
      have hlen : rest.length + 1 ≤ 2 * (rest.filter (notBeats beats v)).length + 1 := by omega
      have hlog : Nat.log2 (rest.length + 1) ≤ Nat.log2 (rest.filter (notBeats beats v)).length + 1 :=
        Nat.le_trans (log2_mono hlen) (log2_two_mul_add_one (rest.filter (notBeats beats v)).length)
      rw [greedy.eq_2]
      simp [hwin']
      omega)

theorem stearns (n : Nat) (beats : Fin n → Fin n → Bool) (htour : Tournament n beats) (hn : 0 < n) :
    ∃ L : List (Fin n), Transitive beats L ∧ L.Nodup ∧ Nat.log2 n + 1 ≤ L.length := by
  let V := List.finRange n
  let L := greedy beats V
  refine ⟨L, ?_, ?_, ?_⟩
  · exact greedy_transitive beats htour V (List.nodup_finRange n)
  · exact greedy_nodup beats V (List.nodup_finRange n)
  · have hVne : V ≠ [] := by
      intro h
      have : List.finRange n = [] := by simpa [V] using h
      have hlen : (List.finRange n).length = 0 := by simp [this]
      have hlen2 : (List.finRange n).length = n := by simp
      omega
    have hlen := greedy_length beats V hVne
    simpa [V, L] using hlen

end JSP001021

#print axioms JSP001021.stearns
#print axioms JSP001021.greedy_length
#print axioms JSP001021.greedy_transitive
