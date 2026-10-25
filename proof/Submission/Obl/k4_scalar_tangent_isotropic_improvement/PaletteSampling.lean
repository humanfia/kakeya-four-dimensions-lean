import Mathlib

/-! Common-state sampling against a fixed, unnormalized reference palette. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open scoped BigOperators Classical

attribute [-instance] Nat.decidableForallFin Fintype.decidableForallFintype

/-- A weighted average with total weight one has a supporting term at least as
large as every lower bound for the average. -/
theorem exists_weighted_sample {β : Type*} [Fintype β] (w f : β → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (c : ℝ)
    (hc : c ≤ ∑ j, w j * f j) : ∃ j, 0 < w j ∧ c ≤ f j := by
  classical
  by_contra hno
  push Not at hno
  have hpos : ∃ j, 0 < w j := by
    by_contra hn
    push Not at hn
    have hsum : ∑ j, w j ≤ 0 := Finset.sum_nonpos (fun j hj => hn j)
    rw [hw1] at hsum
    norm_num at hsum
  obtain ⟨j₀, hj₀⟩ := hpos
  have hle (j : β) : w j * f j ≤ w j * c := by
    rcases eq_or_lt_of_le (hw j) with hj | hj
    · rw [← hj]
      simp
    · exact mul_le_mul_of_nonneg_left (hno j hj).le (hw j)
  have hstrict : w j₀ * f j₀ < w j₀ * c := mul_lt_mul_of_pos_left (hno j₀ hj₀) hj₀
  have hsum := Finset.sum_lt_sum (fun j hj => hle j) ⟨j₀, Finset.mem_univ _, hstrict⟩
  rw [← Finset.sum_mul, hw1, one_mul] at hsum
  exact (not_lt_of_ge hc) hsum

/-- The same weighted pigeonhole applies to a subprobability palette at a
positive target. The unused weight can be assigned score zero. -/
theorem exists_weighted_sample_of_subprobability {β : Type*} [Fintype β] (w f : β → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j ≤ 1) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ ∑ j, w j * f j) : ∃ j, 0 < w j ∧ c ≤ f j := by
  classical
  let w' : Option β → ℝ := fun j => match j with | none => 1 - ∑ j, w j | some j => w j
  let f' : Option β → ℝ := fun j => match j with | none => 0 | some j => f j
  have hw' : ∀ j, 0 ≤ w' j := by
    intro j
    cases j with
    | none => dsimp [w']; linarith
    | some j => exact hw j
  have hw1' : ∑ j, w' j = 1 := by simp [w']
  have hmean : c ≤ ∑ j, w' j * f' j := by simpa [w', f'] using hc
  obtain ⟨j, hj, hfj⟩ := exists_weighted_sample w' f' hw' hw1' c hmean
  cases j with
  | none => simp only [f'] at hfj; exact (not_le_of_gt hc0 hfj).elim
  | some j => exact ⟨j, hj, hfj⟩

/-- One choice of velocity keeps a definite fraction of the original state
weights when each state has that much allowed palette mass. -/
theorem palette_select_state {ι β : Type*} [Fintype β] (w : β → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j ≤ 1) (m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) (S : Finset ι) (hS : 0 < ∑ i ∈ S, m i)
    (Good : ι → β → Prop) (Allowed : β → Prop) {q : ℝ} (hq : 0 < q)
    (hgood : ∀ i ∈ S, q ≤ ∑ j : β, if Allowed j ∧ Good i j then w j else 0) :
    ∃ j : β, Allowed j ∧ q * (∑ i ∈ S, m i) ≤ ∑ i ∈ S.filter (fun i => Good i j), m i := by
  classical
  let score : β → ℝ := fun j => if Allowed j then ∑ i ∈ S.filter (fun i => Good i j), m i else 0
  have havg : q * (∑ i ∈ S, m i) ≤ ∑ j, w j * score j := by
    calc
      q * (∑ i ∈ S, m i) = ∑ i ∈ S, m i * q := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ ∑ i ∈ S, m i * (∑ j : β, if Allowed j ∧ Good i j then w j else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hgood i hi) (hm i)
      _ = ∑ j, w j * score j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases ha : Allowed j
        · simp only [score, ite_eq_left ha, Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hg : Good i j <;> simp [ha, hg] <;> ring
        · simp [score, ha]
  obtain ⟨j, hj, hscore⟩ := exists_weighted_sample_of_subprobability w score hw hw1 (mul_pos hq hS) havg
  have ha : Allowed j := by
    by_contra hn
    simp only [score, ite_eq_right hn] at hscore
    exact (not_le_of_gt (mul_pos hq hS)) hscore
  exact ⟨j, ha, by simpa only [score, ite_eq_left ha] using hscore⟩

/-- Deleting the neighborhoods of at most three preceding velocities costs
less than half of each state's original good-palette mass. -/
theorem palette_mass_after_three_exclusions {β : Type*} [Fintype β]
    (w v : β → ℝ) (hw : ∀ j, 0 ≤ w j) (Good : β → Prop) {q δ : ℝ} (hq : 0 < q)
    (hgood : q ≤ ∑ j : β, if Good j then w j else 0)
    (hcap : ∀ u : ℝ, (∑ j : β, if |v j - u| < δ then w j else 0) ≤ q / 8)
    (n : ℕ) (hn : n ≤ 3) (u : Fin n → ℝ) :
    q / 2 ≤ ∑ j : β, if (∀ a, δ ≤ |v j - u a|) ∧ Good j then w j else 0 := by
  classical
  have hpoint (j : β) : (if Good j then w j else 0) ≤
      (if (∀ a, δ ≤ |v j - u a|) ∧ Good j then w j else 0) +
        ∑ a : Fin n, if |v j - u a| < δ then w j else 0 := by
    have hnonneg (a : Fin n) : 0 ≤ if |v j - u a| < δ then w j else 0 := by
      split_ifs
      · exact hw j
      · exact le_rfl
    by_cases hg : Good j
    · by_cases ha : ∀ a, δ ≤ |v j - u a|
      · rw [ite_eq_left hg, ite_eq_left (And.intro ha hg)]
        exact le_add_of_nonneg_right (Finset.sum_nonneg (fun a ha => hnonneg a))
      · have hex : ∃ a, |v j - u a| < δ := by push Not at ha; exact ha
        obtain ⟨a, ha'⟩ := hex
        rw [ite_eq_left hg, ite_eq_right (by intro h; exact ha h.1), zero_add]
        have hsingle := Finset.single_le_sum (f := fun a : Fin n => if |v j - u a| < δ then w j else 0)
          (fun a ha => hnonneg a) (Finset.mem_univ a)
        simpa only [ite_eq_left ha'] using hsingle
    · simp only [hg, and_false, ite_false, zero_add]
      exact Finset.sum_nonneg (fun a ha => hnonneg a)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j hj => hpoint j)
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
  have hbad : (∑ a : Fin n, ∑ j : β, if |v j - u a| < δ then w j else 0) ≤ (n : ℝ) * (q / 8) := by
    calc
      _ ≤ ∑ _a : Fin n, q / 8 := Finset.sum_le_sum (fun a ha => hcap (u a))
      _ = _ := by simp
  have hn' : (n : ℝ) ≤ 3 := by exact_mod_cast hn
  have hcount := mul_le_mul_of_nonneg_right hn' (by positivity : 0 ≤ q / 8)
  nlinarith

/-- Four separated velocities have a common family of good states with a
polynomial fraction of the original state mass. No incidence normalization is
performed, and every selection is averaged against the same palette `w`. -/
theorem common_palette_four {ι β : Type*} [Fintype β]
    (w v : β → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j ≤ 1)
    (m : ι → ℝ) (hm : ∀ i, 0 ≤ m i) (S : Finset ι) (hS : 0 < ∑ i ∈ S, m i)
    (Good : ι → β → Prop) {q δ : ℝ} (hq : 0 < q)
    (hgood : ∀ i ∈ S, q ≤ ∑ j : β, if Good i j then w j else 0)
    (hcap : ∀ u : ℝ, (∑ j : β, if |v j - u| < δ then w j else 0) ≤ q / 8) :
    ∃ a : Fin 4 → β, (∀ r s, r ≠ s → δ ≤ |v (a r) - v (a s)|) ∧
      (q / 2) ^ 4 * (∑ i ∈ S, m i) ≤
        ∑ i ∈ S.filter (fun i => ∀ r, Good i (a r)), m i := by
  classical
  have hhalf : 0 < q / 2 := by positivity
  have haux : ∀ n : ℕ, n ≤ 4 → ∃ a : Fin n → β,
      (∀ r s, r ≠ s → δ ≤ |v (a r) - v (a s)|) ∧
      (q / 2) ^ n * (∑ i ∈ S, m i) ≤
        ∑ i ∈ S.filter (fun i => ∀ r, Good i (a r)), m i := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro r
        exact Fin.elim0 r
      · simp
    | succ n ih =>
      intro hn
      obtain ⟨a, ha, hmass⟩ := ih (by omega)
      let T : Finset ι := S.filter (fun i => ∀ r, Good i (a r))
      have hT : 0 < ∑ i ∈ T, m i :=
        lt_of_lt_of_le (mul_pos (pow_pos hhalf n) hS) hmass
      let Allowed : β → Prop := fun j => ∀ r, δ ≤ |v j - v (a r)|
      have hallowed : ∀ i ∈ T, q / 2 ≤
          ∑ j : β, if Allowed j ∧ Good i j then w j else 0 := by
        intro i hi
        exact palette_mass_after_three_exclusions w v hw (Good i) hq
          (hgood i (Finset.mem_filter.mp hi).1) hcap n (by omega) (fun r => v (a r))
      obtain ⟨j, hj, hjmass⟩ := palette_select_state w hw hw1 m hm T hT Good Allowed hhalf hallowed
      refine ⟨Fin.cons j a, ?_, ?_⟩
      · intro r s hrs
        cases r using Fin.cases with
        | zero =>
          cases s using Fin.cases with
          | zero => exact (hrs rfl).elim
          | succ s => simpa only [Fin.cons_zero, Fin.cons_succ] using hj s
        | succ r =>
          cases s using Fin.cases with
          | zero => simpa only [Fin.cons_zero, Fin.cons_succ, abs_sub_comm] using hj r
          | succ s =>
            simp only [Fin.cons_succ]
            apply ha r s
            intro heq
            exact hrs (congrArg Fin.succ heq)
      · have hfilter : T.filter (fun i => Good i j) =
            S.filter (fun i => ∀ r : Fin (n + 1), Good i ((Fin.cons j a : Fin (n + 1) → β) r)) := by
          ext i
          simp only [T, Finset.mem_filter, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
          tauto
        calc
          (q / 2) ^ (n + 1) * (∑ i ∈ S, m i) =
              (q / 2) * ((q / 2) ^ n * (∑ i ∈ S, m i)) := by rw [pow_succ]; ring
          _ ≤ (q / 2) * (∑ i ∈ T, m i) := mul_le_mul_of_nonneg_left hmass hhalf.le
          _ ≤ ∑ i ∈ T.filter (fun i => Good i j), m i := hjmass
          _ = _ := by rw [hfilter]
  exact haux 4 le_rfl

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
