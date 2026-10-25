import Submission.Obl.k4_weighted_convex_tubes.Sampling

open scoped BigOperators

namespace Submission.Obl.k4_oss_bad_direction_extraction

/-- Sampling finitely many weighted points controls every real interval by testing its
two extreme selected points. -/
theorem exists_interval_sample {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hP : 16 ≤ ∑ i, p i) {L : ℝ} (hL : 0 ≤ L)
    (hcount : 4 * (Fintype.card ι : ℝ) ^ 2 ≤ Real.exp (L / 2)) :
    ∃ T : Finset ι, (∑ i, p i) ≤ 2 * T.card ∧
      ∀ a b : ℝ, ((T.filter (fun i => a ≤ x i ∧ x i ≤ b)).card : ℝ) ≤
        4 * ∑ i ∈ Finset.univ.filter (fun i => a ≤ x i ∧ x i ≤ b), p i + L := by
  classical
  let e := Fintype.equivFin (ι × ι)
  let U : Fin (Fintype.card (ι × ι)) → Finset ι := fun h =>
    Finset.univ.filter (fun i => x (e.symm h).1 ≤ x i ∧ x i ≤ x (e.symm h).2)
  let t : Fin (Fintype.card (ι × ι)) → ℝ := fun h => 4 * ∑ i ∈ U h, p i + L
  obtain ⟨T, hT, htests⟩ :=
    Submission.Obl.k4_weighted_convex_tubes.exists_good_subset p hp0 hp1 hP U t
      (fun h => add_nonneg (mul_nonneg (by norm_num)
        (Finset.sum_nonneg (fun i _ => hp0 i))) hL)
      (fun h _ => ⟨by dsimp [t]; linarith,
        by
          have hs : 0 ≤ ∑ i ∈ U h, p i := Finset.sum_nonneg (fun i _ => hp0 i)
          calc
            4 * (Fintype.card (ι × ι) : ℝ) = 4 * (Fintype.card ι : ℝ) ^ 2 := by
              simp [Fintype.card_prod, pow_two]
            _ ≤ Real.exp (L / 2) := hcount
            _ ≤ Real.exp (t h / 2) := Real.exp_le_exp.mpr (by dsimp [t]; linarith)⟩)
  refine ⟨T, hT, ?_⟩
  intro a b
  let F := T.filter (fun i => a ≤ x i ∧ x i ≤ b)
  by_cases hF : F.Nonempty
  · obtain ⟨i, hi, hmin⟩ := F.exists_min_image x hF
    obtain ⟨j, hj, hmax⟩ := F.exists_max_image x hF
    have hiab := (Finset.mem_filter.mp hi).2
    have hjab := (Finset.mem_filter.mp hj).2
    have hEq : F = T ∩ U (e (i, j)) := by
      ext k
      simp only [F, Finset.mem_filter, Finset.mem_inter, U, Equiv.symm_apply_apply,
        Finset.mem_univ, true_and]
      constructor
      · intro hk
        have hkF : k ∈ F := Finset.mem_filter.mpr hk
        exact ⟨hk.1, hmin k hkF, hmax k hkF⟩
      · rintro ⟨hk, hik, hkj⟩
        exact ⟨hk, hiab.1.trans hik, hkj.trans hjab.2⟩
    have hsub : U (e (i, j)) ⊆
        Finset.univ.filter (fun k => a ≤ x k ∧ x k ≤ b) := by
      intro k hk
      simp only [U, Equiv.symm_apply_apply, Finset.mem_filter,
        Finset.mem_univ, true_and] at hk ⊢
      exact ⟨hiab.1.trans hk.1, hk.2.trans hjab.2⟩
    calc
      (F.card : ℝ) = ((T ∩ U (e (i, j))).card : ℝ) := by rw [hEq]
      _ ≤ t (e (i, j)) := htests _
      _ ≤ 4 * ∑ k ∈ Finset.univ.filter (fun k => a ≤ x k ∧ x k ≤ b), p k + L := by
        dsimp [t]
        exact add_le_add (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => hp0 k))
          (show (0 : ℝ) ≤ 4 by norm_num)) le_rfl
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card : ℝ) ≤ _
    rw [he, Finset.card_empty, Nat.cast_zero]
    exact add_nonneg (mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun i _ => hp0 i))) hL

end Submission.Obl.k4_oss_bad_direction_extraction
