import Mathlib

namespace Submission.Obl.k4_algebraic_sheet_bound

open Set Metric

/-- A circle and a radius from the origin can avoid any finite set not containing the origin. -/
theorem exists_compact_connected_circle_avoiding {F : Set ℂ}
    (hF : F.Finite) (h0 : (0 : ℂ) ∉ F) :
    ∃ (r : ℝ) (K : Set ℂ), 1 < r ∧ r < 2 ∧ IsCompact K ∧ IsPreconnected K ∧
      (0 : ℂ) ∈ K ∧ sphere (0 : ℂ) r ⊆ K ∧ K ⊆ ball 0 2 ∧ Disjoint K F := by
  obtain ⟨r, hr, hrF⟩ :=
    ((Set.Ioo_infinite (show (1 : ℝ) < 2 by norm_num)).sdiff (hF.image norm)).nonempty
  obtain ⟨b, _, hb⟩ :=
    ((Set.infinite_univ (α := ℝ)).sdiff (hF.image (fun z : ℂ => z.im / z.re))).nonempty
  let v : ℂ := 1 + (b : ℂ) * Complex.I
  have hv : v ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [v] at this
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let g : ℝ → ℂ := fun s => ((s / ‖v‖ : ℝ) : ℂ) * v
  have hg : Continuous g := by fun_prop
  have hgnorm (s : ℝ) (hs : 0 ≤ s) : ‖g s‖ = s := by
    simp only [g, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hs hvnorm.le)]
    exact div_mul_cancel₀ s hvnorm.ne'
  have hcircle : Disjoint (sphere (0 : ℂ) r) F := by
    refine Set.disjoint_left.mpr ?_
    intro z hz hzF
    apply hrF
    refine ⟨z, hzF, ?_⟩
    simpa only [mem_sphere, dist_zero_right] using hz
  have hradial : Disjoint (g '' Icc 0 r) F := by
    refine Set.disjoint_left.mpr ?_
    rintro z ⟨s, hs, rfl⟩ hz
    apply hb
    refine ⟨g s, hz, ?_⟩
    have hsne : s ≠ 0 := by
      intro hs0
      subst s
      exact h0 (by simpa [g] using hz)
    have hcne : s / ‖v‖ ≠ 0 := div_ne_zero hsne hvnorm.ne'
    simp only [g, v, Complex.mul_re, Complex.add_re, Complex.one_re,
      Complex.mul_im, Complex.add_im, Complex.one_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      add_zero, zero_add, mul_one, sub_zero]
    exact mul_div_cancel_left₀ b hcne
  refine ⟨r, (g '' Icc 0 r) ∪ sphere 0 r, hr.1, hr.2,
    (isCompact_Icc.image hg).union (isCompact_sphere 0 r), ?_, ?_, subset_union_right, ?_,
    hradial.union_left hcircle⟩
  · apply IsPreconnected.union (g r)
    · exact mem_image_of_mem g ⟨by linarith [hr.1], le_rfl⟩
    · simp only [mem_sphere, dist_zero_right, hgnorm r (by linarith [hr.1])]
    · exact isPreconnected_Icc.image g hg.continuousOn
    · exact isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 r
  · exact Or.inl ⟨0, ⟨le_rfl, by linarith [hr.1]⟩, by simp [g]⟩
  · intro z hz
    rcases hz with ⟨s, hs, rfl⟩ | hz
    · simpa only [mem_ball, dist_zero_right, hgnorm s hs.1] using hs.2.trans_lt hr.2
    · exact lt_of_eq_of_lt (by simpa only [mem_sphere, dist_zero_right] using hz) hr.2

end Submission.Obl.k4_algebraic_sheet_bound
