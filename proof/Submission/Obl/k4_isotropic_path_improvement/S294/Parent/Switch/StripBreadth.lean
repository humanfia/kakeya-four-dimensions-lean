-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Switch.StripBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Switch/StripBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Velocity-strip breadth gives breadth of the lifted base
directions `(1, V)` away from every proper subspace of `ℝ³`: a proper
subspace lies in the kernel of a unit covector `n`, and
`|⟪n, (1, V)⟫| < r` is a planar velocity strip of half-width at most
`2 (U + 1) r` when `n` has a substantial planar part, and is empty for
bounded velocities otherwise.
-/
import Mathlib

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch

open Set MeasureTheory
open scoped RealInnerProductSpace

/-- The lifted direction `(1, V)` of a planar velocity. -/
noncomputable def liftDir (V : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![1, V 0, V 1]

theorem exists_unit_normal_of_finrank_lt (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hW : Module.finrank ℝ W < 3) :
    ∃ n : EuclideanSpace ℝ (Fin 3), ‖n‖ = 1 ∧ ∀ y ∈ W, ⟪n, y⟫ = 0 := by
  have hne : W ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, finrank_euclideanSpace, Fintype.card_fin] at hW
    exact lt_irrefl _ hW
  have hperp : Wᗮ ≠ ⊥ := by
    intro hbot
    exact hne (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hperp
  refine ⟨‖b‖⁻¹ • b, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hb0)]
  · intro y hy
    rw [inner_smul_left, Submodule.inner_left_of_mem_orthogonal hy hb, mul_zero]

theorem abs_inner_le_infDist (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (n x : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1) (hW : ∀ y ∈ W, ⟪n, y⟫ = 0) :
    |⟪n, x⟫| ≤ Metric.infDist x (W : Set _) := by
  rw [Metric.le_infDist ⟨0, W.zero_mem⟩]
  intro y hy
  have h : ⟪n, x⟫ = ⟪n, x - y⟫ := by
    rw [inner_sub_right, hW y hy, sub_zero]
  rw [h, dist_eq_norm]
  calc |⟪n, x - y⟫| ≤ ‖n‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
    _ = ‖x - y‖ := by rw [hn, one_mul]

theorem inner_liftDir (n : EuclideanSpace ℝ (Fin 3)) (V : EuclideanSpace ℝ (Fin 2)) :
    ⟪n, liftDir V⟫ = n 0 + (n 1 * V 0 + n 2 * V 1) := by
  simp [liftDir, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]
  ring

theorem norm_sq_three (n : EuclideanSpace ℝ (Fin 3)) :
    ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [sq_abs]

theorem norm_sq_two (n : EuclideanSpace ℝ (Fin 2)) : ‖n‖ ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [sq_abs]

/-- A thin neighborhood of a proper subspace, met by lifted bounded
velocities, lies in a planar velocity strip. -/
theorem lift_near_subspace_subset_strip (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hW : Module.finrank ℝ W < 3) (U w r : ℝ) (hU : 0 ≤ U) (hr0 : 0 ≤ r)
    (hrw : 2 * (U + 1) * r ≤ w) (hr : r ≤ 1 / 4) :
    ∃ (m : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖m‖ = 1 ∧
      ∀ V : EuclideanSpace ℝ (Fin 2), ‖V‖ ≤ U →
        Metric.infDist (liftDir V) (W : Set _) < r → |⟪m, V⟫ - t| ≤ w := by
  obtain ⟨n, hn, hnW⟩ := exists_unit_normal_of_finrank_lt W hW
  let n' : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![n 1, n 2]
  have hn' : ‖n'‖ ^ 2 = n 1 ^ 2 + n 2 ^ 2 := by
    rw [norm_sq_two]; simp [n']
  have hn3 : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by rw [← norm_sq_three, hn, one_pow]
  have hinner (V : EuclideanSpace ℝ (Fin 2)) : ⟪n, liftDir V⟫ = n 0 + ⟪n', V⟫ := by
    rw [inner_liftDir]
    congr 1
    simp [n', PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  set σ : ℝ := 1 / (2 * (U + 1)) with hσ
  have hσpos : 0 < σ := by positivity
  by_cases hs : σ ≤ ‖n'‖
  · have hspos : 0 < ‖n'‖ := lt_of_lt_of_le hσpos hs
    refine ⟨‖n'‖⁻¹ • n', -(n 0) / ‖n'‖, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hspos.ne']
    · intro V _ hV
      have h1 : |⟪n, liftDir V⟫| < r :=
        lt_of_le_of_lt (abs_inner_le_infDist W n _ hn hnW) hV
      rw [hinner] at h1
      have h2 : ⟪‖n'‖⁻¹ • n', V⟫ - -n 0 / ‖n'‖ = (n 0 + ⟪n', V⟫) / ‖n'‖ := by
        rw [inner_smul_left]
        simp only [conj_trivial]
        field_simp
        ring
      rw [h2, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
      have h3 : r ≤ w * σ := by
        rw [hσ]
        rw [mul_one_div, le_div_iff₀ (by positivity)]
        linarith
      nlinarith
  · refine ⟨WithLp.toLp 2 ![1, 0], 0, ?_, ?_⟩
    · have : ‖(WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 := by
        rw [norm_sq_two]; simp
      have hnn := norm_nonneg (WithLp.toLp 2 ![(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2))
      nlinarith
    · intro V hV hdist
      exfalso
      have hlt : ‖n'‖ < σ := lt_of_not_ge hs
      have hσhalf : σ ≤ 1 / 2 := by
        rw [hσ, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have hn'sq : ‖n'‖ ^ 2 < 1 / 4 := by
        have h0 := norm_nonneg n'
        nlinarith
      have hn0 : (3 : ℝ) / 4 < n 0 ^ 2 := by nlinarith
      have habs0 : (17 : ℝ) / 20 < |n 0| := by
        have h1 := sq_abs (n 0)
        have h2 := abs_nonneg (n 0)
        nlinarith
      have hσU : σ * U ≤ 1 / 2 := by
        rw [hσ, one_div, inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have hx : |⟪n', V⟫| ≤ 1 / 2 := by
        calc |⟪n', V⟫| ≤ ‖n'‖ * ‖V‖ := abs_real_inner_le_norm _ _
          _ ≤ σ * U := mul_le_mul hlt.le hV (norm_nonneg _) hσpos.le
          _ ≤ 1 / 2 := hσU
      have h1 : |⟪n, liftDir V⟫| < r :=
        lt_of_le_of_lt (abs_inner_le_infDist W n _ hn hnW) hdist
      rw [hinner] at h1
      have h2 : |n 0| - |⟪n', V⟫| ≤ |n 0 + ⟪n', V⟫| := by
        have := abs_sub_abs_le_abs_sub (n 0) (-⟪n', V⟫)
        simpa only [abs_neg, sub_neg_eq_add] using this
      linarith

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch

open Set MeasureTheory
open scoped RealInnerProductSpace ENNReal

/-- Per-state velocity-strip breadth gives per-state breadth of the lifted
directions away from every proper subspace of `ℝ³`. -/
theorem state_subspace_ratio_of_strip_ratio {X Q : Type*} [MeasurableSpace X]
    (μ : Measure X) (st : X → Q) (V : X → EuclideanSpace ℝ (Fin 2)) (U w r : ℝ) (p : ENNReal)
    (hV : ∀ x, ‖V x‖ ≤ U) (hU : 0 ≤ U) (hr0 : 0 ≤ r) (hrw : 2 * (U + 1) * r ≤ w)
    (hr : r ≤ 1 / 4)
    (hstrip : ∀ q (m : EuclideanSpace ℝ (Fin 2)) (t : ℝ), ‖m‖ = 1 →
      μ (st ⁻¹' {q} ∩ {x | |⟪m, V x⟫ - t| ≤ w}) ≤ p * μ (st ⁻¹' {q})) :
    ∀ q (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ W < 3 →
      μ (st ⁻¹' {q} ∩ {x | Metric.infDist (liftDir (V x)) (W : Set _) < r}) ≤
        p * μ (st ⁻¹' {q}) := by
  intro q W hW
  obtain ⟨m, t, hm, hsub⟩ := lift_near_subspace_subset_strip W hW U w r hU hr0 hrw hr
  refine (measure_mono ?_).trans (hstrip q m t hm)
  intro x hx
  exact ⟨hx.1, hsub (V x) (hV x) hx.2⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch
