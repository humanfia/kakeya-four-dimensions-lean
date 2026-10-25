import Mathlib

/-!
# Graph-chart localization for `k4_lower_of_discrete`

From a set `K ⊆ ℝ⁴` with a unit segment in every direction we extract the graph form that the
discrete estimate DK4 speaks about (paper Theorem 2.17, "A finite selection from outer
measure"): a set `S` of slopes `u ∈ ℝ³`, `‖u‖ ≤ 1/2`, of positive outer Lebesgue measure, base
points `x u` with `x u 0 = 0` and `‖x u‖ ≤ 2`, and one fixed translation `w`, such that the whole
graph segment `x u + t • (1, u)`, `t ∈ [0, 1]`, lies in the image of `K` under `y ↦ 2 • y - w`.

The dilation by `2` makes the time projection of every such segment longer than `3/2`; a time
window `[α, α + 1]` with `α ∈ ½ℤ` and an integer intercept box are then chosen for each slope, and
the countably many choices are pigeonholed by outer subadditivity. No measurability of `K`, of
`S` or of the witness map is used.
-/

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace Submission.Obl.k4_lower_of_discrete

/-- Points of `ℝ⁴`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- Slopes in `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The graph direction `(1, u)` of a slope `u`. -/
noncomputable def slopeVec (u : E3) : E4 := !₂[1, u 0, u 1, u 2]

@[simp] theorem slopeVec_apply_zero (u : E3) : slopeVec u 0 = 1 := by simp [slopeVec]

theorem norm_sq_slopeVec (u : E3) : ‖slopeVec u‖ ^ 2 = 1 + ‖u‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [slopeVec, Fin.sum_univ_succ]

theorem norm_slopeVec_sub (u u' : E3) : ‖slopeVec u - slopeVec u'‖ = ‖u - u'‖ := by
  have h : ‖slopeVec u - slopeVec u'‖ ^ 2 = ‖u - u'‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [slopeVec, Fin.sum_univ_succ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem one_le_norm_slopeVec (u : E3) : 1 ≤ ‖slopeVec u‖ := by
  have h := norm_sq_slopeVec u
  nlinarith [norm_nonneg (slopeVec u), sq_nonneg ‖u‖]

theorem norm_slopeVec_le {u : E3} (hu : ‖u‖ ≤ 1 / 2) : ‖slopeVec u‖ ≤ 4 / 3 := by
  have h := norm_sq_slopeVec u
  nlinarith [norm_nonneg (slopeVec u), norm_nonneg u]

/-- The unit direction of the slope `u`. -/
theorem norm_inv_smul_slopeVec (u : E3) : ‖‖slopeVec u‖⁻¹ • slopeVec u‖ = 1 := by
  have h : ‖slopeVec u‖ ≠ 0 := by linarith [one_le_norm_slopeVec u]
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]

/-- **Graph-chart localization.** A set with a unit segment in every direction contains, after
the affine map `y ↦ 2 • y - w` for one fixed `w`, a full graph segment `x u + t • (1, u)`,
`t ∈ [0, 1]`, for every slope `u` of a set `S` of positive outer measure in the ball of radius
`1/2`, with `x u 0 = 0` and `‖x u‖ ≤ 2`. -/
theorem exists_graph_localization {K : Set E4}
    (hK : ∀ e ∈ sphere (0 : E4) 1, ∃ a : E4, segment ℝ a (a + e) ⊆ K) :
    ∃ (S : Set E3) (x : E3 → E4) (w : E4),
      S ⊆ closedBall (0 : E3) (1 / 2) ∧ volume S ≠ 0 ∧
      ∀ u ∈ S, x u 0 = 0 ∧ ‖x u‖ ≤ 2 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, x u + t • slopeVec u ∈ (fun y : E4 => (2 : ℝ) • y - w) '' K := by
  classical
  have hdir : ∀ u : E3, ‖slopeVec u‖⁻¹ • slopeVec u ∈ sphere (0 : E4) 1 := fun u => by
    rw [mem_sphere_zero_iff_norm]
    exact norm_inv_smul_slopeVec u
  choose a ha using fun u => hK _ (hdir u)
  -- the time window `[α, α + 1]` with `α = m₀ / 2` and the integer intercept box
  let m0 : E3 → ℤ := fun u => ⌈2 * (2 * a u 0)⌉
  let β : E3 → ℝ := fun u => (m0 u : ℝ) / 2 - 2 * a u 0
  let B : E3 → E4 := fun u => (2 : ℝ) • a u + β u • slopeVec u
  let ι : E3 → (Fin 4 → ℤ) := fun u => ![m0 u, ⌊B u 1⌋, ⌊B u 2⌋, ⌊B u 3⌋]
  let wOf : (Fin 4 → ℤ) → E4 := fun j => !₂[(j 0 : ℝ) / 2, j 1, j 2, j 3]
  let x : E3 → E4 := fun u => B u - wOf (ι u)
  -- outer subadditivity over the countably many choices
  let T : (Fin 4 → ℤ) → Set E3 := fun j => {u | u ∈ closedBall (0 : E3) (1 / 2) ∧ ι u = j}
  have hcover : closedBall (0 : E3) (1 / 2) ⊆ ⋃ j, T j := fun u hu =>
    mem_iUnion.mpr ⟨ι u, hu, rfl⟩
  have hpos : volume (closedBall (0 : E3) (1 / 2)) ≠ 0 := by
    rw [EuclideanSpace.volume_closedBall_fin_three]
    apply mul_ne_zero
    · exact pow_ne_zero _ (by simp)
    · simp [Real.pi_pos]
  obtain ⟨j, hj⟩ : ∃ j, volume (T j) ≠ 0 := by
    by_contra! H
    have hle := (measure_mono (μ := volume) hcover).trans (measure_iUnion_le T)
    simp only [H, tsum_zero, nonpos_iff_eq_zero] at hle
    exact hpos hle
  refine ⟨T j, x, wOf j, fun u hu => hu.1, hj, ?_⟩
  rintro u ⟨hu, rfl⟩
  have hu' : ‖u‖ ≤ 1 / 2 := by simpa [mem_closedBall, dist_zero_right] using hu
  have hβ0 : 0 ≤ β u := by
    have := Int.le_ceil (2 * (2 * a u 0))
    simp only [β, m0]
    linarith
  have hβ1 : β u < 1 / 2 := by
    have := Int.ceil_lt_add_one (2 * (2 * a u 0))
    simp only [β, m0]
    linarith
  have hfrac : ∀ y : ℝ, 0 ≤ y - ⌊y⌋ ∧ y - ⌊y⌋ < 1 := fun y =>
    ⟨sub_nonneg.mpr (Int.floor_le y), by linarith [Int.lt_floor_add_one y]⟩
  have hx0 : x u 0 = 0 := by
    simp [x, B, wOf, ι, β, m0]
  have hx1 : x u 1 = B u 1 - ⌊B u 1⌋ := by simp [x, wOf, ι]
  have hx2 : x u 2 = B u 2 - ⌊B u 2⌋ := by simp [x, wOf, ι]
  have hx3 : x u 3 = B u 3 - ⌊B u 3⌋ := by simp [x, wOf, ι]
  refine ⟨hx0, ?_, ?_⟩
  · have hsq : ‖x u‖ ^ 2 = x u 0 ^ 2 + x u 1 ^ 2 + x u 2 ^ 2 + x u 3 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ]
      ring
    rw [hx0, hx1, hx2, hx3] at hsq
    obtain ⟨h1, h1'⟩ := hfrac (B u 1)
    obtain ⟨h2, h2'⟩ := hfrac (B u 2)
    obtain ⟨h3, h3'⟩ := hfrac (B u 3)
    nlinarith [norm_nonneg (x u)]
  · intro t ht
    set N := ‖slopeVec u‖ with hN
    have hN1 : 1 ≤ N := one_le_norm_slopeVec u
    have hN2 : N ≤ 4 / 3 := norm_slopeVec_le hu'
    have hNne : N ≠ 0 := by linarith
    set τ : ℝ := (β u + t) * N / 2 with hτ
    have hτ0 : 0 ≤ τ := by
      have := ht.1
      positivity
    have hτ1 : τ ≤ 1 := by
      have h1 : β u + t ≤ 3 / 2 := by linarith [ht.2]
      have h2 : (β u + t) * N ≤ 3 / 2 * (4 / 3) := by
        apply mul_le_mul h1 hN2 (by linarith) (by norm_num)
      simp only [hτ]
      linarith
    refine ⟨a u + τ • (N⁻¹ • slopeVec u), ha u ?_, ?_⟩
    · rw [segment_eq_image']
      exact ⟨τ, ⟨hτ0, hτ1⟩, by simp only [add_sub_cancel_left]; rfl⟩
    · have hcoef : (2 : ℝ) * τ * N⁻¹ = β u + t := by
        simp only [hτ]
        field_simp
      simp only [x, B]
      rw [smul_add, smul_smul, smul_smul, hcoef, add_smul]
      abel

end Submission.Obl.k4_lower_of_discrete
