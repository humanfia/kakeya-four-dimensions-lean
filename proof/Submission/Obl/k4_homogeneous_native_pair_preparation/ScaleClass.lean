-- Adapted from this LOT tree, o206, session x0709, commit f7d6ac58,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/PrepClass.lean.
-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/PrepClass.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_homogeneous_native_pair_preparation.ChartAxes
import Submission.Obl.k4_homogeneous_native_pair_preparation.DyadicMagnitude

/-!
# Homogenized scale classes of old charts

Old chart matrices with polynomially bounded entries and inverse entries have long and
narrow scales `r₁, r₂` in a polynomial range, so their dyadic indices lie in a grid of
`O(log N)` values.  Some class of the grid carries at least a `1 / |grid|²` share of
any weighting (`exists_heavy_class`).  In a class, `R₁ ≤ r₁ < 2 R₁`, `R₂ ≤ r₂ < 2 R₂`
and `R₂ ≤ R₁`.
-/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.Construction

open Matrix
open scoped ENNReal

/-- **Pigeonhole over classes.** -/
theorem exists_heavy_class {ι κ : Type*} [Fintype ι] [DecidableEq κ] (w : ι → ℝ≥0∞)
    (cls : ι → κ) (G : Finset κ) (hG : ∀ i, cls i ∈ G) (hne : G.Nonempty) :
    ∃ k ∈ G, ∑ i, w i ≤ (G.card : ℝ≥0∞) * ∑ i ∈ Finset.univ.filter (fun i => cls i = k), w i := by
  classical
  have hsplit : ∑ i, w i = ∑ k ∈ G, ∑ i ∈ Finset.univ.filter (fun i => cls i = k), w i := by
    rw [Finset.sum_fiberwise_of_maps_to (fun i _ => hG i)]
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image G
    (fun k => ∑ i ∈ Finset.univ.filter (fun i => cls i = k), w i) hne
  refine ⟨k, hk, ?_⟩
  rw [hsplit]
  calc ∑ k' ∈ G, ∑ i ∈ Finset.univ.filter (fun i => cls i = k'), w i
      ≤ ∑ _k' ∈ G, ∑ i ∈ Finset.univ.filter (fun i => cls i = k), w i :=
        Finset.sum_le_sum (fun k' hk' => hmax k' hk')
    _ = (G.card : ℝ≥0∞) * ∑ i ∈ Finset.univ.filter (fun i => cls i = k), w i := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The dyadic scale class of a chart matrix. -/
noncomputable def scaleClass (Q : Matrix (Fin 2) (Fin 2) ℝ) : ℤ × ℤ :=
  (magnitudeIndex (r₁ Q), magnitudeIndex (r₂ Q))

theorem r₂_pos {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) : 0 < r₂ Q :=
  div_pos (abs_pos.mpr hQ) (r₁_pos hQ)

/-- The scales of a chart in its class. -/
theorem scaleClass_bounds {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) {i₁ i₂ : ℤ}
    (h : scaleClass Q = (i₁, i₂)) :
    (2 : ℝ) ^ i₁ ≤ r₁ Q ∧ r₁ Q < 2 * (2 : ℝ) ^ i₁ ∧
      (2 : ℝ) ^ i₂ ≤ r₂ Q ∧ r₂ Q < 2 * (2 : ℝ) ^ i₂ := by
  simp only [scaleClass, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have b1 := (magnitudeIndex_eq_iff (r₁_pos hQ) i₁).mp h1
  have b2 := (magnitudeIndex_eq_iff (r₂_pos hQ) i₂).mp h2
  exact ⟨b1.1, b1.2, b2.1, b2.2⟩

/-- In a class, the narrow scale is at most the long scale. -/
theorem class_R₂_le_R₁ {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) {i₁ i₂ : ℤ}
    (h : scaleClass Q = (i₁, i₂)) : (2 : ℝ) ^ i₂ ≤ (2 : ℝ) ^ i₁ := by
  obtain ⟨h1, h1', h2, h2'⟩ := scaleClass_bounds hQ h
  have hr := r₂_le_r₁ hQ
  have hlt : (2 : ℝ) ^ i₂ < 2 * (2 : ℝ) ^ i₁ := by linarith
  have hle : i₂ ≤ i₁ := by
    by_contra hne
    push Not at hne
    have : (2 : ℝ) ^ (i₁ + 1) ≤ (2 : ℝ) ^ i₂ :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one] at this
    linarith
  exact zpow_le_zpow_right₀ (by norm_num) hle

/-- The determinant of a chart matrix with polynomially bounded inverse entries is
polynomially bounded below. -/
theorem abs_det_ge_of_inv_entries {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) {X : ℝ}
    (hX : (∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j|) ≤ X) : 1 / (2 * X ^ 2) ≤ |Q.det| := by
  have hdinv : (Q⁻¹).det = (Q.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hd2 : |(Q⁻¹).det| ≤ 2 * X ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Fin.sum_univ_two] at hX
    have a := abs_nonneg (Q⁻¹ 0 0); have b := abs_nonneg (Q⁻¹ 0 1)
    have c := abs_nonneg (Q⁻¹ 1 0); have d := abs_nonneg (Q⁻¹ 1 1)
    calc |Q⁻¹ 0 0 * Q⁻¹ 1 1 - Q⁻¹ 0 1 * Q⁻¹ 1 0|
        ≤ |Q⁻¹ 0 0| * |Q⁻¹ 1 1| + |Q⁻¹ 0 1| * |Q⁻¹ 1 0| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ X * X + X * X := by
          apply add_le_add <;> apply mul_le_mul <;> linarith
      _ = 2 * X ^ 2 := by ring
  have hpos : 0 < |Q.det| := abs_pos.mpr hQ
  rw [hdinv, abs_inv] at hd2
  have hX0 : 0 < 2 * X ^ 2 := lt_of_lt_of_le (inv_pos.mpr hpos) hd2
  rw [div_le_iff₀ hX0]
  calc 1 = |Q.det|⁻¹ * |Q.det| := by field_simp
    _ ≤ 2 * X ^ 2 * |Q.det| := mul_le_mul_of_nonneg_right hd2 hpos.le
    _ = |Q.det| * (2 * X ^ 2) := by ring

/-- The scales of a chart with polynomially bounded entries and inverse entries. -/
theorem scales_range {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) {X : ℝ} (hX1 : 1 ≤ X)
    (hX : (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) ≤ X) :
    1 / (2 * X ^ 3) ≤ r₂ Q ∧ r₂ Q ≤ r₁ Q ∧ r₁ Q ≤ X := by
  have hsplit : (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) =
      (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) + ∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j| := by
    simp only [Fin.sum_univ_two]; ring
  have hA : (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) ≤ X := by
    have : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j| := by positivity
    linarith
  have hB : (∑ i : Fin 2, ∑ j : Fin 2, |Q⁻¹ i j|) ≤ X := by
    have : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Q i j| := by positivity
    linarith
  have hr1 : r₁ Q ≤ X := (r₁_le_entrySum Q).trans hA
  have hdet := abs_det_ge_of_inv_entries hQ hB
  have hr1pos := r₁_pos hQ
  refine ⟨?_, r₂_le_r₁ hQ, hr1⟩
  unfold r₂
  rw [le_div_iff₀ hr1pos]
  calc 1 / (2 * X ^ 3) * r₁ Q ≤ 1 / (2 * X ^ 3) * X := by gcongr
    _ = 1 / (2 * X ^ 2) := by field_simp
    _ ≤ |Q.det| := hdet

/-- The class of a chart lies in the dyadic grid of exponent `a` once `2 X³ ≤ N^a`. -/
theorem scaleClass_mem_grid {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0) {X N a : ℝ}
    (hX1 : 1 ≤ X) (hN : 0 < N)
    (hX : (∑ i : Fin 2, ∑ j : Fin 2, (|Q i j| + |Q⁻¹ i j|)) ≤ X)
    (hXa : 2 * X ^ 3 ≤ N ^ a) :
    scaleClass Q ∈ magnitudeGrid N a ×ˢ magnitudeGrid N a := by
  obtain ⟨h2, h21, h1⟩ := scales_range hQ hX1 hX
  have hX3 : X ≤ 2 * X ^ 3 := by
    have h1 : 1 ≤ X ^ 2 := one_le_pow₀ hX1
    nlinarith
  have hNa : 0 < N ^ a := Real.rpow_pos_of_pos hN a
  have hlo : N ^ (-a) ≤ 1 / (2 * X ^ 3) := by
    rw [Real.rpow_neg hN.le, one_div]
    exact inv_anti₀ (by positivity) hXa
  have hr2pos := r₂_pos hQ
  have hr1pos := r₁_pos hQ
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · exact magnitudeIndex_mem hN hr1pos (hlo.trans (h2.trans h21)) (h1.trans (hX3.trans hXa))
  · exact magnitudeIndex_mem hN hr2pos (hlo.trans h2) ((h21.trans h1).trans (hX3.trans hXa))

end Submission.Obl.k4_homogeneous_native_pair_preparation.Construction
