import Mathlib

/-!
# Geometry of admissible slices for `k4_directional_jet_path_transfer`

With `r = (8A)⁻¹` and `A ≥ 2`, every affine complex slice `t ↦ p + t • (p' + w - p)` from a
vertex `p` towards a point within `2r` of the next vertex `p'` maps the complex `r`-thickening
of the real unit segment into the `A⁻¹`-thickening of any set containing the segment `[p, p']`.
-/

namespace Submission.Obl.k4_directional_jet_path_transfer

open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A point of the complex `r`-thickening of the real unit segment is within `r` of a real
parameter in `[0, 1]`. -/
lemma exists_real_of_mem_thickening_unit {r : ℝ} {t : ℂ}
    (ht : t ∈ thickening r (segment ℝ (0 : ℂ) 1)) :
    ∃ σ : ℝ, 0 ≤ σ ∧ σ ≤ 1 ∧ ‖t - (σ : ℂ)‖ < r := by
  rw [mem_thickening_iff] at ht
  obtain ⟨z, hz, hdist⟩ := ht
  rw [segment_eq_image'] at hz
  obtain ⟨σ, ⟨h0, h1⟩, rfl⟩ := hz
  refine ⟨σ, h0, h1, ?_⟩
  simpa [dist_eq_norm, Complex.real_smul] using hdist

omit [NormedSpace ℂ E] in
/-- A closed ball of radius less than `ε` around a point of `S` lies in the `ε`-thickening. -/
lemma closedBall_subset_thickening_of_mem {S : Set E} {x : E} (hx : x ∈ S) {R ε : ℝ}
    (h : R < ε) : closedBall x R ⊆ thickening ε S :=
  (closedBall_subset_ball h).trans (ball_subset_thickening hx ε)

/-- **Admissible slices.** For `A ≥ 2`, `r = (8A)⁻¹`, vertices of norm at most one, and a
perturbation `‖w‖ ≤ 2r` of the target vertex, the slice from `p` towards `p' + w` maps the
complex `r`-thickening of `[0, 1]` into the `A⁻¹`-thickening of `S ⊇ [p, p']`. -/
lemma slice_mem_thickening {S : Set E} {p p' w : E} (hS : segment ℝ p p' ⊆ S)
    (hp : ‖p‖ ≤ 1) (hp' : ‖p'‖ ≤ 1) {A : ℝ} (hA : 2 ≤ A) (hw : ‖w‖ ≤ 2 * (8 * A)⁻¹) :
    ∀ t ∈ thickening ((8 * A)⁻¹) (segment ℝ (0 : ℂ) 1),
      p + t • (p' + w - p) ∈ thickening A⁻¹ S := by
  intro t ht
  obtain ⟨σ, h0, h1, hσ⟩ := exists_real_of_mem_thickening_unit ht
  rw [mem_thickening_iff]
  refine ⟨p + σ • (p' - p), ?_, ?_⟩
  · apply hS
    rw [segment_eq_image']
    exact ⟨σ, ⟨h0, h1⟩, rfl⟩
  · set r : ℝ := (8 * A)⁻¹ with hr
    have hA0 : 0 < A := by linarith
    have hr0 : 0 < r := by positivity
    have hr16 : r ≤ 1 / 16 := by
      rw [hr, inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hAr : A⁻¹ = 8 * r := by
      rw [hr, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (8 : ℝ) ≠ 0), one_mul]
    have key : p + t • (p' + w - p) - (p + σ • (p' - p)) =
        (t - (σ : ℂ)) • (p' - p) + t • w := by
      rw [← Complex.coe_smul, sub_smul, smul_sub, smul_add, smul_sub, smul_sub]
      abel
    have hpp : ‖p' - p‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
    have ht1 : ‖t‖ ≤ 1 + ‖t - (σ : ℂ)‖ := by
      calc ‖t‖ = ‖(σ : ℂ) + (t - σ)‖ := by rw [add_sub_cancel]
        _ ≤ ‖(σ : ℂ)‖ + ‖t - σ‖ := norm_add_le _ _
        _ ≤ 1 + ‖t - σ‖ := by
          gcongr
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
          exact h1
    rw [dist_eq_norm, key, hAr]
    set d := ‖t - (σ : ℂ)‖
    have hd0 : 0 ≤ d := norm_nonneg _
    calc ‖(t - (σ : ℂ)) • (p' - p) + t • w‖
        ≤ ‖(t - (σ : ℂ)) • (p' - p)‖ + ‖t • w‖ := norm_add_le _ _
      _ = d * ‖p' - p‖ + ‖t‖ * ‖w‖ := by rw [norm_smul, norm_smul]
      _ ≤ d * 2 + (1 + d) * (2 * r) := by
          gcongr
      _ < 8 * r := by nlinarith

end Submission.Obl.k4_directional_jet_path_transfer
