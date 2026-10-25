-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/ZoomCoordinates.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/ZoomCoordinates.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.NativeCoordinates
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.BaseTranslation

/-!
# Zoomed coordinates at a group point

A producer normalizes the physical base to block (cube) coordinates `x = c₁ + M₁ x_phys` with
inverse `(c₁', M₁')`. The certificate uses the zoomed coordinates `z = λ (x - c)` around a group
point `c`, whose inverse is `(c₁' + M₁' c, λ⁻¹ M₁')`. In zoomed coordinates the native
coefficients are the cube ones, translated to `c` and dilated by `λ⁻¹`:
`baseDilation λ (nativeB S_z) = baseTranslation c (nativeB S_x)` and the same for `nativeC`,
while `nativeA` does not change.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open MvPolynomial

lemma quadratic_coefficients_eq {A B C A' B' C' : ℝ}
    (h : ∀ w : ℝ, A * w ^ 2 + B * w + C = A' * w ^ 2 + B' * w + C') :
    A = A' ∧ B = B' ∧ C = C' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h (-1)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
    zero_add, one_pow, mul_one, even_two, Even.neg_pow, mul_neg] at h0 h1 h2
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The zoomed inverse normalization. -/
def zoomShift (c₁' : Fin 3 → ℝ) (M₁' : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) :
    Fin 3 → ℝ := fun k => c₁' k + ∑ j : Fin 3, M₁' k j * c j

def zoomMatrix (M₁' : Matrix (Fin 3) (Fin 3) ℝ) (lam : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  lam⁻¹ • M₁'

lemma coordinateMap_zoom (c₁' : Fin 3 → ℝ) (M₁' : Matrix (Fin 3) (Fin 3) ℝ) (B' : ℝ)
    (c : Fin 3 → ℝ) {lam : ℝ} (_hlam : lam ≠ 0) (z : Base) (w : ℝ) :
    coordinateMap (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) B' ![z 0, z 1, z 2, w] =
      coordinateMap c₁' M₁' B'
        ![lam⁻¹ * z 0 + c 0, lam⁻¹ * z 1 + c 1, lam⁻¹ * z 2 + c 2, w] := by
  funext i
  fin_cases i <;>
    simp [coordinateMap, zoomShift, zoomMatrix, Fin.sum_univ_three, Matrix.smul_apply] <;> ring

/-- The zoomed native quadratic is the cube one at the translated, dilated point. -/
lemma eval_zoom_native (c₁' : Fin 3 → ℝ) (M₁' : Matrix (Fin 3) (Fin 3) ℝ) (B' : ℝ)
    (c : Fin 3 → ℝ) {lam : ℝ} (hlam : lam ≠ 0) (R0 : Poly) (z : Base) (w : ℝ) :
    eval ![z 0, z 1, z 2, w] (transportPolynomial (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) B' R0) =
      eval ![lam⁻¹ * z 0 + c 0, lam⁻¹ * z 1 + c 1, lam⁻¹ * z 2 + c 2, w]
        (transportPolynomial c₁' M₁' B' R0) := by
  rw [eval_transportPolynomial, eval_transportPolynomial, coordinateMap_zoom _ _ _ _ hlam]

lemma eval_zoom_potential (c₁' : Fin 3 → ℝ) (M₁' : Matrix (Fin 3) (Fin 3) ℝ)
    (c : Fin 3 → ℝ) {lam : ℝ} (_hlam : lam ≠ 0) (Pot : MvPolynomial (Fin 3) ℝ) (z : Fin 3 → ℝ) :
    eval z (basePullback (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) Pot) =
      eval (fun i => lam⁻¹ * z i + c i) (basePullback c₁' M₁' Pot) := by
  rw [eval_basePullback, eval_basePullback]
  apply congrArg (fun v : Fin 3 → ℝ => eval v Pot)
  funext k
  simp only [zoomShift, zoomMatrix, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- Native coefficients in zoomed coordinates. -/
theorem zoom_native_coefficients (c₁' : Fin 3 → ℝ) (M₁' : Matrix (Fin 3) (Fin 3) ℝ) (B' : ℝ)
    (c : Fin 3 → ℝ) {lam : ℝ} (hlam : lam ≠ 0) (R0 : Poly) (hR0 : R0.totalDegree ≤ 2)
    (Pot : MvPolynomial (Fin 3) ℝ) :
    nativeA (transportPolynomial (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) B' R0) =
        nativeA (transportPolynomial c₁' M₁' B' R0) ∧
    baseDilation lam (nativeB (transportPolynomial (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) B' R0)) =
        baseTranslation c (nativeB (transportPolynomial c₁' M₁' B' R0)) ∧
    baseDilation lam (nativeC (transportPolynomial (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) B' R0)
        (basePullback (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) Pot)) =
        baseTranslation c (nativeC (transportPolynomial c₁' M₁' B' R0) (basePullback c₁' M₁' Pot)) := by
  set Sz := transportPolynomial (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) B' R0
  set Sx := transportPolynomial c₁' M₁' B' R0
  set Pz := basePullback (zoomShift c₁' M₁' c) (zoomMatrix M₁' lam) Pot
  set Px := basePullback c₁' M₁' Pot
  have hSz : Sz.totalDegree ≤ 2 := (totalDegree_transportPolynomial_le _ _ _ _).trans hR0
  have hSx : Sx.totalDegree ≤ 2 := (totalDegree_transportPolynomial_le _ _ _ _).trans hR0
  -- pointwise comparison of the two native expansions
  have hcmp : ∀ (z : Base), nativeA Sz = nativeA Sx ∧
      eval (fun i => z i) (nativeB Sz) =
        eval (fun i => lam⁻¹ * z i + c i) (nativeB Sx) ∧
      eval (fun i => z i) (nativeC Sz Pz) =
        eval (fun i => lam⁻¹ * z i + c i) (nativeC Sx Px) := by
    intro z
    set x : Base := WithLp.toLp 2 (fun i => lam⁻¹ * z i + c i) with hx
    have hall : ∀ w : ℝ, nativeA Sz * w ^ 2 + eval (fun i => z i) (nativeB Sz) * w +
        eval (fun i => z i) (nativeC Sz Pz) =
        nativeA Sx * w ^ 2 + eval (fun i => x i) (nativeB Sx) * w +
        eval (fun i => x i) (nativeC Sx Px) := by
      intro w
      rw [← native_equation Sz hSz Pz z w, ← native_equation Sx hSx Px x w,
        eval_zoom_native _ _ _ _ hlam, eval_zoom_potential _ _ _ hlam]
    obtain ⟨hA, hB, hC⟩ := quadratic_coefficients_eq hall
    exact ⟨hA, hB, hC⟩
  have h0 := hcmp 0
  refine ⟨h0.1, ?_, ?_⟩
  · apply MvPolynomial.funext
    intro y
    rw [eval_baseDilation, eval_baseTranslation]
    have := (hcmp (WithLp.toLp 2 (fun i => lam * y i))).2.1
    rw [this]
    apply congrArg (fun v : Fin 3 → ℝ => eval v (nativeB Sx))
    funext i
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul, add_comm]
  · apply MvPolynomial.funext
    intro y
    rw [eval_baseDilation, eval_baseTranslation]
    have := (hcmp (WithLp.toLp 2 (fun i => lam * y i))).2.2
    rw [this]
    apply congrArg (fun v : Fin 3 → ℝ => eval v (nativeC Sx Px))
    funext i
    rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul, add_comm]

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
