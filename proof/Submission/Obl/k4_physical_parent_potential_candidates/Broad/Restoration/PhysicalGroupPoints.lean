-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Restoration/PhysicalGroupPoints.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
-- Adapted from this LOT tree, o267, branch x0945, commit 7135e2fbe574;
-- source Submission/Obl/k4_original_potential_reference_completion/PhysicalGroupPoints.lean (session x0945).
-- Existing source attributions are preserved below.

import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.SampledPackaging
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.GroupWitness
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.ZoomDiscriminant
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Restoration.ZoomLocalization

/-!
# Group points in physical coordinates

The group conditions of the exits do not depend on the normalization: the group equation
`R0 - Pot`, the hidden derivatives (in units of the hidden scale `B' = B⁻¹`) and the
certificate's test `Rc` take the same values at a physical point and at its normalized image.
`PhysicalGroupPoint` states them physically; any normalization with an explicit inverse turns
it into a `CertifiedNativeGroupPoint` (frozen coordinates) or a `CertifiedGroupPoint`
(normalized coordinates) as soon as the normalized point lies in the required ball.

The zoomed normalization `z = λ (c₁ + M₁ x - c)` of a cube normalization `c₁ + M₁ x` is the
normalization `(λ (c₁ - c), λ M₁)`; its base point is the zoom of the cube base point.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

open Metric Set MeasureTheory MvPolynomial

/-- A physical point of a group: group equation within `εfit`, hidden derivative of `R0` with
sign `σ` and size in `[A₁⁻¹, A₁]`, the certificate test's hidden derivative in the same window
and its value at most `Vc`. Hidden derivatives are measured in units of `B' = B⁻¹`. -/
def PhysicalGroupPoint (B' : ℝ) (R0 Rc : Poly) (Pot : MvPolynomial (Fin 3) ℝ)
    (εfit A₁ σ Vc : ℝ) (x : Fin 4 → ℝ) : Prop :=
  |eval x R0 - eval (fun i : Fin 3 => x i.castSucc) Pot| ≤ εfit ∧
  0 < B' * eval x (pderiv 3 R0) * σ ∧
  A₁⁻¹ ≤ |B' * eval x (pderiv 3 R0)| ∧ |B' * eval x (pderiv 3 R0)| ≤ A₁ ∧
  A₁⁻¹ ≤ |B' * eval x (pderiv 3 Rc)| ∧ |B' * eval x (pderiv 3 Rc)| ≤ A₁ ∧
  |eval x Rc| ≤ Vc

/-- A physical group point whose normalized base point lies in the unit ball is a certified
native group point of the transported polynomials. -/
theorem certifiedNativeGroupPoint_of_physical {c c' : Fin 3 → ℝ}
    {M M' : Matrix (Fin 3) (Fin 3) ℝ} {B B' : ℝ} (hM : M' * M = 1)
    (hc : ∀ k, c' k = -∑ j : Fin 3, M' k j * c j) (hB : B' * B = 1)
    {R0 Rc : Poly} {Pot : MvPolynomial (Fin 3) ℝ} {εfit A₁ σ Vc : ℝ} {x : Fin 4 → ℝ}
    (hx : PhysicalGroupPoint B' R0 Rc Pot εfit A₁ σ Vc x)
    (hball : (pointOfCoordinates (coordinateMap c M B x)).1 ∈ closedBall (0 : Base) 1) :
    CertifiedNativeGroupPoint c M B (transportPolynomial c' M' B' R0) (basePullback c' M' Pot)
      (transportPolynomial c' M' B' Rc) εfit A₁ σ x := by
  obtain ⟨hfit, hsign, hlo, hhi, hclo, hchi, -⟩ := hx
  obtain ⟨hR, hRd⟩ := eval_normalized_native hM hc hB R0 x
  obtain ⟨-, hRcd⟩ := eval_normalized_native hM hc hB Rc x
  have hP := eval_normalized_potential hM hc hB Pot x
  refine ⟨⟨hball, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hR, hP]; exact hfit
  · rw [hRd]; exact hsign
  · rw [hRd]; exact hlo
  · rw [hRd]; exact hhi
  · rw [hRcd]; exact hclo
  · rw [hRcd]; exact hchi

/-- A physical group point whose normalized base point lies in the ball of radius `4` is a
certified group point of the transported polynomials at its normalized point. -/
theorem certifiedGroupPoint_of_physical {c c' : Fin 3 → ℝ}
    {M M' : Matrix (Fin 3) (Fin 3) ℝ} {B B' : ℝ} (hM : M' * M = 1)
    (hc : ∀ k, c' k = -∑ j : Fin 3, M' k j * c j) (hB : B' * B = 1)
    {R0 Rc : Poly} {Pot : MvPolynomial (Fin 3) ℝ} {εfit A₁ σ Vc : ℝ} {x : Fin 4 → ℝ}
    (hx : PhysicalGroupPoint B' R0 Rc Pot εfit A₁ σ Vc x)
    (hball : (pointOfCoordinates (coordinateMap c M B x)).1 ∈ ball (0 : Base) 4) :
    CertifiedGroupPoint (transportPolynomial c' M' B' R0) (basePullback c' M' Pot)
      (transportPolynomial c' M' B' Rc) εfit A₁ σ Vc
      (pointOfCoordinates (coordinateMap c M B x)).1
      (pointOfCoordinates (coordinateMap c M B x)).2 := by
  obtain ⟨hfit, hsign, hlo, hhi, hclo, hchi, hval⟩ := hx
  obtain ⟨hR, hRd⟩ := eval_normalized_native hM hc hB R0 x
  obtain ⟨hRc, hRcd⟩ := eval_normalized_native hM hc hB Rc x
  have hP := eval_normalized_potential hM hc hB Pot x
  have hco := coordinates_pointOfCoordinates (coordinateMap c M B x)
  have hbase : (fun i : Fin 3 => (pointOfCoordinates (coordinateMap c M B x)).1 i) =
      fun i : Fin 3 => coordinateMap c M B x i.castSucc := rfl
  refine ⟨⟨hball, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hco, hbase, hR, hP]; exact hfit
  · rw [hco, hRd]; exact hsign
  · rw [hco, hRd]; exact hlo
  · rw [hco, hRd]; exact hhi
  · rw [hco, hRcd]; exact hclo
  · rw [hco, hRcd]; exact hchi
  · rw [hco, hRc]; exact hval

/-- The forward zoomed normalization `x ↦ λ (c₁ + M₁ x - c)` as a normalization. -/
def zoomForwardShift (c₁ c : Fin 3 → ℝ) (lam : ℝ) : Fin 3 → ℝ := fun i => lam * (c₁ i - c i)

lemma coordinateMap_zoomForward (c₁ c : Fin 3 → ℝ) (M₁ : Matrix (Fin 3) (Fin 3) ℝ)
    (B lam : ℝ) (x : Fin 4 → ℝ) :
    (pointOfCoordinates (coordinateMap (zoomForwardShift c₁ c lam) (lam • M₁) B x)).1 =
      zoomMap (WithLp.toLp 2 c) lam (pointOfCoordinates (coordinateMap c₁ M₁ B x)).1 ∧
    (pointOfCoordinates (coordinateMap (zoomForwardShift c₁ c lam) (lam • M₁) B x)).2 =
      (pointOfCoordinates (coordinateMap c₁ M₁ B x)).2 := by
  refine ⟨?_, rfl⟩
  ext i
  simp only [pointOfCoordinates, zoomMap, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  rw [coordinateMap_castSucc, coordinateMap_castSucc]
  simp only [zoomForwardShift, Matrix.smul_apply, smul_eq_mul]
  have hsum : lam * (c₁ i + ∑ l : Fin 3, M₁ i l * x l.castSucc - c i) =
      lam * (c₁ i - c i) + ∑ l : Fin 3, lam * (M₁ i l * x l.castSucc) := by
    rw [← Finset.mul_sum]; ring
  rw [hsum]
  simp only [mul_assoc]

/-- The inverse of the zoomed normalization, in the form the exits use. -/
theorem zoomForward_inverse {c₁ c₁' : Fin 3 → ℝ} {M₁ M₁' : Matrix (Fin 3) (Fin 3) ℝ}
    (hM : M₁' * M₁ = 1) (hc : ∀ k, c₁' k = -∑ i : Fin 3, M₁' k i * c₁ i)
    (c : Fin 3 → ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    zoomMatrix M₁' lam * (lam • M₁) = 1 ∧
    ∀ k, zoomShift c₁' M₁' c k =
      -∑ i : Fin 3, zoomMatrix M₁' lam k i * zoomForwardShift c₁ c lam i := by
  obtain ⟨h1, h2⟩ := zoom_inverse hM hc c hlam
  exact ⟨h1, fun k => by rw [h2 k]; rfl⟩

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
