/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.PolynomialRemezCoefficients
import Submission.Lib.K4PolynomialNorming.LargeFibers

open Set MeasureTheory

namespace Submission.Lib.K4PolynomialNorming

/-- Two successive one-variable Remez estimates control every coefficient
of a bivariate polynomial from a positive-measure real observation set. -/
theorem bivariate_polynomial_coeff_le_of_small_values
    (p : Polynomial (Polynomial ℂ)) (D : ℕ) (houter : p.natDegree ≤ D)
    (hinner : ∀ i, (p.coeff i).natDegree ≤ D)
    (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hrect : E ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε)
    (hmass : ENNReal.ofReal ℓ ≤ (volume.prod volume) E)
    (hsmall : ∀ x y : ℝ, (x, y) ∈ E →
      ‖(p.map (Polynomial.evalRingHom (x : ℂ))).eval (y : ℂ)‖ ≤ ε) :
    ∀ i j : ℕ, ‖(p.coeff i).coeff j‖ ≤
      (1 + 32 * (D + 1 : ℕ) / ℓ) ^ (2 * D) * ε := by
  classical
  have hvol : volume (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal 2 := by norm_num
  obtain ⟨G, hGm, hGS, hGmass, hfib⟩ := exists_many_large_fibers
    volume volume (Set.Icc (-1 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) E measurableSet_Icc hE hrect
    2 2 ℓ (by norm_num) (by norm_num) hℓ hvol hvol hmass
  have h22 : (2 : ℝ) * 2 = 4 := by norm_num
  have hGmass' : ENNReal.ofReal (ℓ / 4) ≤ volume G := by simpa only [h22] using hGmass
  have hfib' (x : ℝ) (hx : x ∈ G) : ENNReal.ofReal (ℓ / 4) ≤ volume (Prod.mk x ⁻¹' E) := by
    simpa only [h22] using hfib x hx
  let C : ℝ := 1 + 4 * (D + 1 : ℕ) * (1 + (1 : ℝ)) / (ℓ / 4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (i : ℕ) (x : ℝ) (hx : x ∈ G) : ‖(p.coeff i).eval (x : ℂ)‖ ≤ C ^ D * ε := by
    have hdeg : (p.map (Polynomial.evalRingHom (x : ℂ))).natDegree ≤ D :=
      Polynomial.natDegree_map_le.trans houter
    have h := complex_polynomial_coeff_le_of_small_values
      (p.map (Polynomial.evalRingHom (x : ℂ))) D hdeg (Prod.mk x ⁻¹' E)
      (ℓ / 4) 1 ε (by positivity) (by norm_num) hε (hfib' x hx)
      (fun y hy => abs_le.mpr ⟨(hrect hy).2.1, (hrect hy).2.2⟩)
      (fun y hy => hsmall x y hy) i
    simpa only [Polynomial.coeff_map, Polynomial.coe_evalRingHom] using h
  intro i j
  have h := complex_polynomial_coeff_le_of_small_values (p.coeff i) D (hinner i)
    G (ℓ / 4) 1 (C ^ D * ε) (by positivity) (by norm_num) (by positivity) hGmass'
    (fun x hx => abs_le.mpr ⟨(hGS hx).1, (hGS hx).2⟩) (hpoint i) j
  have hCeq : C = 1 + 32 * (D + 1 : ℕ) / ℓ := by
    dsimp [C]
    field_simp
    <;> ring
  calc
    ‖(p.coeff i).coeff j‖ ≤ C ^ D * (C ^ D * ε) := h
    _ = C ^ (D + D) * ε := by rw [pow_add]; ring
    _ = (1 + 32 * (D + 1 : ℕ) / ℓ) ^ (2 * D) * ε := by rw [hCeq, show D + D = 2 * D by omega]

end Submission.Lib.K4PolynomialNorming
