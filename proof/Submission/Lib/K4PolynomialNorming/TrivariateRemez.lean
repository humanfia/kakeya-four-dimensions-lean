/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.BivariateRemez

open Set MeasureTheory

namespace Submission.Lib.K4PolynomialNorming

/-- The three-variable coefficient Remez bound on a unit box. The product
measure is grouped as a planar base and one real fiber. -/
theorem trivariate_polynomial_coeff_le_of_small_values
    (p : Polynomial (Polynomial (Polynomial ℂ))) (D : ℕ) (houter : p.natDegree ≤ D)
    (hmiddle : ∀ i, (p.coeff i).natDegree ≤ D)
    (hinner : ∀ i j, ((p.coeff i).coeff j).natDegree ≤ D)
    (E : Set ((ℝ × ℝ) × ℝ)) (hE : MeasurableSet E)
    (hrect : E ⊆ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ×ˢ Set.Icc (-1 : ℝ) 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε)
    (hmass : ENNReal.ofReal ℓ ≤ ((volume.prod volume).prod volume) E)
    (hsmall : ∀ x y z : ℝ, ((x, y), z) ∈ E →
      ‖(p.map ((Polynomial.evalRingHom (y : ℂ)).comp
        (Polynomial.mapRingHom (Polynomial.evalRingHom (x : ℂ))))).eval (z : ℂ)‖ ≤ ε) :
    ∀ i j k : ℕ, ‖((p.coeff i).coeff j).coeff k‖ ≤
      (1 + 128 * (D + 1 : ℕ) / ℓ) ^ (3 * D) * ε := by
  classical
  have hvol1 : volume (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal 2 := by norm_num
  have hvol2 : (volume.prod volume) (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ≤
      ENNReal.ofReal 4 := by rw [Measure.prod_prod]; norm_num
  obtain ⟨G, hGm, hGS, hGmass, hfib⟩ := exists_many_large_fibers
    (volume.prod volume) volume (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
    (Set.Icc (-1 : ℝ) 1) E (measurableSet_Icc.prod measurableSet_Icc) hE hrect
    4 2 ℓ (by norm_num) (by norm_num) hℓ hvol2 hvol1 hmass
  have hGmass' : ENNReal.ofReal (ℓ / 4) ≤ (volume.prod volume) G := by
    simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using hGmass
  have hfib' (w : ℝ × ℝ) (hw : w ∈ G) : ENNReal.ofReal (ℓ / 8) ≤ volume (Prod.mk w ⁻¹' E) := by
    simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using hfib w hw
  let C₁ : ℝ := 1 + 4 * (D + 1 : ℕ) * (1 + (1 : ℝ)) / (ℓ / 8)
  let C₂ : ℝ := 1 + 32 * (D + 1 : ℕ) / (ℓ / 4)
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hpoint (i : ℕ) (w : ℝ × ℝ) (hw : w ∈ G) :
      ‖((p.coeff i).map (Polynomial.evalRingHom (w.1 : ℂ))).eval (w.2 : ℂ)‖ ≤ C₁ ^ D * ε := by
    let φ : Polynomial (Polynomial ℂ) →+* ℂ :=
      (Polynomial.evalRingHom (w.2 : ℂ)).comp (Polynomial.mapRingHom (Polynomial.evalRingHom (w.1 : ℂ)))
    have hdeg : (p.map φ).natDegree ≤ D := Polynomial.natDegree_map_le.trans houter
    have h := complex_polynomial_coeff_le_of_small_values (p.map φ) D hdeg
      (Prod.mk w ⁻¹' E) (ℓ / 8) 1 ε (by positivity) (by norm_num) hε (hfib' w hw)
      (fun z hz => abs_le.mpr ⟨(hrect hz).2.1, (hrect hz).2.2⟩)
      (fun z hz => hsmall w.1 w.2 z hz) i
    simpa only [Polynomial.coeff_map, φ, RingHom.comp_apply, Polynomial.coe_evalRingHom,
      Polynomial.coe_mapRingHom] using h
  have hC₁eq : C₁ = 1 + 64 * (D + 1 : ℕ) / ℓ := by dsimp [C₁]; field_simp; ring
  have hC₂eq : C₂ = 1 + 128 * (D + 1 : ℕ) / ℓ := by dsimp [C₂]; field_simp; ring
  have hC₁₂ : C₁ ≤ C₂ := by rw [hC₁eq, hC₂eq]; gcongr <;> norm_num
  intro i j k
  have h := bivariate_polynomial_coeff_le_of_small_values (p.coeff i) D (hmiddle i) (hinner i)
    G hGm hGS (ℓ / 4) (C₁ ^ D * ε) (by positivity) (by positivity) hGmass'
    (fun x y hxy => hpoint i (x, y) hxy) j k
  calc
    ‖((p.coeff i).coeff j).coeff k‖ ≤ C₂ ^ (2 * D) * (C₁ ^ D * ε) := h
    _ ≤ C₂ ^ (2 * D) * (C₂ ^ D * ε) := by gcongr
    _ = C₂ ^ (2 * D + D) * ε := by rw [pow_add]; ring
    _ = (1 + 128 * (D + 1 : ℕ) / ℓ) ^ (3 * D) * ε := by
      rw [hC₂eq, show 2 * D + D = 3 * D by omega]

end Submission.Lib.K4PolynomialNorming
