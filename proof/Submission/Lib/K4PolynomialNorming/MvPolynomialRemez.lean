/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.TrivariateRemez
import Submission.Lib.K4PolynomialNorming.PolynomialEncodings
import Submission.Lib.K4PolynomialNorming.RemezCoordinates

open Set MeasureTheory MvPolynomial

namespace Submission.Lib.K4PolynomialNorming

private theorem binary_mvPolynomial_coeff_bound_on_product
    (F : MvPolynomial (Fin 2) ℂ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set (ℝ × ℝ)) (hE : MeasurableSet E)
    (hrect : E ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε)
    (hmass : ENNReal.ofReal ℓ ≤ (volume.prod volume) E)
    (hsmall : ∀ x y : ℝ, (x, y) ∈ E → ‖MvPolynomial.eval ![(y : ℂ), (x : ℂ)] F‖ ≤ ε) :
    ∀ m : Fin 2 →₀ ℕ, ‖F.coeff m‖ ≤ (1 + 32 * (D + 1 : ℕ) / ℓ) ^ (2 * D) * ε := by
  have h := bivariate_polynomial_coeff_le_of_small_values (binaryPolynomialEncoding ℂ F) D
    ((binaryPolynomialEncoding_natDegree_le F).trans hD)
    (fun i => (binaryPolynomialEncoding_coeff_natDegree_le F i).trans hD) E hE hrect ℓ ε hℓ hε hmass
    (fun x y hxy => by rw [eval_binaryPolynomialEncoding]; exact hsmall x y hxy)
  intro m
  have hm : (Finsupp.single (0 : Fin 1) (m 1)).cons (m 0) = m := by
    change (Finsupp.single default (m.tail default)).cons (m 0) = m
    rw [← Finsupp.unique_single, Finsupp.cons_tail]
  simpa only [binaryPolynomialEncoding_coeff_coeff, hm] using h (m 0) (m 1)

private theorem ternary_mvPolynomial_coeff_bound_on_product
    (F : MvPolynomial (Fin 3) ℂ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set ((ℝ × ℝ) × ℝ)) (hE : MeasurableSet E)
    (hrect : E ⊆ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ×ˢ Set.Icc (-1 : ℝ) 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε)
    (hmass : ENNReal.ofReal ℓ ≤ ((volume.prod volume).prod volume) E)
    (hsmall : ∀ x y z : ℝ, ((x, y), z) ∈ E →
      ‖MvPolynomial.eval ![(z : ℂ), (y : ℂ), (x : ℂ)] F‖ ≤ ε) :
    ∀ m : Fin 3 →₀ ℕ, ‖F.coeff m‖ ≤ (1 + 128 * (D + 1 : ℕ) / ℓ) ^ (3 * D) * ε := by
  have h := trivariate_polynomial_coeff_le_of_small_values (ternaryPolynomialEncoding ℂ F) D
    ((ternaryPolynomialEncoding_natDegree_le F).trans hD)
    (fun i => (ternaryPolynomialEncoding_coeff_natDegree_le F i).trans hD)
    (fun i j => (ternaryPolynomialEncoding_coeff_coeff_natDegree_le F i j).trans hD)
    E hE hrect ℓ ε hℓ hε hmass
    (fun x y z hxyz => by rw [eval_ternaryPolynomialEncoding]; exact hsmall x y z hxyz)
  intro m
  have hm : ((Finsupp.single (0 : Fin 1) (m 2)).cons (m 1)).cons (m 0) = m := by
    change ((Finsupp.single default (m.tail.tail default)).cons (m.tail 0)).cons (m 0) = m
    rw [← Finsupp.unique_single, Finsupp.cons_tail, Finsupp.cons_tail]
  simpa only [ternaryPolynomialEncoding_coeff_coeff_coeff, hm] using h (m 0) (m 1) (m 2)

/-- The binary coefficient Remez bound directly in multivariate polynomial
coordinates and the standard Lebesgue measure. -/
theorem binary_mvPolynomial_coeff_le_of_small_values
    (F : MvPolynomial (Fin 2) ℂ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set (Fin 2 → ℝ)) (hE : MeasurableSet E)
    (hbox : ∀ u ∈ E, ∀ i, |u i| ≤ 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (hmass : ENNReal.ofReal ℓ ≤ volume E)
    (hsmall : ∀ u ∈ E, ‖MvPolynomial.eval (fun i => (u i : ℂ)) F‖ ≤ ε) :
    ∀ m : Fin 2 →₀ ℕ, ‖F.coeff m‖ ≤ (1 + 32 * (D + 1 : ℕ) / ℓ) ^ (2 * D) * ε := by
  let E' : Set (ℝ × ℝ) := reversePairCoordinates.symm ⁻¹' E
  have hE' : MeasurableSet E' := reversePairCoordinates.symm.measurable hE
  have hvol : (volume.prod volume) E' = volume E :=
    reversePairCoordinates_measurePreserving.symm.measure_preimage hE.nullMeasurableSet
  have hrect : E' ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 := by
    rintro ⟨x, y⟩ hxy
    have hc := hbox (reversePairCoordinates.symm (x, y)) hxy
    refine ⟨abs_le.mp ?_, abs_le.mp ?_⟩
    · simpa [reversePairCoordinates_symm_apply] using hc 1
    · simpa [reversePairCoordinates_symm_apply] using hc 0
  apply binary_mvPolynomial_coeff_bound_on_product F D hD E' hE' hrect ℓ ε hℓ hε
    (by simpa only [hvol] using hmass)
  intro x y hxy
  have h := hsmall (reversePairCoordinates.symm (x, y)) hxy
  have hvec : (fun i : Fin 2 => ((![y, x] : Fin 2 → ℝ) i : ℂ)) = ![(y : ℂ), (x : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  simpa only [reversePairCoordinates_symm_apply, hvec] using h

/-- The ternary coefficient Remez bound directly in multivariate polynomial
coordinates and the standard Lebesgue measure. -/
theorem ternary_mvPolynomial_coeff_le_of_small_values
    (F : MvPolynomial (Fin 3) ℂ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set (Fin 3 → ℝ)) (hE : MeasurableSet E)
    (hbox : ∀ u ∈ E, ∀ i, |u i| ≤ 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (hmass : ENNReal.ofReal ℓ ≤ volume E)
    (hsmall : ∀ u ∈ E, ‖MvPolynomial.eval (fun i => (u i : ℂ)) F‖ ≤ ε) :
    ∀ m : Fin 3 →₀ ℕ, ‖F.coeff m‖ ≤ (1 + 128 * (D + 1 : ℕ) / ℓ) ^ (3 * D) * ε := by
  let E' : Set ((ℝ × ℝ) × ℝ) := reverseTripleCoordinates.symm ⁻¹' E
  have hE' : MeasurableSet E' := reverseTripleCoordinates.symm.measurable hE
  have hvol : ((volume.prod volume).prod volume) E' = volume E :=
    reverseTripleCoordinates_measurePreserving.symm.measure_preimage hE.nullMeasurableSet
  have hrect : E' ⊆ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) ×ˢ Set.Icc (-1 : ℝ) 1 := by
    rintro ⟨⟨x, y⟩, z⟩ hxyz
    have hc := hbox (reverseTripleCoordinates.symm ((x, y), z)) hxyz
    refine ⟨⟨abs_le.mp ?_, abs_le.mp ?_⟩, abs_le.mp ?_⟩
    · simpa [reverseTripleCoordinates_symm_apply] using hc 2
    · simpa [reverseTripleCoordinates_symm_apply] using hc 1
    · simpa [reverseTripleCoordinates_symm_apply] using hc 0
  apply ternary_mvPolynomial_coeff_bound_on_product F D hD E' hE' hrect ℓ ε hℓ hε
    (by simpa only [hvol] using hmass)
  intro x y z hxyz
  have h := hsmall (reverseTripleCoordinates.symm ((x, y), z)) hxyz
  have hvec : (fun i : Fin 3 => ((![z, y, x] : Fin 3 → ℝ) i : ℂ)) = ![(z : ℂ), (y : ℂ), (x : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  simpa only [reverseTripleCoordinates_symm_apply, hvec] using h

/-- Euclidean-space form of binary polynomial Remez. -/
theorem euclidean_binary_mvPolynomial_coeff_le_of_small_values
    (F : MvPolynomial (Fin 2) ℂ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : MeasurableSet E)
    (hbox : ∀ u ∈ E, ∀ i, |u i| ≤ 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (hmass : ENNReal.ofReal ℓ ≤ volume E)
    (hsmall : ∀ u ∈ E, ‖MvPolynomial.eval (fun i => (u i : ℂ)) F‖ ≤ ε) :
    ∀ m : Fin 2 →₀ ℕ, ‖F.coeff m‖ ≤ (1 + 32 * (D + 1 : ℕ) / ℓ) ^ (2 * D) * ε := by
  have hp := PiLp.volume_preserving_toLp (Fin 2)
  apply binary_mvPolynomial_coeff_le_of_small_values F D hD (WithLp.toLp 2 ⁻¹' E)
    (hp.measurable hE) (fun u hu i => hbox (WithLp.toLp 2 u) hu i) ℓ ε hℓ hε
    (by simpa only [hp.measure_preimage hE.nullMeasurableSet] using hmass)
  exact fun u hu => hsmall (WithLp.toLp 2 u) hu

/-- Euclidean-space form of ternary polynomial Remez. -/
theorem euclidean_ternary_mvPolynomial_coeff_le_of_small_values
    (F : MvPolynomial (Fin 3) ℂ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E)
    (hbox : ∀ u ∈ E, ∀ i, |u i| ≤ 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (hmass : ENNReal.ofReal ℓ ≤ volume E)
    (hsmall : ∀ u ∈ E, ‖MvPolynomial.eval (fun i => (u i : ℂ)) F‖ ≤ ε) :
    ∀ m : Fin 3 →₀ ℕ, ‖F.coeff m‖ ≤ (1 + 128 * (D + 1 : ℕ) / ℓ) ^ (3 * D) * ε := by
  have hp := PiLp.volume_preserving_toLp (Fin 3)
  apply ternary_mvPolynomial_coeff_le_of_small_values F D hD (WithLp.toLp 2 ⁻¹' E)
    (hp.measurable hE) (fun u hu i => hbox (WithLp.toLp 2 u) hu i) ℓ ε hℓ hε
    (by simpa only [hp.measure_preimage hE.nullMeasurableSet] using hmass)
  exact fun u hu => hsmall (WithLp.toLp 2 u) hu

theorem norm_eval_complexification {ι : Type*} (F : MvPolynomial ι ℝ) (u : ι → ℝ) :
    ‖MvPolynomial.eval (fun i => (u i : ℂ)) (MvPolynomial.map (algebraMap ℝ ℂ) F)‖ =
      |MvPolynomial.eval u F| := by
  change ‖MvPolynomial.eval ((algebraMap ℝ ℂ) ∘ u) (MvPolynomial.map (algebraMap ℝ ℂ) F)‖ = _
  rw [← MvPolynomial.map_eval]
  exact Complex.norm_real _

/-- Real binary coefficient Remez, on the actual Euclidean observation set. -/
theorem real_euclidean_binary_mvPolynomial_coeff_le_of_small_values
    (F : MvPolynomial (Fin 2) ℝ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : MeasurableSet E)
    (hbox : ∀ u ∈ E, ∀ i, |u i| ≤ 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (hmass : ENNReal.ofReal ℓ ≤ volume E)
    (hsmall : ∀ u ∈ E, |MvPolynomial.eval (fun i => u i) F| ≤ ε) :
    ∀ m : Fin 2 →₀ ℕ, |F.coeff m| ≤ (1 + 32 * (D + 1 : ℕ) / ℓ) ^ (2 * D) * ε := by
  have hd : (MvPolynomial.map (algebraMap ℝ ℂ) F).totalDegree ≤ D :=
    (show (MvPolynomial.map (algebraMap ℝ ℂ) F).totalDegree ≤ F.totalDegree from by
      unfold MvPolynomial.totalDegree
      exact Finset.sup_mono (support_map_subset (algebraMap ℝ ℂ) F)).trans hD
  have h := euclidean_binary_mvPolynomial_coeff_le_of_small_values
    (MvPolynomial.map (algebraMap ℝ ℂ) F) D hd E hE hbox ℓ ε hℓ hε hmass
    (fun u hu => by rw [norm_eval_complexification]; exact hsmall u hu)
  intro m
  have hm := h m
  rw [coeff_map] at hm
  change ‖(F.coeff m : ℂ)‖ ≤ _ at hm
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hm

/-- Real ternary coefficient Remez, on the actual Euclidean observation set. -/
theorem real_euclidean_ternary_mvPolynomial_coeff_le_of_small_values
    (F : MvPolynomial (Fin 3) ℝ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (E : Set (EuclideanSpace ℝ (Fin 3))) (hE : MeasurableSet E)
    (hbox : ∀ u ∈ E, ∀ i, |u i| ≤ 1)
    (ℓ ε : ℝ) (hℓ : 0 < ℓ) (hε : 0 ≤ ε) (hmass : ENNReal.ofReal ℓ ≤ volume E)
    (hsmall : ∀ u ∈ E, |MvPolynomial.eval (fun i => u i) F| ≤ ε) :
    ∀ m : Fin 3 →₀ ℕ, |F.coeff m| ≤ (1 + 128 * (D + 1 : ℕ) / ℓ) ^ (3 * D) * ε := by
  have hd : (MvPolynomial.map (algebraMap ℝ ℂ) F).totalDegree ≤ D :=
    (show (MvPolynomial.map (algebraMap ℝ ℂ) F).totalDegree ≤ F.totalDegree from by
      unfold MvPolynomial.totalDegree
      exact Finset.sup_mono (support_map_subset (algebraMap ℝ ℂ) F)).trans hD
  have h := euclidean_ternary_mvPolynomial_coeff_le_of_small_values
    (MvPolynomial.map (algebraMap ℝ ℂ) F) D hd E hE hbox ℓ ε hℓ hε hmass
    (fun u hu => by rw [norm_eval_complexification]; exact hsmall u hu)
  intro m
  have hm := h m
  rw [coeff_map] at hm
  change ‖(F.coeff m : ℂ)‖ ≤ _ at hm
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hm

end Submission.Lib.K4PolynomialNorming
