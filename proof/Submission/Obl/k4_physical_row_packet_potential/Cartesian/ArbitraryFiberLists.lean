-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/ArbitraryFiberLists.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/ArbitraryFiberLists.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/ArbitraryFiberLists.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.PolynomialFiberLists
import Submission.Obl.k4_scalar_initial_true_horizon.FiniteCardBound

/-!
The actual coefficient-list bound holds for an arbitrary original family,
not merely an a priori finite sample. Every finite collection of distinct
codes has actual fitting representatives, so the finite packing theorem
and the accepted uniform-cardinality criterion apply.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set

noncomputable section

/-- Ordinary original witness durations and pointwise local value lists
give one finite coefficient list for the ENTIRE original family. The
constant is uniform before both the family and the coefficient mesh. -/
theorem arbitrary_polynomial_fit_list_power_bound (D q : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ι : Type*)
      (P : ι → Fin q → Polynomial ℝ), (∀ i j, (P i j).natDegree ≤ D) →
      ∀ (E : ι → Set ℝ), (∀ i, MeasurableSet (E i)) →
      (∀ i, E i ⊆ Icc (0 : ℝ) 1) → ∀ p K : ℝ, 0 < p → 1 ≤ K →
      (∀ i, ENNReal.ofReal (1 / K) ≤ volume (E i)) →
      (∀ t, ∃ V : Finset (Fin q → ℤ), (V.card : ℝ) ≤ K ∧
        ∀ i, t ∈ E i → (fun j : Fin q => ⌊(P i j).eval t / p⌋) ∈ V) →
      ∃ F : Finset (Fin (q * (D + 1)) → ℤ),
        (F.card : ℝ) ≤ A * K ^ (3 + 3 * D * (q * (D + 1))) ∧
        ∀ i, polynomialFitCoefficientCode D p (P i) ∈ F := by
  classical
  obtain ⟨A, hA, hbound⟩ := polynomial_fit_list_power_bound D q
  refine ⟨A, hA, ?_⟩
  intro ι P hP E hE hunit p K hp hK hmass hlocal
  let codes := Set.range (fun i => polynomialFitCoefficientCode D p (P i))
  have hcount : ∀ F : Finset (Fin (q * (D + 1)) → ℤ), (↑F : Set _) ⊆ codes →
      (F.card : ℝ) ≤ A * K ^ (3 + 3 * D * (q * (D + 1))) := by
    intro F hF
    have hex (c : F) : ∃ i, polynomialFitCoefficientCode D p (P i) = c.1 := hF c.2
    choose index hindex using hex
    have hfinlocal (t : ℝ) :
        (((Finset.univ.filter fun c : F => t ∈ E (index c)).image
          (fun c => fun j : Fin q => ⌊(P (index c) j).eval t / p⌋)).card : ℝ) ≤ K := by
      obtain ⟨V, hV, hVm⟩ := hlocal t
      apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (show
        (Finset.univ.filter fun c : F => t ∈ E (index c)).image
          (fun c => fun j : Fin q => ⌊(P (index c) j).eval t / p⌋) ⊆ V from ?_))) hV
      intro v hv
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hv
      exact hVm (index c) (Finset.mem_filter.mp hc).2
    have hb := hbound F (fun c => P (index c)) (fun c => hP (index c))
      (fun c => E (index c)) (fun c => hE (index c)) (fun c => hunit (index c))
      p K hp hK (fun c => hmass (index c)) hfinlocal
    have hinj : Function.Injective (fun c : F => polynomialFitCoefficientCode D p (P (index c))) := by
      intro c c' h
      apply Subtype.ext
      exact (hindex c).symm.trans (h.trans (hindex c'))
    simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_coe] using hb
  have hfinite := Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
    codes (A * K ^ (3 + 3 * D * (q * (D + 1)))) hcount
  refine ⟨hfinite.toFinset, hcount _ (by simp), ?_⟩
  intro i
  exact hfinite.mem_toFinset.mpr ⟨i, rfl⟩

/-- Approximating the ORIGINAL field to one value mesh only enlarges the
pointwise value list by the fixed factor `3^q`. The resulting coefficient
list is still uniform in the family, its magnitude, and the mesh. -/
theorem approximate_original_field_fiber_lists (D q : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ι : Type*)
      (P : ι → Fin q → Polynomial ℝ), (∀ i j, (P i j).natDegree ≤ D) →
      ∀ (E : ι → Set ℝ), (∀ i, MeasurableSet (E i)) →
      (∀ i, E i ⊆ Icc (0 : ℝ) 1) → ∀ p K : ℝ, 0 < p → 1 ≤ K →
      (∀ i, ENNReal.ofReal (1 / K) ≤ volume (E i)) →
      ∀ G : ι → ℝ → Fin q → ℝ,
      (∀ i t, t ∈ E i → ∀ j, |(P i j).eval t - G i t j| ≤ p) →
      (∀ t, ∃ V : Finset (Fin q → ℤ), (V.card : ℝ) ≤ K ∧
        ∀ i, t ∈ E i → (fun j : Fin q => ⌊G i t j / p⌋) ∈ V) →
      ∃ F : Finset (Fin (q * (D + 1)) → ℤ),
        (F.card : ℝ) ≤ A * K ^ (3 + 3 * D * (q * (D + 1))) ∧
        ∀ i, polynomialFitCoefficientCode D p (P i) ∈ F := by
  classical
  obtain ⟨A, hA, hbound⟩ := arbitrary_polynomial_fit_list_power_bound D q
  let b : ℕ := 3 + 3 * D * (q * (D + 1))
  refine ⟨A * ((3 : ℝ) ^ q) ^ b, by positivity, ?_⟩
  intro ι P hP E hE hunit p K hp hK hmass G hfit hlocal
  let K' := (3 : ℝ) ^ q * K
  have hthree : 1 ≤ (3 : ℝ) ^ q := one_le_pow₀ (by norm_num)
  have hKK' : K ≤ K' := by dsimp [K']; nlinarith
  have hK' : 1 ≤ K' := hK.trans hKK'
  have hmass' (i : ι) : ENNReal.ofReal (1 / K') ≤ volume (E i) := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) (hmass i)
    exact one_div_le_one_div_of_le (by linarith) hKK'
  have hlocal' (t : ℝ) : ∃ V : Finset (Fin q → ℤ), (V.card : ℝ) ≤ K' ∧
      ∀ i, t ∈ E i → (fun j : Fin q => ⌊(P i j).eval t / p⌋) ∈ V := by
    obtain ⟨V, hV, hVm⟩ := hlocal t
    let W := V.biUnion (Submission.Lib.K4ListedExceptions.integerCodeBox 1)
    refine ⟨W, ?_, ?_⟩
    · have hc : W.card ≤ V.card * 3 ^ q := by
        calc
          W.card ≤ ∑ v ∈ V,
              (Submission.Lib.K4ListedExceptions.integerCodeBox 1 v).card :=
            Finset.card_biUnion_le
          _ = V.card * 3 ^ q := by
            simp only [Submission.Lib.K4ListedExceptions.card_integerCodeBox,
              Finset.sum_const_nat]
      have hcr : (W.card : ℝ) ≤ (V.card : ℝ) * (3 : ℝ) ^ q := by exact_mod_cast hc
      exact hcr.trans (by dsimp [K']; nlinarith)
    · intro i hi
      apply Finset.mem_biUnion.mpr
      refine ⟨_, hVm i hi, ?_⟩
      apply Submission.Lib.K4ListedExceptions.floor_code_mem_integerCodeBox 1
        (fun j => (P i j).eval t) (G i t) (fun _ => p) (fun _ => hp)
      simpa only [Nat.cast_one, one_mul] using hfit i t hi
  obtain ⟨F, hF, hFm⟩ := hbound ι P hP E hE hunit p K' hp hK' hmass' hlocal'
  refine ⟨F, ?_, hFm⟩
  calc
    (F.card : ℝ) ≤ A * K' ^ b := hF
    _ = (A * ((3 : ℝ) ^ q) ^ b) * K ^ b := by dsimp only [K']; rw [mul_pow]; ring

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
