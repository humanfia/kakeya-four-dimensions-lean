-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/BoxNorming.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). Curl coefficients from large-curl start mass when the base
law lives in a box of radius `R ≥ 1` (packet bases are bounded by `K`, not
by one). Rescaling the curl polynomial reduces to
`Submission.Lib.K4PolynomialNorming.original_polynomial_sublevel_mass_bound`
(session x0001); the argument is that of `original_large_curl_mass` and
`original_curl_coefficients_of_mass_budget` there.
-/
import Submission.Lib.K4PolynomialNorming.OriginalCurlSublevel
import Submission.Lib.K4ScalarSwitching.SwitchPath
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory MvPolynomial
open scoped ENNReal
open Submission.Lib.K4PolynomialNorming

/-- The polynomial `u ↦ F (R u)`. -/
noncomputable def rescalePoly {n : ℕ} (R : ℝ) (F : MvPolynomial (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ :=
  aeval (fun i => C R * X i) F

theorem coeff_rescalePoly {n : ℕ} (R : ℝ) (F : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    (rescalePoly R F).coeff m = R ^ (m.sum fun _ e => e) * F.coeff m := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial s a =>
    unfold rescalePoly
    rw [aeval_monomial]
    simp only [algebraMap_eq, mul_pow, Finsupp.prod]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, prod_X_pow_eq_monomial,
      ← C_pow, ← mul_assoc, ← C_mul, C_mul_monomial, mul_one, coeff_monomial, coeff_monomial]
    by_cases hsm : s = m
    · subst hsm
      simp [Finsupp.sum, mul_comm]
    · simp [hsm]
  | add p q hp hq =>
    simp only [rescalePoly, map_add] at hp hq ⊢
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
    ring

theorem eval_rescalePoly {n : ℕ} (R : ℝ) (F : MvPolynomial (Fin n) ℝ) (u : Fin n → ℝ) :
    eval u (rescalePoly R F) = eval (fun i => R * u i) F := by
  unfold rescalePoly
  rw [Submission.Lib.K4ScalarSwitching.Switching.eval_substitution]
  have h : (fun j => eval u (C R * X j)) = fun i => R * u i := by
    funext i
    simp
  rw [h]

theorem totalDegree_rescalePoly {n : ℕ} (R : ℝ) (F : MvPolynomial (Fin n) ℝ) :
    (rescalePoly R F).totalDegree ≤ F.totalDegree :=
  Submission.Lib.K4ScalarSwitching.PolynomialDegree.degree_aeval_le F _
    (fun i => (totalDegree_mul _ _).trans (by simp))

theorem abs_coeff_le_rescale {n : ℕ} {R : ℝ} (hR : 1 ≤ R) (F : MvPolynomial (Fin n) ℝ)
    (m : Fin n →₀ ℕ) : |F.coeff m| ≤ |(rescalePoly R F).coeff m| := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  rw [coeff_rescalePoly, abs_mul, abs_of_nonneg (pow_nonneg hR0 _)]
  exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hR)

/-- A large curl coefficient forces large-curl starting mass, for a base law
with ceiling after rescaling the radius-`R` box to the unit box. -/
theorem original_large_curl_mass_box (D : ℕ) : ∃ cNorm : ℕ,
    ∀ {X : Type*} [MeasurableSpace X]
      (P : Measure X) [IsProbabilityMeasure P]
      (base : X → Fin 3 → ℝ) (hbase : Measurable base) (R : ℝ) (hR : 1 ≤ R)
      (K : ENNReal) (hcap : P.map (fun x => fun j => R⁻¹ * base x j) ≤ K • volume)
      (hbox : ∀ᵐ x ∂P, ∀ j, |base x j| ≤ R)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
      (hdegree : ∀ i j, (pderiv j (T i) - pderiv i (T j)).totalDegree ≤ D)
      (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε)
      (hlarge : ∃ i j m, A ^ cNorm * ε < |(pderiv j (T i) - pderiv i (T j)).coeff m|),
      1 ≤ P (largeFieldCurlStart T base ε) + K * ENNReal.ofReal A⁻¹ := by
  obtain ⟨cNorm, hNorm⟩ := original_polynomial_sublevel_mass_bound D 3
  refine ⟨cNorm, ?_⟩
  intro X _ P _ base hbase R hR K hcap hbox T hdegree A ε hA hε hlarge
  obtain ⟨i, j, m, hm⟩ := hlarge
  let F := pderiv j (T i) - pderiv i (T j)
  have hR0 : 0 < R := by linarith
  let base' : X → Fin 3 → ℝ := fun x => fun k => R⁻¹ * base x k
  have hbase' : Measurable base' := by
    apply measurable_pi_iff.mpr
    intro k
    exact ((measurable_pi_apply k).comp hbase).const_mul _
  have hbox' : ∀ᵐ x ∂P, ∀ k, |base' x k| ≤ 1 := by
    filter_upwards [hbox] with x hx k
    simp only [base', abs_mul, abs_inv, abs_of_pos hR0]
    rw [inv_mul_le_iff₀ hR0, mul_one]
    exact hx k
  have hsmall := hNorm P base' hbase' K hcap hbox' (rescalePoly R F)
    ((totalDegree_rescalePoly R F).trans (hdegree i j)) A ε hA hε
    ⟨m, lt_of_lt_of_le hm (abs_coeff_le_rescale hR F m)⟩
  have heval (x : X) : eval (base' x) (rescalePoly R F) = eval (base x) F := by
    rw [eval_rescalePoly]
    have h : (fun k => R * base' x k) = base x := by
      funext k
      simp only [base']
      field_simp
    rw [h]
  simp only [heval] at hsmall
  have hcover : (univ : Set X) ⊆ largeFieldCurlStart T base ε ∪
      {x | |eval (base x) F| ≤ ε} := by
    intro x _
    by_cases hx : x ∈ largeFieldCurlStart T base ε
    · exact Or.inl hx
    · apply Or.inr
      change |eval (base x) F| ≤ ε
      refine le_of_not_gt (fun h => hx ?_)
      exact ⟨i, j, by simpa only [F, map_sub] using h⟩
  calc
    _ = P univ := by simp
    _ ≤ P (largeFieldCurlStart T base ε ∪ {x | |eval (base x) F| ≤ ε}) := measure_mono hcover
    _ ≤ P (largeFieldCurlStart T base ε) + P {x | |eval (base x) F| ≤ ε} :=
      measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hsmall

/-- A strict original-law mass budget bounds every curl coefficient, with the
base law in a box of radius `R`. -/
theorem original_curl_coefficients_of_mass_budget_box (D : ℕ) : ∃ cNorm : ℕ,
    ∀ {X : Type*} [MeasurableSpace X]
      (P : Measure X) [IsProbabilityMeasure P]
      (base : X → Fin 3 → ℝ) (hbase : Measurable base) (R : ℝ) (hR : 1 ≤ R)
      (K : ENNReal) (hcap : P.map (fun x => fun j => R⁻¹ * base x j) ≤ K • volume)
      (hbox : ∀ᵐ x ∂P, ∀ j, |base x j| ≤ R)
      (T : Fin 3 → MvPolynomial (Fin 3) ℝ)
      (hdegree : ∀ i j, (pderiv j (T i) - pderiv i (T j)).totalDegree ≤ D)
      (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 ≤ ε)
      (J Bound : ENNReal)
      (hupper : J * P (largeFieldCurlStart T base ε) ≤ Bound)
      (hbudget : Bound + J * (K * ENNReal.ofReal A⁻¹) < J),
      ∀ i j m, |(pderiv j (T i) - pderiv i (T j)).coeff m| ≤ A ^ cNorm * ε := by
  obtain ⟨cNorm, hNorm⟩ := original_large_curl_mass_box D
  refine ⟨cNorm, ?_⟩
  intro X _ P _ base hbase R hR K hcap hbox T hdegree A ε hA hε J Bound hupper hbudget i j m
  by_contra hn
  have hlower := hNorm P base hbase R hR K hcap hbox T hdegree A ε hA hε
    ⟨i, j, m, lt_of_not_ge hn⟩
  have hscaled : J ≤ J * P (largeFieldCurlStart T base ε) + J * (K * ENNReal.ofReal A⁻¹) := by
    simpa only [mul_one, mul_add] using mul_le_mul' le_rfl hlower
  exact (not_le_of_gt hbudget) (hscaled.trans (add_le_add hupper le_rfl))

end Submission.Obl.k4_physical_row_packet_potential.Switch
