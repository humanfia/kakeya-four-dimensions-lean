-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/CoefficientAnchor.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.DiscriminantBounds

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial Set Metric

private noncomputable def coefficientPolynomial (s : Finset (Fin 3 →₀ ℕ)) :
    (s → ℝ) →ₗ[ℝ] MvPolynomial (Fin 3) ℝ := by
  classical
  exact ∑ m : s, (monomial m.1).comp (LinearMap.proj m)

private theorem coefficientPolynomial_coeff (s : Finset (Fin 3 →₀ ℕ))
    (a : s → ℝ) (m : s) : (coefficientPolynomial s a).coeff m.1 = a m := by
  classical
  simp only [coefficientPolynomial, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, coeff_sum, coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hbm
    exact ite_eq_right (Subtype.coe_injective.ne hbm)
  · simp

private theorem coefficientPolynomial_injective (s : Finset (Fin 3 →₀ ℕ)) :
    Function.Injective (coefficientPolynomial s) := by
  intro a b hab
  funext m
  simpa only [coefficientPolynomial_coeff] using congrArg (fun P => P.coeff m.1) hab

private theorem coefficientPolynomial_recover (s : Finset (Fin 3 →₀ ℕ))
    (P : MvPolynomial (Fin 3) ℝ) (hP : P.support ⊆ s) :
    coefficientPolynomial s (fun m => P.coeff m.1) = P := by
  classical
  simp only [coefficientPolynomial, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  calc
    (∑ m : s, monomial m.1 (P.coeff m.1)) = ∑ m ∈ s, monomial m (P.coeff m) := by
      exact (Finset.sum_subtype s (fun _ => Iff.rfl) (fun m => monomial m (P.coeff m))).symm
    _ = ∑ m ∈ P.support, monomial m (P.coeff m) := by
      exact (Finset.sum_subset hP (by
        intro m _ hm
        rw [notMem_support_iff.mp hm, map_zero])).symm
    _ = P := P.as_sum.symm

private theorem box_norm_le {r : ℝ} (hr : 0 < r) (x : Fin 3 → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-(r / 3)) (r / 3)) : ‖WithLp.toLp 2 x‖ ≤ r := by
  have hs (i : Fin 3) : (x i) ^ 2 ≤ (r / 3) ^ 2 := by
    have hl := (hx i).1
    have hu := (hx i).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.le) (by linarith : 0 ≤ x i + r / 3)]
  have hn := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)
  simp [Fin.sum_univ_succ] at hn
  nlinarith [hs 0, hs 1, hs 2, norm_nonneg (WithLp.toLp 2 x)]

/-- On any fixed finite monomial span, one real point of a fixed ball
controls every coefficient, with one constant for the entire span. -/
theorem finite_monomial_anchor (s : Finset (Fin 3 →₀ ℕ)) {r : ℝ} (hr : 0 < r) :
    ∃ K : ℝ, 0 < K ∧ ∀ P : MvPolynomial (Fin 3) ℝ, P.support ⊆ s →
      ∃ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ r ∧
        ∀ m, |P.coeff m| ≤ K * |eval (fun i => z i) P| := by
  classical
  let B := closedBall (0 : EuclideanSpace ℝ (Fin 3)) r
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) r)
  let : Nonempty B := ⟨⟨0, mem_closedBall_self hr.le⟩⟩
  let f : (s → ℝ) →ₗ[ℝ] C(B, ℝ) :=
    { toFun := fun a =>
        ⟨fun z => eval (fun i => z.1 i) (coefficientPolynomial s a),
          (MvPolynomial.continuous_eval _).comp (by fun_prop)⟩
      map_add' := by intro a b; ext z; simp
      map_smul' := by intro t a; ext z; simp }
  have hfinj : Function.Injective f := by
    intro a b hab
    apply coefficientPolynomial_injective s
    apply MvPolynomial.funext_set (fun _ : Fin 3 => Ioo (-(r / 3)) (r / 3))
      (fun _ => Ioo_infinite (by linarith))
    intro x hx
    have hx' : ∀ i, x i ∈ Ioo (-(r / 3)) (r / 3) := fun i => hx i (mem_univ i)
    let z : B := ⟨WithLp.toLp 2 x, mem_closedBall_zero_iff.mpr (box_norm_le hr x hx')⟩
    exact congrArg (fun g : C(B, ℝ) => g z) hab
  obtain ⟨K, hK, hanti⟩ := f.injective_iff_antilipschitz.mp hfinj
  refine ⟨K, hK, ?_⟩
  intro P hP
  let a : s → ℝ := fun m => P.coeff m.1
  have hrecover : coefficientPolynomial s a = P := coefficientPolynomial_recover s P hP
  have hn : ∃ z : B, ‖f a‖ ≤ ‖f a z‖ := by
    by_contra h
    push Not at h
    exact (lt_irrefl ‖f a‖) ((f a).norm_lt_iff_of_nonempty.mpr h)
  obtain ⟨z, hz⟩ := hn
  refine ⟨z.1, mem_closedBall_zero_iff.mp z.2, ?_⟩
  intro m
  by_cases hm : m ∈ s
  · have hcoeff : |P.coeff m| ≤ ‖a‖ := by
      exact norm_le_pi_norm a ⟨m, hm⟩
    have hb := ZeroHomClass.bound_of_antilipschitz f hanti a
    have h := hcoeff.trans (hb.trans (mul_le_mul_of_nonneg_left hz K.2))
    simpa only [f, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.coe_mk, hrecover,
      Real.norm_eq_abs] using h
  · rw [notMem_support_iff.mp (fun h => hm (hP h)), abs_zero]
    exact mul_nonneg K.2 (abs_nonneg _)

/-- A fixed degree bound admits a uniform real anchor for all coefficients. -/
theorem polynomial_coefficient_anchor (D : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ K : ℝ, 0 < K ∧ ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ D →
      ∃ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ r ∧
        ∀ m, |P.coeff m| ≤ K * |eval (fun i => z i) P| := by
  obtain ⟨K, hK, h⟩ := finite_monomial_anchor (monomialSet 3 D) hr
  exact ⟨K, hK, fun P hP => h P (support_subset_monomialSet P hP)⟩

end Submission.Obl.k4_paired_test_normalization
