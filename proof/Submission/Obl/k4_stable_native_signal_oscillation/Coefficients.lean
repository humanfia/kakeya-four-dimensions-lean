import Mathlib

namespace Submission.Obl.k4_stable_native_signal_oscillation
open Set MvPolynomial

noncomputable def boxExponent {D : ℕ} (d : Fin 3 → Fin (D + 1)) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (d i : ℕ))

lemma boxExponent_injective {D : ℕ} : Function.Injective (boxExponent (D := D)) := by
  intro d e h
  funext i
  apply Fin.ext
  have hi := congrArg (fun f : Fin 3 →₀ ℕ => f i) h
  simpa [boxExponent] using hi

noncomputable def boxPolynomial {D : ℕ} (c : (Fin 3 → Fin (D + 1)) → ℝ) : MvPolynomial (Fin 3) ℝ :=
  ∑ d, monomial (boxExponent d) (c d)

lemma coeff_boxPolynomial {D : ℕ} (c : (Fin 3 → Fin (D + 1)) → ℝ)
    (d : Fin 3 → Fin (D + 1)) :
    (boxPolynomial c).coeff (boxExponent d) = c d := by
  classical
  simp [boxPolynomial, coeff_monomial, boxExponent_injective.eq_iff]

lemma boxPolynomial_coefficients {D : ℕ} (P : MvPolynomial (Fin 3) ℝ)
    (hP : P.totalDegree ≤ D) :
    boxPolynomial (D := D) (fun d => P.coeff (boxExponent d)) = P := by
  classical
  apply MvPolynomial.ext
  intro m
  by_cases hm : ∃ d : Fin 3 → Fin (D + 1), boxExponent d = m
  · obtain ⟨d, rfl⟩ := hm
    exact coeff_boxPolynomial _ _
  · have hcoeff : P.coeff m = 0 := by
      by_contra h
      have hmem := mem_support_iff.mpr h
      have hlt (i : Fin 3) : m i < D + 1 := by
        have hi := (le_degreeOf_of_mem_support i hmem).trans
          ((degreeOf_le_totalDegree P i).trans hP)
        omega
      apply hm
      refine ⟨fun i => ⟨m i, hlt i⟩, ?_⟩
      ext i
      simp [boxExponent]
    rw [hcoeff]
    simp only [boxPolynomial, coeff_sum, coeff_monomial]
    apply Finset.sum_eq_zero
    intro d hd
    exact ite_eq_right (by intro h; exact hm ⟨d, h⟩)

lemma cube_small_norm (x : Fin 3 → ℝ)
    (hx : x ∈ Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-1 / 32 : ℝ) (1 / 32))) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 / 8 := by
  have hb (i : Fin 3) : |x i| ≤ 1 / 32 := by
    apply abs_le.mpr
    obtain ⟨hl, hr⟩ := hx i (mem_univ _)
    constructor <;> linarith
  have hs : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ ^ 2 ≤ 3 * (1 / 32 : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ i, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) i‖ ^ 2
          ≤ ∑ _i : Fin 3, (1 / 32 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using hb i) 2
      _ = 3 * (1 / 32 : ℝ) ^ 2 := by norm_num
  nlinarith [norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))]

/-- Bounded values on a fixed real ball control every coefficient, in each fixed degree. -/
lemma exists_coefficient_bound_on_ball_degree (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
    ∀ V : ℝ, 0 ≤ V →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 8 → |eval (fun i => x i) P| ≤ V) →
      ∀ m, |P.coeff m| ≤ C * V := by
  classical
  let B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 8)
  have hB : IsCompact B := isCompact_closedBall _ _
  have : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let L : (((Fin 3 → Fin (D + 1)) → ℝ)) →ₗ[ℝ] C(B, ℝ) :=
    { toFun := fun c => ⟨fun x => eval (fun i => x.val i) (boxPolynomial c),
        (MvPolynomial.continuous_eval _).comp (by fun_prop)⟩
      map_add' := by
        intro c d
        ext x
        simp [boxPolynomial, eval_monomial, Finset.sum_add_distrib]
      map_smul' := by
        intro r c
        ext x
        simp [boxPolynomial, eval_monomial, mul_assoc, Finset.mul_sum] }
  have hL : Function.Injective L := by
    intro c d hcd
    have hpoly : boxPolynomial c = boxPolynomial d := by
      apply MvPolynomial.funext_set (fun _ : Fin 3 => Set.Icc (-1 / 32 : ℝ) (1 / 32))
        (by intro i; exact Set.Icc_infinite (by norm_num))
      intro x hx
      have hnorm := cube_small_norm x hx
      have he := congrArg (fun f : C(B, ℝ) => f
        ⟨WithLp.toLp 2 x, by simpa only [B, Metric.mem_closedBall, dist_zero_right] using hnorm⟩) hcd
      exact he
    funext e
    simpa only [coeff_boxPolynomial] using congrArg (fun p => p.coeff (boxExponent e)) hpoly
  obtain ⟨C, hC, hanti⟩ := L.injective_iff_antilipschitz.mp hL
  refine ⟨C, hC, ?_⟩
  intro P hP V hV hbound m
  let c : (Fin 3 → Fin (D + 1)) → ℝ := fun d => P.coeff (boxExponent d)
  have hcP : boxPolynomial c = P := boxPolynomial_coefficients P hP
  have hLc : ‖L c‖ ≤ V := (ContinuousMap.norm_le _ hV).mpr (by
    intro x
    change |eval (fun i => x.val i) (boxPolynomial c)| ≤ V
    rw [hcP]
    exact hbound x (by simpa only [B, Metric.mem_closedBall, dist_zero_right] using x.property))
  have hc : ‖c‖ ≤ (C : ℝ) * V :=
    (hanti.le_mul_norm (map_zero L) c).trans (mul_le_mul_of_nonneg_left hLc C.coe_nonneg)
  by_cases hm : ∃ d : Fin 3 → Fin (D + 1), boxExponent d = m
  · obtain ⟨d, rfl⟩ := hm
    have he : |P.coeff (boxExponent d)| ≤ ‖c‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm c d
    exact he.trans hc
  · rw [← hcP]
    simp only [boxPolynomial, coeff_sum, coeff_monomial]
    have hz : ∑ d : Fin 3 → Fin (D + 1), (if boxExponent d = m then c d else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      exact ite_eq_right (by intro h; exact hm ⟨d, h⟩)
    simpa only [hz, abs_zero] using mul_nonneg C.coe_nonneg hV

/-- The quadratic specialization used for centers and discriminants. -/
lemma exists_coefficient_bound_on_ball : ∃ C : ℝ, 0 < C ∧
    ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ 2 →
    ∀ V : ℝ, 0 ≤ V →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 8 → |eval (fun i => x i) P| ≤ V) →
      ∀ m, |P.coeff m| ≤ C * V := exists_coefficient_bound_on_ball_degree 2

end Submission.Obl.k4_stable_native_signal_oscillation
