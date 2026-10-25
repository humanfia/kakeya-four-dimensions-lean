import Mathlib
import ChallengeDeps
import Submission.Obl.k4_polynomial_variation_tube.Local

/-!
# Variation of `arctan ∘ P` along a line

For a real polynomial `P` in `n` variables and an affine line `t ↦ a + t • e`, the function
`t ↦ arctan (P (a + t • e))` has total variation at most `π * deg P`: its derivative vanishes
only at the roots of the derivative of the univariate restriction `Q` of `P` to the line,
and between consecutive roots it is monotone with values in `(-π/2, π/2)`.

The main results are `line_variation_lintegral`, `line_variation_Icc`,
`line_variation_integrable` and `line_deriv_eq_fderiv`.
-/

open MeasureTheory Set

namespace Submission.Obl.k4_polynomial_variation_tube

/-! ### One-dimensional variation -/

/-- On an interval where a continuous derivative is positive, the variation is the
increment, hence at most `2 * M` for a function bounded by `M`. -/
lemma lintegral_Ioc_enorm_deriv_le_of_pos {h h' : ℝ → ℝ} {M a b : ℝ}
    (hd : ∀ t, HasDerivAt h (h' t) t) (hc : Continuous h') (hb : ∀ t, |h t| ≤ M)
    (hab : a ≤ b) (hpos : ∀ t ∈ Ioo a b, 0 < h' t) :
    ∫⁻ t in Ioc a b, ‖h' t‖ₑ ≤ ENNReal.ofReal (2 * M) := by
  rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
  have hcongr : ∫⁻ t in Ioo a b, ‖h' t‖ₑ = ∫⁻ t in Ioo a b, ENNReal.ofReal (h' t) := by
    refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (hpos t ht)]
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal]
  · apply ENNReal.ofReal_le_ofReal
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hc.intervalIntegrable a b)]
    have ha := hb a
    have hb' := hb b
    rw [abs_le] at ha hb'
    linarith [ha.1, ha.2, hb'.1, hb'.2]
  · exact (hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hpos t ht).le

/-- On an interval where a continuous derivative does not vanish, the variation is at most
`2 * M` for a function bounded by `M`. -/
lemma lintegral_Ioc_enorm_deriv_le_of_ne_zero {h h' : ℝ → ℝ} {M a b : ℝ}
    (hd : ∀ t, HasDerivAt h (h' t) t) (hc : Continuous h') (hb : ∀ t, |h t| ≤ M)
    (hab : a ≤ b) (hne : ∀ t ∈ Ioo a b, h' t ≠ 0) :
    ∫⁻ t in Ioc a b, ‖h' t‖ₑ ≤ ENNReal.ofReal (2 * M) := by
  by_cases hpos : ∀ t ∈ Ioo a b, 0 < h' t
  · exact lintegral_Ioc_enorm_deriv_le_of_pos hd hc hb hab hpos
  · push Not at hpos
    obtain ⟨t₀, ht₀, ht₀'⟩ := hpos
    have h0 : h' t₀ < 0 := lt_of_le_of_ne ht₀' (hne t₀ ht₀)
    have hneg : ∀ t ∈ Ioo a b, 0 < -h' t := by
      intro t ht
      by_contra hcon
      have h1 : 0 < h' t := lt_of_le_of_ne (by linarith) (hne t ht).symm
      obtain ⟨s, hs, hs0⟩ :=
        isPreconnected_Ioo.intermediate_value ht₀ ht hc.continuousOn ⟨h0.le, h1.le⟩
      exact hne s hs hs0
    have key := lintegral_Ioc_enorm_deriv_le_of_pos (h := fun t => -h t)
      (h' := fun t => -h' t) (fun t => (hd t).neg) hc.neg
      (fun t => by simpa only [abs_neg] using hb t) hab hneg
    simpa only [enorm_neg] using key

/-- A function bounded by `M` whose continuous derivative vanishes only on a finite set `Z`
has variation at most `(#(Z ∩ (a, b)) + 1) * 2M` on `(a, b]`. -/
lemma lintegral_Ioc_enorm_deriv_le_card {h h' : ℝ → ℝ} {M : ℝ} (Z : Finset ℝ)
    (hd : ∀ t, HasDerivAt h (h' t) t) (hc : Continuous h') (hb : ∀ t, |h t| ≤ M)
    (hZ : ∀ t, h' t = 0 → t ∈ Z) :
    ∀ (k : ℕ) (a b : ℝ), a ≤ b → (Z.filter (fun t => t ∈ Ioo a b)).card = k →
      ∫⁻ t in Ioc a b, ‖h' t‖ₑ ≤ ENNReal.ofReal ((k + 1) * (2 * M)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a b hab hk
  by_cases hz : ∃ z ∈ Z, z ∈ Ioo a b
  · obtain ⟨z, hzZ, hz⟩ := hz
    rw [← Ioc_union_Ioc_eq_Ioc hz.1.le hz.2.le,
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
    have hcard : (Z.filter (fun t => t ∈ Ioo a z)).card
        + (Z.filter (fun t => t ∈ Ioo z b)).card + 1 ≤ k := by
      have hdisj : Disjoint (Z.filter (fun t => t ∈ Ioo a z))
          (Z.filter (fun t => t ∈ Ioo z b)) := by
        rw [Finset.disjoint_filter]
        intro t _ h1 h2
        exact lt_asymm h1.2 h2.1
      have hnot : z ∉ (Z.filter (fun t => t ∈ Ioo a z)) ∪
          (Z.filter (fun t => t ∈ Ioo z b)) := by
        simp [Finset.mem_union, Finset.mem_filter]
      have hsub : insert z ((Z.filter (fun t => t ∈ Ioo a z)) ∪
          (Z.filter (fun t => t ∈ Ioo z b))) ⊆ Z.filter (fun t => t ∈ Ioo a b) := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, mem_Ioo] at ht ⊢
        rcases ht with rfl | ⟨hZt, h1, h2⟩ | ⟨hZt, h1, h2⟩
        · exact ⟨hzZ, hz⟩
        · exact ⟨hZt, h1, h2.trans hz.2⟩
        · exact ⟨hZt, hz.1.trans h1, h2⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj, hk] at this
      exact this
    have h1 := ih _ (by omega) a z hz.1.le rfl
    have h2 := ih _ (by omega) z b hz.2.le rfl
    refine (add_le_add h1 h2).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : ((Z.filter (fun t => t ∈ Ioo a z)).card : ℝ)
        + (Z.filter (fun t => t ∈ Ioo z b)).card + 1 ≤ k := by exact_mod_cast hcard
    nlinarith
  · push Not at hz
    have hne : ∀ t ∈ Ioo a b, h' t ≠ 0 := fun t ht h0 => hz t (hZ t h0) ht
    refine (lintegral_Ioc_enorm_deriv_le_of_ne_zero hd hc hb hab hne).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith

/-- A function bounded by `M` whose continuous derivative vanishes only on a finite set `Z`
has total variation at most `(#Z + 1) * 2M`. -/
lemma lintegral_enorm_deriv_le_card {h h' : ℝ → ℝ} {M : ℝ} (Z : Finset ℝ)
    (hd : ∀ t, HasDerivAt h (h' t) t) (hc : Continuous h') (hb : ∀ t, |h t| ≤ M)
    (hZ : ∀ t, h' t = 0 → t ∈ Z) :
    ∫⁻ t, ‖h' t‖ₑ ≤ ENNReal.ofReal ((Z.card + 1) * (2 * M)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  have hU : (⋃ N : ℕ, Ioc (-(N : ℝ)) N) = univ := by
    refine eq_univ_of_forall (fun t => mem_iUnion.2 ?_)
    obtain ⟨N, hN⟩ := exists_nat_gt |t|
    refine ⟨N, ?_, ?_⟩
    · linarith [neg_abs_le t]
    · linarith [le_abs_self t]
  rw [← setLIntegral_univ, ← hU, setLIntegral_iUnion_of_directed]
  · refine iSup_le (fun N => ?_)
    refine (lintegral_Ioc_enorm_deriv_le_card Z hd hc hb hZ _ _ _
      (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith) rfl).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have : ((Z.filter (fun t => t ∈ Ioo (-(N : ℝ)) N)).card : ℝ) ≤ Z.card := by
      exact_mod_cast Finset.card_filter_le _ _
    nlinarith
  · refine Monotone.directed_le (fun N N' hNN' => Ioc_subset_Ioc ?_ ?_)
    · have : (N : ℝ) ≤ N' := by exact_mod_cast hNN'
      linarith
    · exact_mod_cast hNN'

/-- The variation of `arctan ∘ Q` for a real univariate polynomial `Q` is at most
`π * deg Q`. -/
lemma lintegral_enorm_deriv_arctan_poly_le (Q : Polynomial ℝ) :
    ∫⁻ t, ‖1 / (1 + Q.eval t ^ 2) * Q.derivative.eval t‖ₑ ≤
      ENNReal.ofReal (Real.pi * Q.natDegree) := by
  by_cases hQ : Q.derivative = 0
  · simp [hQ]
  · have hZ : ∀ t, 1 / (1 + Q.eval t ^ 2) * Q.derivative.eval t = 0 →
        t ∈ Q.derivative.roots.toFinset := by
      intro t ht
      have hpos : (0 : ℝ) < 1 + Q.eval t ^ 2 := by positivity
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
      rcases mul_eq_zero.1 ht with h | h
      · exact absurd h (one_div_pos.2 hpos).ne'
      · exact h
    have hd : ∀ t, HasDerivAt (fun s => Real.arctan (Q.eval s))
        (1 / (1 + Q.eval t ^ 2) * Q.derivative.eval t) t :=
      fun t => (Q.hasDerivAt t).arctan
    have hc : Continuous (fun t => 1 / (1 + Q.eval t ^ 2) * Q.derivative.eval t) := by
      refine Continuous.mul ?_ Q.derivative.continuous
      exact continuous_const.div (continuous_const.add (Q.continuous.pow 2))
        (fun t => by positivity)
    have hb : ∀ t, |Real.arctan (Q.eval t)| ≤ Real.pi / 2 := fun t => by
      rw [abs_le]
      exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
    refine (lintegral_enorm_deriv_le_card _ hd hc hb hZ).trans (ENNReal.ofReal_le_ofReal ?_)
    have hcard : Q.derivative.roots.toFinset.card + 1 ≤ Q.natDegree := by
      have h1 : Q.derivative.roots.toFinset.card ≤ Q.derivative.natDegree :=
        (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
      have h2 := Polynomial.natDegree_derivative_le Q
      have h3 : 1 ≤ Q.natDegree := by
        by_contra h
        push Not at h
        exact hQ (Polynomial.derivative_of_natDegree_zero (by omega))
      omega
    have : ((Q.derivative.roots.toFinset.card : ℝ) + 1) ≤ Q.natDegree := by
      exact_mod_cast hcard
    nlinarith [Real.pi_pos]

/-! ### Restriction of a polynomial to an affine line -/

variable {n : ℕ}

/-- The coordinates of the affine line `t ↦ a + t • e`, as polynomials in `t`. -/
noncomputable def linePoly (a e : EuclideanSpace ℝ (Fin n)) (j : Fin n) : Polynomial ℝ :=
  Polynomial.C (e j) * Polynomial.X + Polynomial.C (a j)

/-- The restriction of `p` to the affine line `t ↦ a + t • e`, as a univariate polynomial. -/
noncomputable def lineRestrict (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    Polynomial ℝ :=
  MvPolynomial.aeval (linePoly a e) p

lemma eval_lineRestrict (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (lineRestrict p a e).eval t = MvPolynomial.eval (fun j => (a + t • e) j) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [lineRestrict]
  | add p q hp hq =>
    simp only [lineRestrict, map_add, Polynomial.eval_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p j hp =>
    simp only [lineRestrict, map_mul, Polynomial.eval_mul, MvPolynomial.aeval_X,
      MvPolynomial.eval_X] at hp ⊢
    rw [hp]
    congr 1
    simp [linePoly]
    ring

lemma natDegree_lineRestrict_le (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    (lineRestrict p a e).natDegree ≤ p.totalDegree := by
  have hlin : ∀ j, (linePoly a e j).natDegree ≤ 1 := fun j => Polynomial.natDegree_linear_le
  conv_lhs => rw [lineRestrict, p.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  refine Finset.sum_le_sum (fun i _ => Polynomial.natDegree_pow_le.trans ?_)
  simpa using Nat.mul_le_mul_left (s i) (hlin i)

/-! ### The line variation bound -/

lemma hasDerivAt_arctan_line (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n))
    (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.arctan (MvPolynomial.eval (fun j => (a + u • e) j) p))
      (1 / (1 + (lineRestrict p a e).eval t ^ 2) * (lineRestrict p a e).derivative.eval t) t := by
  have h := ((lineRestrict p a e).hasDerivAt t).arctan
  have heq : (fun u : ℝ => Real.arctan ((lineRestrict p a e).eval u)) =
      fun u : ℝ => Real.arctan (MvPolynomial.eval (fun j => (a + u • e) j) p) := by
    funext u
    rw [eval_lineRestrict]
  rwa [heq] at h

lemma deriv_arctan_line (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    deriv (fun u : ℝ => Real.arctan (MvPolynomial.eval (fun j => (a + u • e) j) p)) t =
      1 / (1 + (lineRestrict p a e).eval t ^ 2) * (lineRestrict p a e).derivative.eval t :=
  (hasDerivAt_arctan_line p a e t).deriv

/-- **Line variation**: the derivative of `t ↦ arctan (p (a + t • e))` has integral of its
absolute value over the whole line at most `π * deg p`. -/
theorem line_variation_lintegral (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ u, ‖deriv (fun u : ℝ => Real.arctan (MvPolynomial.eval (fun j => (a + u • e) j) p)) u‖ₑ ≤
      ENNReal.ofReal (Real.pi * p.totalDegree) := by
  simp only [deriv_arctan_line]
  refine (lintegral_enorm_deriv_arctan_poly_le _).trans (ENNReal.ofReal_le_ofReal ?_)
  have : ((lineRestrict p a e).natDegree : ℝ) ≤ p.totalDegree := by
    exact_mod_cast natDegree_lineRestrict_le p a e
  nlinarith [Real.pi_pos]

/-- The derivative of `t ↦ arctan (p (a + t • e))` is integrable over the line. -/
theorem line_variation_integrable (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun u : ℝ => ‖deriv (fun u : ℝ => Real.arctan
      (MvPolynomial.eval (fun j => (a + u • e) j) p)) u‖) := by
  refine ⟨(measurable_deriv _).norm.aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, enorm_norm]
  exact lt_of_le_of_lt (line_variation_lintegral p a e) ENNReal.ofReal_lt_top

/-- **Line variation** on a bounded interval. -/
theorem line_variation_Icc (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n))
    (s t : ℝ) :
    ∫ u in Icc s t, ‖deriv (fun u : ℝ => Real.arctan
      (MvPolynomial.eval (fun j => (a + u • e) j) p)) u‖ ≤ Real.pi * p.totalDegree := by
  have hnn : 0 ≤ Real.pi * p.totalDegree := by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => norm_nonneg _))
    (measurable_deriv _).norm.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hnn ((setLIntegral_le_lintegral _ _).trans ?_)
  simpa only [ofReal_norm] using line_variation_lintegral p a e

/-- The derivative along the line is the directional derivative of `arctan ∘ p`. -/
theorem line_deriv_eq_fderiv (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n))
    (u : ℝ) :
    deriv (fun u : ℝ => Real.arctan (MvPolynomial.eval (fun j => (a + u • e) j) p)) u =
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        Real.arctan (MvPolynomial.eval (fun j => y j) p)) (a + u • e) e := by
  have hF : Differentiable ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.arctan (MvPolynomial.eval (fun j => y j) p)) :=
    (Real.contDiff_arctan.comp (contDiff_polynomial_eval p)).differentiable (by simp)
  have hline : HasDerivAt (fun u : ℝ => a + u • e) e u := by
    simpa using ((hasDerivAt_id u).smul_const e).const_add a
  exact ((hF (a + u • e)).hasFDerivAt.comp_hasDerivAt u hline).deriv

/-- **Line variation**, in terms of the directional derivative of `arctan ∘ p`. -/
theorem line_variation_fderiv (p : MvPolynomial (Fin n) ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ u : ℝ, ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        Real.arctan (MvPolynomial.eval (fun j => y j) p)) (a + u • e) e‖ₑ ≤
      ENNReal.ofReal (Real.pi * p.totalDegree) := by
  simpa only [line_deriv_eq_fderiv] using line_variation_lintegral p a e

end Submission.Obl.k4_polynomial_variation_tube
