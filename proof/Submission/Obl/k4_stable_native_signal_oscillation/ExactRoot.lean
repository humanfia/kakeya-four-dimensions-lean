import Submission.Obl.k4_stable_native_signal_oscillation.ExactRootBasic
import Submission.Obl.k4_stable_native_signal_oscillation.ExactRootAlgebra

/-!
# Exact-root signal partition

Let `μ` be a probability law on exact simple roots of a quadratic hidden test `P`
(`P = 0`, `K⁻¹ ≤ |∂₃P| ≤ K`), with base density at most `K` and `|S| ≤ K` for a quadratic
signal `S`. Write `P = γ + β t + κ t²/2` and `S = γ' + β' t + κ' t²/2` in the hidden
coordinate `t`, with base polynomials `γ, β, γ', β'`.

* If `κ = 0`, the signal is `N₀ / β²` with `N₀ = β² γ' - β β' γ + κ'/2 γ²`.
* If `κ ≠ 0`, with `u = ∂₃P = β + κ t`, one has `u² = Δ = β² - 2κγ` and `S = M + B u`
  for base polynomials `M, B`; the other root sheet carries `M - B u`, and the product
  `N = M² - B² Δ` of the two branch values is a base polynomial.
  - If `max |B| ≤ 2 K^(c+2)`, the branch expression is directly Lipschitz.
  - Otherwise drop the thin slab `|B| ≤ max|B| / K^c` (small mass by Remez), and use
    `(F(x) - F(y)) (F(y) - F'(x)) = 2 F(y) (M(x) - M(y)) - (N(x) - N(y))`, where the
    other branch `F'(x)` is large: the size of `B` cancels.

Polynomial bounds and Lipschitz constants come from the fixed-degree polynomial control
(Remez through `Submission.k4_algebraic_sheet_remez`), applied to the base of the law.
There are two groups, by the sign of `∂₃P`.
-/

namespace Submission.Obl.k4_stable_native_signal_oscillation

open MvPolynomial MeasureTheory Set Metric
open Submission.Obl.k4_quadratic_atlas_normalization

/-- The base discriminant `β² - 2 κ γ` of the hidden quadratic. -/
noncomputable def erDisc (P : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ :=
  restrictBase (pderiv 3 P) ^ 2 - C (2 * curvature P 3) * restrictBase P

/-- The constant branch coefficient of the signal on the root sheets. -/
noncomputable def erM (P S : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ :=
  restrictBase S -
    C (curvature P 3)⁻¹ * (restrictBase (pderiv 3 P) * restrictBase (pderiv 3 S)) +
    C (curvature S 3 / (2 * curvature P 3 ^ 2)) * (erDisc P + restrictBase (pderiv 3 P) ^ 2)

/-- The coefficient of the hidden derivative in the signal on the root sheets. -/
noncomputable def erB (P S : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ :=
  C (curvature P 3)⁻¹ * restrictBase (pderiv 3 S) -
    C (curvature S 3 / curvature P 3 ^ 2) * restrictBase (pderiv 3 P)

/-- The product of the two branch values. -/
noncomputable def erN (P S : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ :=
  erM P S ^ 2 - erB P S ^ 2 * erDisc P

/-- For a linear hidden test, the signal numerator over `β²`. -/
noncomputable def erN0 (P S : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 3) ℝ :=
  restrictBase (pderiv 3 P) ^ 2 * restrictBase S -
    restrictBase (pderiv 3 P) * restrictBase (pderiv 3 S) * restrictBase P +
    C (curvature S 3 / 2) * restrictBase P ^ 2

lemma erDisc_degree2 (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) :
    (erDisc P).totalDegree ≤ 2 := by
  have h1 := er_totalDegree_restrict_deriv P hP
  have h2 := er_totalDegree_restrict P hP
  unfold erDisc
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_pow _ _).trans (by omega)
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)

section degrees

variable (P S : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (hS : S.totalDegree ≤ 2)
include hP hS

lemma erM_degree2 : (erM P S).totalDegree ≤ 2 := by
  have h1 := er_totalDegree_restrict_deriv P hP
  have h2 := er_totalDegree_restrict P hP
  have h3 := er_totalDegree_restrict_deriv S hS
  have h4 := er_totalDegree_restrict S hS
  have h5 := erDisc_degree2 P hP
  unfold erM
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_sub _ _).trans (max_le h4 ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_mul _ _).trans (by omega)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_add _ _).trans (max_le h5 ?_)
    exact (totalDegree_pow _ _).trans (by omega)

lemma erB_degree1 : (erB P S).totalDegree ≤ 1 := by
  have h1 := er_totalDegree_restrict_deriv P hP
  have h3 := er_totalDegree_restrict_deriv S hS
  unfold erB
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)
  · exact (totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)

lemma erN_degree : (erN P S).totalDegree ≤ 4 := by
  have hM := erM_degree2 P S hP hS
  have hB := erB_degree1 P S hP hS
  have hD := erDisc_degree2 P hP
  unfold erN
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_pow _ _).trans (by omega)
  · refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_pow (erB P S) 2
    omega

lemma erN0_degree : (erN0 P S).totalDegree ≤ 4 := by
  have h1 := er_totalDegree_restrict_deriv P hP
  have h2 := er_totalDegree_restrict P hP
  have h3 := er_totalDegree_restrict_deriv S hS
  have h4 := er_totalDegree_restrict S hS
  unfold erN0
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_pow (restrictBase (pderiv 3 P)) 2
      omega
    · refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_mul (restrictBase (pderiv 3 P)) (restrictBase (pderiv 3 S))
      omega
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    have := totalDegree_pow (restrictBase P) 2
    omega

end degrees

/-- At an exact root with nonzero curvature, the hidden derivative squares to the base
discriminant and the signal is `M + B u`. -/
lemma er_root_point (P S : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (hS : S.totalDegree ≤ 2) (hκ : curvature P 3 ≠ 0) (p : EuclideanSpace ℝ (Fin 4))
    (hroot : eval (fun i => p i) P = 0) :
    eval (fun i => p i) (pderiv 3 P) ^ 2 = eval (fun j => erBase p j) (erDisc P) ∧
    eval (fun i => p i) S = eval (fun j => erBase p j) (erM P S) +
      eval (fun j => erBase p j) (erB P S) * eval (fun i => p i) (pderiv 3 P) := by
  rw [er_eval_expand P hP p] at hroot
  have hid := er_root_identity (κ' := curvature S 3)
    (γ' := eval (fun j => erBase p j) (restrictBase S))
    (β' := eval (fun j => erBase p j) (restrictBase (pderiv 3 S))) hκ hroot
  rw [er_deriv_expand P hP p, er_eval_expand S hS p]
  simp only [erDisc, erM, erB, eval_sub, eval_add, eval_mul, eval_pow, eval_C]
  refine ⟨hid.1, ?_⟩
  rw [hid.2]
  ring

/-- At an exact root of a linear hidden test, the signal is `N₀ / β²`. -/
lemma er_linear_point (P S : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (hS : S.totalDegree ≤ 2) (hκ : curvature P 3 = 0) (p : EuclideanSpace ℝ (Fin 4))
    (hroot : eval (fun i => p i) P = 0) :
    eval (fun i => p i) (pderiv 3 P) = eval (fun j => erBase p j) (restrictBase (pderiv 3 P)) ∧
    eval (fun j => erBase p j) (erN0 P S) =
      eval (fun j => erBase p j) (restrictBase (pderiv 3 P)) ^ 2 * eval (fun i => p i) S := by
  rw [er_eval_expand P hP p, hκ] at hroot
  refine ⟨by rw [er_deriv_expand P hP p, hκ, zero_mul, add_zero], ?_⟩
  rw [er_eval_expand S hS p]
  simp only [erN0, eval_sub, eval_add, eval_mul, eval_pow, eval_C]
  set γ := eval (fun j => erBase p j) (restrictBase P)
  set β := eval (fun j => erBase p j) (restrictBase (pderiv 3 P))
  set β' := eval (fun j => erBase p j) (restrictBase (pderiv 3 S))
  set t := p 3
  linear_combination (-β * β' + curvature S 3 / 2 * (γ - β * t)) * hroot

/-- The exact-root signal partition: a probability law on exact simple roots of a quadratic
hidden test, with bounded base density, has two groups (by the sign of the hidden
derivative), after a reciprocal-polynomial loss, on which the signal is Lipschitz in the
base. -/
theorem er_partition (hPC : PolyControlStatement) (A : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (K : ℝ) (P S : MvPolynomial (Fin 4) ℝ)
      (μ : Measure (EuclideanSpace ℝ (Fin 4))), 2 ≤ K → P.totalDegree ≤ 2 →
      S.totalDegree ≤ 2 → IsProbabilityMeasure μ →
      Measure.map erBase μ ≤ ENNReal.ofReal K • volume →
      (∀ᵐ p ∂μ, ‖erBase p‖ ≤ K ∧ eval (fun i => p i) P = 0 ∧
        K⁻¹ ≤ |eval (fun i => p i) (pderiv 3 P)| ∧ |eval (fun i => p i) (pderiv 3 P)| ≤ K ∧
        |eval (fun i => p i) S| ≤ K) →
      ∃ (n : ℕ) (E : Fin n → Set (EuclideanSpace ℝ (Fin 4))), (n : ℝ) ≤ K ^ C ∧
        (∀ i, MeasurableSet (E i)) ∧ (∀ i j, i ≠ j → Disjoint (E i) (E j)) ∧
        μ (⋃ i, E i)ᶜ ≤ ENNReal.ofReal ((K ^ A)⁻¹) ∧
        ∀ i p, p ∈ E i → ∀ q, q ∈ E i →
          |eval (fun j => p j) S - eval (fun j => q j) S| ≤ K ^ C * ‖erBase p - erBase q‖ := by
  obtain ⟨N, hN1, hctl⟩ := er_control hPC 4
  obtain ⟨c, hslab⟩ := er_slab hPC 4 A
  refine ⟨N + c + 10, by omega, ?_⟩
  intro K P S μ hK hP hS hprob hd hae
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hpow : ∀ a b : ℕ, a ≤ b → K ^ a ≤ K ^ b := fun a b h => pow_le_pow_right₀ hK1 h
  have hcv : ∀ Q : MvPolynomial (Fin 4) ℝ,
      Continuous (fun p : EuclideanSpace ℝ (Fin 4) => eval (fun i => p i) Q) :=
    fun Q => (MvPolynomial.continuous_eval Q).comp (by fun_prop)
  let G : Set (EuclideanSpace ℝ (Fin 4)) := {p | ‖erBase p‖ ≤ K ∧ eval (fun i => p i) P = 0 ∧
    K⁻¹ ≤ |eval (fun i => p i) (pderiv 3 P)| ∧ |eval (fun i => p i) (pderiv 3 P)| ≤ K ∧
    |eval (fun i => p i) S| ≤ K}
  have hGm : MeasurableSet G := by
    refine (measurableSet_le measurable_erBase.norm measurable_const).inter ?_
    refine (measurableSet_eq_fun (hcv P).measurable measurable_const).inter ?_
    refine (measurableSet_le measurable_const (hcv _).abs.measurable).inter ?_
    exact (measurableSet_le (hcv _).abs.measurable measurable_const).inter
      (measurableSet_le (hcv S).abs.measurable measurable_const)
  have hG : ∀ᵐ p ∂μ, p ∈ G := hae
  have hGball : ∀ p ∈ G, ‖erBase p‖ ≤ K := fun p hp => hp.1
  let u : EuclideanSpace ℝ (Fin 4) → ℝ := fun p => eval (fun i => p i) (pderiv 3 P)
  have hu : Measurable u := (hcv _).measurable
  have hu0 : ∀ p ∈ G, u p ≠ 0 := by
    intro p hp h
    have h1 : K⁻¹ ≤ |u p| := hp.2.2.1
    rw [h, abs_zero] at h1
    exact absurd h1 (not_le.mpr (inv_pos.mpr hK0))
  have hbase3 : ∀ p ∈ G, ‖erBase p‖ ≤ 3 * K := fun p hp => by linarith [hp.1]
  suffices hmain : ∃ (g : EuclideanSpace ℝ (Fin 4) → ℝ) (b L : ℝ), Measurable g ∧
      μ (G ∩ {p | |g p| ≤ b}) ≤ ENNReal.ofReal ((K ^ A)⁻¹) ∧ L ≤ K ^ (N + c + 10) ∧
      ∀ p ∈ G, ∀ q ∈ G, b < |g p| → b < |g q| → 0 < u p * u q →
        |eval (fun j => p j) S - eval (fun j => q j) S| ≤ L * ‖erBase p - erBase q‖ by
    obtain ⟨g, b, L, hg, hmass, hL, hlip⟩ := hmain
    obtain ⟨E, hEm, hEd, hEmass, hElip⟩ := er_package μ G hGm hG u hu hu0 g hg b
      (fun p => eval (fun j => p j) S) L _ hmass hlip
    refine ⟨2, E, ?_, hEm, hEd, hEmass, ?_⟩
    · calc ((2 : ℕ) : ℝ) = 2 := by norm_num
        _ ≤ K := hK
        _ = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ (N + c + 10) := hpow _ _ (by omega)
    · intro i p hp q hq
      exact (hElip i p hp q hq).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have htriv : μ (G ∩ {p | |(fun _ : EuclideanSpace ℝ (Fin 4) => (0 : ℝ)) p| ≤ -1}) ≤
      ENNReal.ofReal ((K ^ A)⁻¹) := by
    have h : G ∩ {p | |(fun _ : EuclideanSpace ℝ (Fin 4) => (0 : ℝ)) p| ≤ -1} = ∅ := by
      ext p
      simp only [abs_zero, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro _
      norm_num
    rw [h, measure_empty]
    exact bot_le
  have hKN : 0 ≤ K ^ N := by positivity
  by_cases hκ : curvature P 3 = 0
  · -- a linear hidden test
    have hlin : ∀ p ∈ G, u p = eval (fun j => erBase p j) (restrictBase (pderiv 3 P)) ∧
        eval (fun j => erBase p j) (erN0 P S) =
          eval (fun j => erBase p j) (restrictBase (pderiv 3 P)) ^ 2 * eval (fun i => p i) S :=
      fun p hp => er_linear_point P S hP hS hκ p hp.2.1
    have hβ := hctl K hK μ hd G hG hGball (restrictBase (pderiv 3 P))
      ((er_totalDegree_restrict_deriv P hP).trans (by norm_num)) K hK0.le
      (fun p hp => by rw [← (hlin p hp).1]; exact hp.2.2.2.1)
    have hN0 := hctl K hK μ hd G hG hGball (erN0 P S) (erN0_degree P S hP hS) (K ^ 3)
      (by positivity) (fun p hp => by
        rw [(hlin p hp).2, abs_mul, abs_pow, ← (hlin p hp).1]
        calc |u p| ^ 2 * |eval (fun i => p i) S| ≤ K ^ 2 * K :=
              mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hp.2.2.2.1 2) hp.2.2.2.2
                (abs_nonneg _) (by positivity)
          _ = K ^ 3 := by ring)
    refine ⟨fun _ => 0, -1, K ^ 2 * (K ^ N * K ^ 3) + 2 * K ^ 4 * (K ^ N * K),
      measurable_const, htriv, ?_, ?_⟩
    · have h1 : K ^ 2 * (K ^ N * K ^ 3) + 2 * K ^ 4 * (K ^ N * K) = 3 * K ^ (N + 5) := by ring
      rw [h1]
      calc 3 * K ^ (N + 5) ≤ K ^ 2 * K ^ (N + 5) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith
        _ = K ^ (N + 7) := by ring
        _ ≤ K ^ (N + c + 10) := hpow _ _ (by omega)
    · intro p hp q hq _ _ _
      have hβp : K⁻¹ ≤ |eval (fun j => erBase p j) (restrictBase (pderiv 3 P))| := by
        rw [← (hlin p hp).1]; exact hp.2.2.1
      have hβp' : |eval (fun j => erBase p j) (restrictBase (pderiv 3 P))| ≤ K := by
        rw [← (hlin p hp).1]; exact hp.2.2.2.1
      have hβq' : |eval (fun j => erBase q j) (restrictBase (pderiv 3 P))| ≤ K := by
        rw [← (hlin q hq).1]; exact hq.2.2.2.1
      exact er_linear_case_bound hK0 hβp hβp' hβq' (hlin p hp).2 (hlin q hq).2 hq.2.2.2.2
        (hN0.2 _ _ (hbase3 p hp) (hbase3 q hq)) (hβ.2 _ _ (hbase3 p hp) (hbase3 q hq))
        (norm_nonneg _) (by positivity) (by positivity)
  · -- a genuinely quadratic hidden test: two root sheets
    have hpt : ∀ p ∈ G, u p ^ 2 = eval (fun j => erBase p j) (erDisc P) ∧
        eval (fun i => p i) S = eval (fun j => erBase p j) (erM P S) +
          eval (fun j => erBase p j) (erB P S) * u p :=
      fun p hp => er_root_point P S hP hS hκ p hp.2.1
    obtain ⟨x₀, hx₀, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) K).exists_isMaxOn
      (nonempty_closedBall.mpr hK0.le) (er_continuous_eval3 (erB P S)).abs.continuousOn
    set LB := |eval (fun i => x₀ i) (erB P S)| with hLB
    have hx₀K : ‖x₀‖ ≤ K := by simpa [mem_closedBall, dist_zero_right] using hx₀
    have hBle : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ K →
        |eval (fun i => x i) (erB P S)| ≤ LB := fun x hx =>
      hmax (by simpa [mem_closedBall, dist_zero_right] using hx)
    have hLB0 : 0 ≤ LB := abs_nonneg _
    have hMbound : ∀ p ∈ G, |eval (fun j => erBase p j) (erM P S)| ≤ K + LB * K := by
      intro p hp
      have h1 : eval (fun j => erBase p j) (erM P S) =
          eval (fun i => p i) S - eval (fun j => erBase p j) (erB P S) * u p := by
        rw [(hpt p hp).2]; ring
      rw [h1]
      calc _ ≤ |eval (fun i => p i) S| + |eval (fun j => erBase p j) (erB P S) * u p| :=
            abs_sub _ _
        _ ≤ K + LB * K := by
          rw [abs_mul]
          exact add_le_add hp.2.2.2.2
            (mul_le_mul (hBle _ hp.1) hp.2.2.2.1 (abs_nonneg _) hLB0)
    by_cases hsmall : LB ≤ 2 * K ^ (c + 2)
    · -- close branches
      set L₀ := 2 * K ^ (c + 2) with hL₀
      have hL₀0 : 0 ≤ L₀ := by positivity
      have hΔ := hctl K hK μ hd G hG hGball (erDisc P) ((erDisc_degree2 P hP).trans (by norm_num))
        (K ^ 2) (by positivity) (fun p hp => by
          rw [← (hpt p hp).1, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hp.2.2.2.1 2)
      have hB := hctl K hK μ hd G hG hGball (erB P S)
        ((erB_degree1 P S hP hS).trans (by norm_num)) L₀ hL₀0
        (fun p hp => (hBle _ hp.1).trans hsmall)
      have hM := hctl K hK μ hd G hG hGball (erM P S)
        ((erM_degree2 P S hP hS).trans (by norm_num)) (K + L₀ * K) (by positivity)
        (fun p hp => (hMbound p hp).trans (by gcongr))
      refine ⟨fun _ => 0, -1, K ^ N * (K + L₀ * K) + K ^ N * L₀ * K + L₀ * K * (K ^ N * K ^ 2) / 2,
        measurable_const, htriv, ?_, ?_⟩
      · have h1 : K ^ N * (K + L₀ * K) + K ^ N * L₀ * K + L₀ * K * (K ^ N * K ^ 2) / 2 =
            K ^ (N + 1) + 4 * K ^ (N + c + 3) + K ^ (N + c + 5) := by
          rw [hL₀]; ring
        rw [h1]
        have h2 : K ^ (N + 1) ≤ K ^ (N + c + 5) := hpow _ _ (by omega)
        have h3 : 4 * K ^ (N + c + 3) ≤ K ^ (N + c + 5) := by
          have : K ^ (N + c + 5) = K ^ 2 * K ^ (N + c + 3) := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
        calc K ^ (N + 1) + 4 * K ^ (N + c + 3) + K ^ (N + c + 5) ≤ 3 * K ^ (N + c + 5) := by
              linarith
          _ ≤ K ^ 2 * K ^ (N + c + 5) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              nlinarith
          _ = K ^ (N + c + 7) := by ring
          _ ≤ K ^ (N + c + 10) := hpow _ _ (by omega)
      · intro p hp q hq _ _ hsign
        have hSp := (hpt p hp).2
        have hSq := (hpt q hq).2
        rw [hSp, hSq]
        have hLD : |u p ^ 2 - u q ^ 2| ≤ K ^ N * K ^ 2 * ‖erBase p - erBase q‖ := by
          rw [(hpt p hp).1, (hpt q hq).1]
          exact hΔ.2 _ _ (hbase3 p hp) (hbase3 q hq)
        have h := er_small_branch_bound hK0 hp.2.2.1 hq.2.2.1 hp.2.2.2.1 hsign
          ((hBle _ hq.1).trans hsmall) (hM.2 _ _ (hbase3 p hp) (hbase3 q hq))
          (hB.2 _ _ (hbase3 p hp) (hbase3 q hq)) hLD (norm_nonneg _) hL₀0 (by positivity)
        convert h using 2
    · -- separated branches: trim a thin slab of the branch coefficient
      push Not at hsmall
      have hLBpos : 0 < LB := lt_of_le_of_lt (by positivity) hsmall
      have hcKpos : 0 < K ^ c := by positivity
      have hN := hctl K hK μ hd G hG hGball (erN P S) (erN_degree P S hP hS)
        ((K + 2 * LB * K) * K) (by positivity) (fun p hp => by
          have h1 : eval (fun j => erBase p j) (erN P S) =
              (eval (fun i => p i) S - 2 * (eval (fun j => erBase p j) (erB P S) * u p)) *
                eval (fun i => p i) S := by
            simp only [erN, eval_sub, eval_mul, eval_pow]
            rw [← (hpt p hp).1, (hpt p hp).2]
            ring
          rw [h1, abs_mul]
          apply mul_le_mul _ hp.2.2.2.2 (abs_nonneg _) (by positivity)
          calc _ ≤ |eval (fun i => p i) S| + |2 * (eval (fun j => erBase p j) (erB P S) * u p)| :=
                abs_sub _ _
            _ ≤ K + 2 * LB * K := by
              rw [abs_mul, abs_mul, abs_two]
              have := mul_le_mul (hBle _ hp.1) hp.2.2.2.1 (abs_nonneg _) hLB0
              linarith [hp.2.2.2.2])
      have hM := hctl K hK μ hd G hG hGball (erM P S)
        ((erM_degree2 P S hP hS).trans (by norm_num)) (K + LB * K) (by positivity) hMbound
      set ℓ := LB / K ^ (c + 1) with hℓ
      have hℓpos : 0 < ℓ := by positivity
      refine ⟨fun p => eval (fun j => erBase p j) (erB P S), LB / K ^ c,
        (2 * K * (K ^ N * (K + LB * K)) + K ^ N * ((K + 2 * LB * K) * K)) / ℓ,
        (er_continuous_eval3 (erB P S)).measurable.comp measurable_erBase, ?_, ?_, ?_⟩
      · calc μ (G ∩ {p | |eval (fun j => erBase p j) (erB P S)| ≤ LB / K ^ c}) ≤
            μ (erBase ⁻¹' {x | ‖x‖ ≤ K ∧ |eval (fun i => x i) (erB P S)| ≤ LB / K ^ c}) := by
              apply measure_mono
              intro p hp
              exact ⟨hp.1.1, hp.2⟩
          _ ≤ ENNReal.ofReal ((K ^ A)⁻¹) :=
              hslab K hK μ hd (erB P S) ((erB_degree1 P S hP hS).trans (by norm_num)) x₀ hx₀K
                hBle hLBpos
      · have h1 : (2 * K * (K ^ N * (K + LB * K)) + K ^ N * ((K + 2 * LB * K) * K)) / ℓ =
            K ^ (N + c + 1) * (3 * K ^ 2 / LB + 4 * K ^ 2) := by
          rw [hℓ]
          field_simp
          ring
        rw [h1]
        have h2 : 3 * K ^ 2 / LB ≤ K ^ 2 := by
          rw [div_le_iff₀ hLBpos]
          have : 3 ≤ LB := by
            have h4 : (4 : ℝ) ≤ K ^ (c + 2) := by
              calc (4 : ℝ) = 2 ^ 2 := by norm_num
                _ ≤ K ^ 2 := pow_le_pow_left₀ (by norm_num) hK 2
                _ ≤ K ^ (c + 2) := hpow _ _ (by omega)
            linarith
          nlinarith [sq_nonneg K]
        calc K ^ (N + c + 1) * (3 * K ^ 2 / LB + 4 * K ^ 2) ≤ K ^ (N + c + 1) * (5 * K ^ 2) := by
              gcongr; linarith
          _ ≤ K ^ (N + c + 1) * (K ^ 3 * K ^ 2) := by
              gcongr
              nlinarith
          _ = K ^ (N + c + 6) := by ring
          _ ≤ K ^ (N + c + 10) := hpow _ _ (by omega)
      · intro p hp q hq hbp _ _
        have hSp := (hpt p hp).2
        have hSq := (hpt q hq).2
        have hSpK : |eval (fun j => erBase p j) (erM P S) +
            eval (fun j => erBase p j) (erB P S) * u p| ≤ K := by rw [← hSp]; exact hp.2.2.2.2
        have hSqK : |eval (fun j => erBase q j) (erM P S) +
            eval (fun j => erBase q j) (erB P S) * u q| ≤ K := by rw [← hSq]; exact hq.2.2.2.2
        have hsep : ℓ ≤ 2 * |eval (fun j => erBase p j) (erB P S)| * |u p| - 2 * K := by
          have h1 : LB / K ^ c * K⁻¹ ≤ |eval (fun j => erBase p j) (erB P S)| * |u p| :=
            mul_le_mul hbp.le hp.2.2.1 (by positivity) (abs_nonneg _)
          have h2 : LB / K ^ c * K⁻¹ = ℓ * 1 := by rw [hℓ]; field_simp; ring
          have h3 : 2 * K ≤ ℓ := by
            rw [hℓ, le_div_iff₀ (by positivity)]
            have : 2 * K * K ^ (c + 1) = 2 * K ^ (c + 2) := by ring
            linarith
          nlinarith
        have hLN : |(eval (fun j => erBase p j) (erM P S) ^ 2 -
              eval (fun j => erBase p j) (erB P S) ^ 2 * u p ^ 2) -
            (eval (fun j => erBase q j) (erM P S) ^ 2 -
              eval (fun j => erBase q j) (erB P S) ^ 2 * u q ^ 2)| ≤
            K ^ N * ((K + 2 * LB * K) * K) * ‖erBase p - erBase q‖ := by
          have h := hN.2 _ _ (hbase3 p hp) (hbase3 q hq)
          simp only [erN, eval_sub, eval_mul, eval_pow] at h
          rw [(hpt p hp).1, (hpt q hq).1]
          exact h
        have h := er_separated_branch_bound hK0 hSpK hSqK hsep hℓpos
          (hM.2 _ _ (hbase3 p hp) (hbase3 q hq)) hLN
        rw [hSp, hSq]
        calc _ ≤ (2 * K * (K ^ N * (K + LB * K)) + K ^ N * ((K + 2 * LB * K) * K)) *
              ‖erBase p - erBase q‖ / ℓ := h
          _ = _ := by ring

end Submission.Obl.k4_stable_native_signal_oscillation
