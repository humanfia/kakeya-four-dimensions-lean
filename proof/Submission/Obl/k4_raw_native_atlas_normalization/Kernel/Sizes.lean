/- Adapted from this LOT tree, obligation o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758,
   Submission/Lib/K4ChartLifting/Sizes.lean. Original provenance is retained below. -/
import Submission.Obl.k4_raw_native_atlas_normalization.Kernel.NormFormat
import Submission.Obl.k4_raw_native_atlas_normalization.Kernel.Bounds

/-!
# Size bounds for normalized data

Evaluation bounds by the `ℓ¹` coefficient norm, and explicit `ℓ¹` bounds for the
normalization polynomials (`normBound`) and the inverse substitution (`unsubstBound`),
giving bounds for normalized coefficients and normalized test coefficients.
-/
namespace Submission.Obl.k4_raw_native_atlas_normalization.Kernel
open MvPolynomial

theorem abs_eval_le_coeffL1 {σ : Type*} (p : MvPolynomial σ ℝ) (x : σ → ℝ) (R : ℝ)
    (hR : 1 ≤ R) (hx : ∀ i, |x i| ≤ R) :
    |eval x p| ≤ coeffL1 p * R ^ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [coeffL1, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  rw [eval_monomial, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [Finsupp.prod, Finset.abs_prod]
  calc ∏ i ∈ m.support, |x i ^ m i| ≤ ∏ i ∈ m.support, R ^ m i := by
        apply Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
        intro i _
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _
    _ = R ^ (m.sum fun _ e => e) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ R ^ p.totalDegree := pow_le_pow_right₀ hR (le_totalDegree hm)

/-- For a polynomial of degree at most one. -/
theorem abs_eval_le_of_deg_le_one {σ : Type*} (p : MvPolynomial σ ℝ) (hp : p.totalDegree ≤ 1)
    (x : σ → ℝ) (R : ℝ) (hR : 1 ≤ R) (hx : ∀ i, |x i| ≤ R) :
    |eval x p| ≤ coeffL1 p * R := by
  refine (abs_eval_le_coeffL1 p x R hR hx).trans ?_
  apply mul_le_mul_of_nonneg_left _ (coeffL1_nonneg _)
  calc R ^ p.totalDegree ≤ R ^ 1 := pow_le_pow_right₀ hR hp
    _ = R := pow_one R

namespace Frame
variable (F : Frame)

/-- A common bound for the `ℓ¹` norms of the normalization polynomials. -/
noncomputable def normBound : ℝ :=
  (1 + ∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'|) * (1 + |F.t₀|) * (1 + |F.q|) *
    (1 + ‖F.c‖ + ‖F.u‖)

theorem one_le_normBound : 1 ≤ F.normBound := by
  unfold normBound
  have h1 : 1 ≤ 1 + ∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'| := by
    have : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have h2 : 1 ≤ 1 + |F.t₀| := by have := abs_nonneg F.t₀; linarith
  have h3 : 1 ≤ 1 + |F.q| := by have := abs_nonneg F.q; linarith
  have h4 : 1 ≤ 1 + ‖F.c‖ + ‖F.u‖ := by have := norm_nonneg F.c; have := norm_nonneg F.u; linarith
  calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

theorem coeffL1_normCoeffPoly_le (e : Fin 6) : coeffL1 (F.normCoeffPoly e) ≤ F.normBound := by
  set S := ∑ e : Fin 2, ∑ e' : Fin 2, |F.D⁻¹ e e'| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum : S = |F.D⁻¹ 0 0| + |F.D⁻¹ 0 1| + (|F.D⁻¹ 1 0| + |F.D⁻¹ 1 1|) := by
    simp [hS, Fin.sum_univ_two]
  have hc0 := plane_abs_le_norm F.c 0
  have hc1 := plane_abs_le_norm F.c 1
  have hu0 := plane_abs_le_norm F.u 0
  have hu1 := plane_abs_le_norm F.u 1
  have ht := abs_nonneg F.t₀
  have hq := abs_nonneg F.q
  have hcn := norm_nonneg F.c
  have hun := norm_nonneg F.u
  have hX : ∀ i : Fin 6, coeffL1 (X i : MvPolynomial (Fin 6) ℝ) = 1 := fun i => coeffL1_X i
  -- the affine building blocks
  have ha : ∀ (i j : Fin 6) (c u : ℝ), coeffL1 (X i + C F.t₀ * X j - C c - C (F.t₀ * u) :
      MvPolynomial (Fin 6) ℝ) ≤ 1 + |F.t₀| + |c| + |F.t₀| * |u| := by
    intro i j c u
    calc _ ≤ coeffL1 (X i + C F.t₀ * X j - C c : MvPolynomial (Fin 6) ℝ) +
          coeffL1 (C (F.t₀ * u) : MvPolynomial (Fin 6) ℝ) := coeffL1_sub_le _ _
      _ ≤ (coeffL1 (X i + C F.t₀ * X j : MvPolynomial (Fin 6) ℝ) +
          coeffL1 (C c : MvPolynomial (Fin 6) ℝ)) + |F.t₀ * u| := by
          gcongr
          · exact coeffL1_sub_le _ _
          · rw [coeffL1_C]
      _ ≤ ((coeffL1 (X i : MvPolynomial (Fin 6) ℝ) +
          |F.t₀| * coeffL1 (X j : MvPolynomial (Fin 6) ℝ)) + |c|) + |F.t₀ * u| := by
          gcongr
          · exact (coeffL1_add_le _ _).trans (add_le_add le_rfl (coeffL1_C_mul_le _ _))
          · rw [coeffL1_C]
      _ = 1 + |F.t₀| + |c| + |F.t₀| * |u| := by rw [hX, hX, abs_mul]; ring
  have hb : ∀ (i : Fin 6) (u : ℝ), coeffL1 (X i - C u : MvPolynomial (Fin 6) ℝ) ≤ 1 + |u| := by
    intro i u
    refine (coeffL1_sub_le _ _).trans ?_
    rw [hX, coeffL1_C]
  have hrow : ∀ (a b : ℝ) (P Q : MvPolynomial (Fin 6) ℝ) (x y : ℝ), coeffL1 P ≤ x →
      coeffL1 Q ≤ y → coeffL1 (C a * P + C b * Q) ≤ |a| * x + |b| * y := by
    intro a b P Q x y hP hQ
    refine (coeffL1_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (coeffL1_C_mul_le _ _).trans (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
    · exact (coeffL1_C_mul_le _ _).trans (mul_le_mul_of_nonneg_left hQ (abs_nonneg _))
  have hbig : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ S → (1 + |F.t₀|) * (1 + ‖F.c‖ + ‖F.u‖) * (x + y)
      ≤ F.normBound := by
    intro x y hx hy hxy
    unfold normBound
    have h1 : (1 + |F.t₀|) * (1 + ‖F.c‖ + ‖F.u‖) * (x + y) ≤
        (1 + |F.t₀|) * (1 + ‖F.c‖ + ‖F.u‖) * (1 + S) := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (1 + |F.t₀|) * (1 + ‖F.c‖ + ‖F.u‖) * (1 + S) ≤
        (1 + S) * (1 + |F.t₀|) * (1 + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      have : 0 ≤ (1 + S) * (1 + |F.t₀|) * (1 + ‖F.c‖ + ‖F.u‖) := by positivity
      nlinarith
    linarith
  have hmix : ∀ (a b c₀ c₁ u₀ u₁ : ℝ), |c₀| ≤ ‖F.c‖ → |c₁| ≤ ‖F.c‖ → |u₀| ≤ ‖F.u‖ →
      |u₁| ≤ ‖F.u‖ → |a| * (1 + |F.t₀| + |c₀| + |F.t₀| * |u₀|) +
        |b| * (1 + |F.t₀| + |c₁| + |F.t₀| * |u₁|) ≤
      (1 + |F.t₀|) * (1 + ‖F.c‖ + ‖F.u‖) * (|a| + |b|) := by
    intro a b c₀ c₁ u₀ u₁ h1 h2 h3 h4
    have k0 : 1 + |F.t₀| + |c₀| + |F.t₀| * |u₀| ≤ (1 + |F.t₀|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      nlinarith [abs_nonneg c₀, abs_nonneg u₀]
    have k1 : 1 + |F.t₀| + |c₁| + |F.t₀| * |u₁| ≤ (1 + |F.t₀|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      nlinarith [abs_nonneg c₁, abs_nonneg u₁]
    nlinarith [abs_nonneg a, abs_nonneg b]
  fin_cases e
  · show coeffL1 (C (F.D⁻¹ 0 0) * (X 0 + C F.t₀ * X 3 - C (F.c 0) - C (F.t₀ * F.u 0)) +
      C (F.D⁻¹ 0 1) * (X 1 + C F.t₀ * X 4 - C (F.c 1) - C (F.t₀ * F.u 1))) ≤ F.normBound
    refine (hrow _ _ _ _ _ _ (ha _ _ _ _) (ha _ _ _ _)).trans ((hmix _ _ _ _ _ _ hc0 hc1 hu0 hu1).trans
      (hbig _ _ (abs_nonneg _) (abs_nonneg _) ?_))
    rw [hsum]; linarith [abs_nonneg (F.D⁻¹ 1 0), abs_nonneg (F.D⁻¹ 1 1)]
  · show coeffL1 (C (F.D⁻¹ 1 0) * (X 0 + C F.t₀ * X 3 - C (F.c 0) - C (F.t₀ * F.u 0)) +
      C (F.D⁻¹ 1 1) * (X 1 + C F.t₀ * X 4 - C (F.c 1) - C (F.t₀ * F.u 1))) ≤ F.normBound
    refine (hrow _ _ _ _ _ _ (ha _ _ _ _) (ha _ _ _ _)).trans ((hmix _ _ _ _ _ _ hc0 hc1 hu0 hu1).trans
      (hbig _ _ (abs_nonneg _) (abs_nonneg _) ?_))
    rw [hsum]; linarith [abs_nonneg (F.D⁻¹ 0 0), abs_nonneg (F.D⁻¹ 0 1)]
  · show coeffL1 (X 2 + C F.t₀ * X 5 : MvPolynomial (Fin 6) ℝ) ≤ F.normBound
    refine ((coeffL1_add_le _ _).trans (add_le_add le_rfl (coeffL1_C_mul_le _ _))).trans ?_
    rw [hX, hX, mul_one]
    unfold normBound
    have : 1 ≤ (1 + S) * (1 + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      have a1 : 1 ≤ 1 + S := by linarith
      have a2 : 1 ≤ 1 + |F.q| := by linarith
      have a3 : 1 ≤ 1 + ‖F.c‖ + ‖F.u‖ := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    nlinarith
  · show coeffL1 (C F.q * (C (F.D⁻¹ 0 0) * (X 3 - C (F.u 0)) + C (F.D⁻¹ 0 1) * (X 4 - C (F.u 1))))
      ≤ F.normBound
    refine (coeffL1_C_mul_le _ _).trans ?_
    have k := hrow (F.D⁻¹ 0 0) (F.D⁻¹ 0 1) _ _ _ _ (hb 3 (F.u 0)) (hb 4 (F.u 1))
    have k2 : |F.D⁻¹ 0 0| * (1 + |F.u 0|) + |F.D⁻¹ 0 1| * (1 + |F.u 1|) ≤
        (|F.D⁻¹ 0 0| + |F.D⁻¹ 0 1|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      nlinarith [abs_nonneg (F.D⁻¹ 0 0), abs_nonneg (F.D⁻¹ 0 1)]
    have k3 : |F.D⁻¹ 0 0| + |F.D⁻¹ 0 1| ≤ 1 + S := by
      rw [hsum]; linarith [abs_nonneg (F.D⁻¹ 1 0), abs_nonneg (F.D⁻¹ 1 1)]
    unfold normBound
    have : |F.q| * ((|F.D⁻¹ 0 0| + |F.D⁻¹ 0 1|) * (1 + ‖F.c‖ + ‖F.u‖)) ≤
        (1 + S) * (1 + |F.t₀|) * (1 + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      have hX0 : 0 ≤ 1 + ‖F.c‖ + ‖F.u‖ := by positivity
      calc |F.q| * ((|F.D⁻¹ 0 0| + |F.D⁻¹ 0 1|) * (1 + ‖F.c‖ + ‖F.u‖))
          ≤ (1 + |F.q|) * ((1 + S) * (1 + ‖F.c‖ + ‖F.u‖)) := by
            apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right k3 hX0)
              (by positivity) (by positivity)
        _ = (1 + S) * 1 * (1 + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by ring
        _ ≤ (1 + S) * (1 + |F.t₀|) * (1 + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by
            gcongr; linarith
    nlinarith [mul_le_mul_of_nonneg_left (k.trans k2) hq]
  · show coeffL1 (C F.q * (C (F.D⁻¹ 1 0) * (X 3 - C (F.u 0)) + C (F.D⁻¹ 1 1) * (X 4 - C (F.u 1))))
      ≤ F.normBound
    refine (coeffL1_C_mul_le _ _).trans ?_
    have k := hrow (F.D⁻¹ 1 0) (F.D⁻¹ 1 1) _ _ _ _ (hb 3 (F.u 0)) (hb 4 (F.u 1))
    have k2 : |F.D⁻¹ 1 0| * (1 + |F.u 0|) + |F.D⁻¹ 1 1| * (1 + |F.u 1|) ≤
        (|F.D⁻¹ 1 0| + |F.D⁻¹ 1 1|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      nlinarith [abs_nonneg (F.D⁻¹ 1 0), abs_nonneg (F.D⁻¹ 1 1)]
    have k3 : |F.D⁻¹ 1 0| + |F.D⁻¹ 1 1| ≤ 1 + S := by
      rw [hsum]; linarith [abs_nonneg (F.D⁻¹ 0 0), abs_nonneg (F.D⁻¹ 0 1)]
    unfold normBound
    have : |F.q| * ((|F.D⁻¹ 1 0| + |F.D⁻¹ 1 1|) * (1 + ‖F.c‖ + ‖F.u‖)) ≤
        (1 + S) * (1 + |F.t₀|) * (1 + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      have hX0 : 0 ≤ 1 + ‖F.c‖ + ‖F.u‖ := by positivity
      calc |F.q| * ((|F.D⁻¹ 1 0| + |F.D⁻¹ 1 1|) * (1 + ‖F.c‖ + ‖F.u‖))
          ≤ (1 + |F.q|) * ((1 + S) * (1 + ‖F.c‖ + ‖F.u‖)) := by
            apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right k3 hX0)
              (by positivity) (by positivity)
        _ = (1 + S) * 1 * (1 + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by ring
        _ ≤ (1 + S) * (1 + |F.t₀|) * (1 + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by
            gcongr; linarith
    nlinarith [mul_le_mul_of_nonneg_left (k.trans k2) hq]
  · show coeffL1 (C F.q * X 5 : MvPolynomial (Fin 6) ℝ) ≤ F.normBound
    refine (coeffL1_C_mul_le _ _).trans ?_
    rw [hX, mul_one]
    unfold normBound
    have : 1 ≤ (1 + S) * (1 + |F.t₀|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      have a1 : 1 ≤ 1 + S := by linarith
      have a2 : 1 ≤ 1 + |F.t₀| := by linarith
      have a3 : 1 ≤ 1 + ‖F.c‖ + ‖F.u‖ := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    nlinarith

theorem abs_normCoeff_le (l : Fin 6 → ℝ) (R : ℝ) (hR : 1 ≤ R) (hl : ∀ i, |l i| ≤ R) (e : Fin 6) :
    |F.normCoeff l e| ≤ F.normBound * R := by
  have := abs_eval_le_of_deg_le_one (F.normCoeffPoly e) (F.totalDegree_normCoeffPoly_le e) l R hR hl
  rw [← congrFun (F.eval_normCoeffPoly l) e]
  exact this.trans (mul_le_mul_of_nonneg_right (F.coeffL1_normCoeffPoly_le e) (by linarith))

/-- A common bound for the `ℓ¹` norms of the inverse substitution polynomials. -/
noncomputable def unsubstBound : ℝ :=
  (1 + |F.t₀| + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) * (1 + ∑ e : Fin 2, ∑ e' : Fin 2, |F.D e e'|)

theorem one_le_unsubstBound : 1 ≤ F.unsubstBound := by
  unfold unsubstBound
  have h1 : 1 ≤ 1 + |F.t₀| + |F.q| := by have := abs_nonneg F.t₀; have := abs_nonneg F.q; linarith
  have h2 : 1 ≤ 1 + ‖F.c‖ + ‖F.u‖ := by have := norm_nonneg F.c; have := norm_nonneg F.u; linarith
  have h3 : 1 ≤ 1 + ∑ e : Fin 2, ∑ e' : Fin 2, |F.D e e'| := by
    have : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |F.D e e'| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

theorem coeffL1_unsubst_le (i : Fin 4) : coeffL1 (F.unsubst i) ≤ F.unsubstBound := by
  set S := ∑ e : Fin 2, ∑ e' : Fin 2, |F.D e e'| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsum : S = |F.D 0 0| + |F.D 0 1| + (|F.D 1 0| + |F.D 1 1|) := by
    simp [hS, Fin.sum_univ_two]
  have hc0 := plane_abs_le_norm F.c 0
  have hc1 := plane_abs_le_norm F.c 1
  have hu0 := plane_abs_le_norm F.u 0
  have hu1 := plane_abs_le_norm F.u 1
  have ht := abs_nonneg F.t₀
  have hq := abs_nonneg F.q
  have hcn := norm_nonneg F.c
  have hun := norm_nonneg F.u
  have hX : ∀ i : Fin 4, coeffL1 (X i : MvPolynomial (Fin 4) ℝ) = 1 := fun i => coeffL1_X i
  have htime : coeffL1 (C F.t₀ + C F.q * X 0 : MvPolynomial (Fin 4) ℝ) ≤ |F.t₀| + |F.q| := by
    refine (coeffL1_add_le _ _).trans (add_le_add (le_of_eq (coeffL1_C _)) ?_)
    exact (coeffL1_C_mul_le _ _).trans (by rw [hX, mul_one])
  have hrow : ∀ (c u a b : ℝ), coeffL1 (C c + (C F.t₀ + C F.q * X 0) * C u + C a * X 1 +
      C b * X 2 : MvPolynomial (Fin 4) ℝ) ≤ |c| + (|F.t₀| + |F.q|) * |u| + |a| + |b| := by
    intro c u a b
    refine (coeffL1_add_le _ _).trans (add_le_add ((coeffL1_add_le _ _).trans
      (add_le_add ((coeffL1_add_le _ _).trans (add_le_add (le_of_eq (coeffL1_C _)) ?_)) ?_)) ?_)
    · exact (coeffL1_mul_C_le _ _).trans (mul_le_mul_of_nonneg_right htime (abs_nonneg _))
    · exact (coeffL1_C_mul_le _ _).trans (by rw [hX, mul_one])
    · exact (coeffL1_C_mul_le _ _).trans (by rw [hX, mul_one])
  have hB : ∀ x : ℝ, 0 ≤ x → x ≤ (1 + |F.t₀| + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) * x := by
    intro x hx
    have : 1 ≤ (1 + |F.t₀| + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ _ := by gcongr <;> linarith
    nlinarith
  unfold unsubstBound
  fin_cases i
  · show coeffL1 (C F.t₀ + C F.q * X 0 : MvPolynomial (Fin 4) ℝ) ≤ _
    refine htime.trans ?_
    have h1 : |F.t₀| + |F.q| ≤ (1 + |F.t₀| + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) := by nlinarith
    calc |F.t₀| + |F.q| ≤ (1 + |F.t₀| + |F.q|) * (1 + ‖F.c‖ + ‖F.u‖) * 1 := by linarith
      _ ≤ _ := by gcongr; linarith
  · show coeffL1 (C (F.c 0) + (C F.t₀ + C F.q * X 0) * C (F.u 0) + C (F.D 0 0) * X 1 +
      C (F.D 0 1) * X 2 : MvPolynomial (Fin 4) ℝ) ≤ _
    refine (hrow _ _ _ _).trans ?_
    have hD : |F.D 0 0| + |F.D 0 1| ≤ S := by
      rw [hsum]; linarith [abs_nonneg (F.D 1 0), abs_nonneg (F.D 1 1)]
    nlinarith [abs_nonneg (F.D 0 0), abs_nonneg (F.D 0 1), mul_nonneg ht hun, mul_nonneg hq hun,
      hB S hS0, mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 1 + |F.t₀| + |F.q|)
        (by positivity : (0:ℝ) ≤ 1 + ‖F.c‖ + ‖F.u‖)) hS0]
  · show coeffL1 (C (F.c 1) + (C F.t₀ + C F.q * X 0) * C (F.u 1) + C (F.D 1 0) * X 1 +
      C (F.D 1 1) * X 2 : MvPolynomial (Fin 4) ℝ) ≤ _
    refine (hrow _ _ _ _).trans ?_
    have hD : |F.D 1 0| + |F.D 1 1| ≤ S := by
      rw [hsum]; linarith [abs_nonneg (F.D 0 0), abs_nonneg (F.D 0 1)]
    nlinarith [abs_nonneg (F.D 1 0), abs_nonneg (F.D 1 1), mul_nonneg ht hun, mul_nonneg hq hun,
      hB S hS0, mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 1 + |F.t₀| + |F.q|)
        (by positivity : (0:ℝ) ≤ 1 + ‖F.c‖ + ‖F.u‖)) hS0]
  · show coeffL1 (X 3 : MvPolynomial (Fin 4) ℝ) ≤ _
    rw [hX]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by
        gcongr
        · linarith
        · linarith
        · linarith

theorem abs_coeff_normTest_le (δ : ℝ) (P : MvPolynomial (Fin 4) ℝ) (e : Fin 4 →₀ ℕ) :
    |(F.normTest δ P).coeff e| ≤ |δ⁻¹| * (coeffL1 P * F.unsubstBound ^ P.totalDegree) := by
  refine (abs_coeff_le_coeffL1 _ e).trans ?_
  refine (coeffL1_smul _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (coeffL1_bind₁_le _ _ F.one_le_unsubstBound
    F.coeffL1_unsubst_le P) (abs_nonneg _)

end Frame
end Submission.Obl.k4_raw_native_atlas_normalization.Kernel
