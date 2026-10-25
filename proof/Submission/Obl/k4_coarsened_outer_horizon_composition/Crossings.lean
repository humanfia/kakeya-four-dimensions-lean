import Submission.Obl.k4_coarsened_outer_horizon_composition.PolynomialBins
import Submission.Obl.k4_coarsened_outer_horizon_composition.BaseVolume
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_quadratic_slope_volume

noncomputable def hiddenPolynomial (R : MvPolynomial (Fin 4) ℝ) (z : E3) : Polynomial ℝ :=
  coordinatePolynomialHom ![z 0, z 1, z 2, 0] (3 : Fin 4) R

lemma hiddenPolynomial_eval (R : MvPolynomial (Fin 4) ℝ) (z : E3) (w : ℝ) :
    (hiddenPolynomial R z).eval w = MvPolynomial.eval ![z 0, z 1, z 2, w] R := by
  rw [hiddenPolynomial, eval_coordinatePolynomialHom]
  apply congrArg (fun v : Fin 4 → ℝ => MvPolynomial.eval v R)
  funext i
  fin_cases i <;> simp

lemma hiddenPolynomial_derivative (R : MvPolynomial (Fin 4) ℝ) (z : E3) :
    (hiddenPolynomial R z).derivative = hiddenPolynomial (MvPolynomial.pderiv 3 R) z :=
  derivative_coordinatePolynomialHom _ _ _

lemma hiddenPolynomial_degree (R : MvPolynomial (Fin 4) ℝ) (z : E3)
    (hR : R.totalDegree ≤ 2) : (hiddenPolynomial R z).natDegree ≤ 2 := by
  apply (natDegree_eval₂_affine_le R _ ?_).trans hR
  intro i
  split_ifs <;> simp

lemma continuous_hiddenPolynomial_eval (R : MvPolynomial (Fin 4) ℝ) (w : ℝ) :
    Continuous (fun z : E3 => (hiddenPolynomial R z).eval w) := by
  simp_rw [hiddenPolynomial_eval]
  exact (MvPolynomial.continuous_eval R).comp (by fun_prop)

/-- A conservative observable support using only polynomial tests at the hidden
bin representative. It includes every selected incidence of a true chart. -/
noncomputable def crossing (κ t₀ t₁ a b : ℝ) (c u : E2)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) : Set Obs :=
  {o | o.1 ∈ baseCross κ t₀ t₁ c u Q ∧ binTest (hiddenPolynomial R o.1) κ a b o.2}

lemma measurableSet_crossing (κ t₀ t₁ a b : ℝ) (c u : E2)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ) :
    MeasurableSet (crossing κ t₀ t₁ a b c u Q R) := by
  have hsec (n : ℤ) : MeasurableSet {z : E3 |
      z ∈ baseCross κ t₀ t₁ c u Q ∧ binTest (hiddenPolynomial R z) κ a b n} := by
    simp_rw [binTest, hiddenPolynomial_derivative]
    apply (measurableSet_baseCross κ t₀ t₁ c u Q).inter
    have hval := (continuous_hiddenPolynomial_eval R ((n : ℝ) * a)).measurable
    have hder := (continuous_hiddenPolynomial_eval (MvPolynomial.pderiv 3 R) ((n : ℝ) * a)).measurable
    have hcur := (continuous_hiddenPolynomial_eval (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 R)) 0).measurable
    exact (measurableSet_le hval.abs measurable_const).inter
      ((measurableSet_le measurable_const hder.abs).union
        (measurableSet_le measurable_const (hcur.abs.mul_const a)))
  have heq : crossing κ t₀ t₁ a b c u Q R = ⋃ n : ℤ,
      {z : E3 | z ∈ baseCross κ t₀ t₁ c u Q ∧ binTest (hiddenPolynomial R z) κ a b n} ×ˢ {n} := by
    ext ⟨z, n⟩
    simp [crossing]
  rw [heq]
  exact MeasurableSet.iUnion fun n => (hsec n).prod (measurableSet_singleton n)

/-- The observable support of one chart has the expected reference volume. -/
theorem reference_crossing {κ t₀ t₁ a b : ℝ} (hκ : 1 ≤ κ) (ht : t₀ ≤ t₁)
    (ha : 0 < a) (hb : 0 < b) (c u : E2) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : Q.det ≠ 0) (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) :
    (volume.prod Measure.count) (crossing κ t₀ t₁ a b c u Q R) ≤
      ENNReal.ofReal (256 * κ ^ 4 * (t₁ - t₀) * |Q.det|) := by
  have hκ0 : 0 ≤ κ := by linarith
  have hbase := measurableSet_baseCross κ t₀ t₁ c u Q
  rw [Measure.prod_apply (measurableSet_crossing κ t₀ t₁ a b c u Q R)]
  calc
    _ ≤ ∫⁻ z : E3, (baseCross κ t₀ t₁ c u Q).indicator
        (fun _ => ENNReal.ofReal (64 * κ ^ 2)) z := by
      apply lintegral_mono
      intro z
      dsimp only
      by_cases hz : z ∈ baseCross κ t₀ t₁ c u Q
      · rw [indicator_of_mem hz]
        have heq : Prod.mk z ⁻¹' crossing κ t₀ t₁ a b c u Q R =
            {n : ℤ | binTest (hiddenPolynomial R z) κ a b n} := by
          ext n
          simp [crossing, hz]
        rw [heq]
        have hn := binTest_count (hiddenPolynomial R z) (hiddenPolynomial_degree R z hR) hκ ha hb
        rw [Measure.count_apply_finite _ hn.1, ← ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_le_ofReal
        simpa only [Set.ncard_eq_toFinset_card _ hn.1] using hn.2
      · have heq : Prod.mk z ⁻¹' crossing κ t₀ t₁ a b c u Q R = ∅ := by
          ext n
          simp [crossing, hz]
        simp [heq, hz]
    _ = ENNReal.ofReal (64 * κ ^ 2) * volume (baseCross κ t₀ t₁ c u Q) := by
      rw [lintegral_indicator hbase, lintegral_const]
      simp
    _ ≤ ENNReal.ofReal (64 * κ ^ 2) * ENNReal.ofReal (4 * κ ^ 2 * (t₁ - t₀) * |Q.det|) :=
      mul_le_mul (le_refl _) (volume_baseCross hκ0 ht c u Q hQ) zero_le zero_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 64 * κ ^ 2)]
      congr 1
      ring

lemma hiddenPolynomial_eval_obs (R : MvPolynomial (Fin 4) ℝ) (B a : ℝ) (p : Inc) :
    (hiddenPolynomial R (obs B a p).1).eval (x p.1 p.2 3) =
      MvPolynomial.eval (x p.1 p.2) R :=
  hiddenPolynomial_eval R (obs B a p).1 (x p.1 p.2 3)

/-- The bounds at one selected incidence imply membership in the observable
polynomial crossing set, including at every hidden-bin boundary. -/
theorem obs_mem_crossing {κ t₀ t₁ a B : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hB : 0 < B)
    (c u : E2) (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : MvPolynomial (Fin 4) ℝ)
    (hR : R.totalDegree ≤ 2) (p : Inc) (ht : p.2 ∈ Icc t₀ t₁)
    (hs : ‖Matrix.toEuclideanLin Q⁻¹ (y p.1 p.2 - c - p.2 • u)‖ ≤ κ)
    (hv : |MvPolynomial.eval (x p.1 p.2) R| ≤ κ * a)
    (hd : |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv 3 R)| ≤ κ * B)
    (hc : |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 R))| ≤
      κ * B ^ 2 / a)
    (hf : B / κ ≤ |MvPolynomial.eval (x p.1 p.2) (MvPolynomial.pderiv 3 R)|) :
    obs B a p ∈ crossing κ t₀ t₁ (a / B) B c u Q R := by
  have hdeg := hiddenPolynomial_degree R (obs B a p).1 hR
  have hvalue : |(hiddenPolynomial R (obs B a p).1).eval (x p.1 p.2 3)| ≤ κ * (a / B) * B := by
    rw [hiddenPolynomial_eval_obs]
    apply hv.trans_eq
    field_simp
  have hderiv : |(hiddenPolynomial R (obs B a p).1).derivative.eval (x p.1 p.2 3)| ≤ κ * B := by
    simpa only [hiddenPolynomial_derivative, hiddenPolynomial_eval_obs] using hd
  have hcurv : |(hiddenPolynomial R (obs B a p).1).derivative.derivative.eval 0| ≤ κ * B / (a / B) := by
    rw [← quadratic_second_constant _ hdeg (x p.1 p.2 3),
      hiddenPolynomial_derivative, hiddenPolynomial_derivative, hiddenPolynomial_eval_obs]
    apply hc.trans_eq
    field_simp
  have hderivfloor : B / κ ≤ |(hiddenPolynomial R (obs B a p).1).derivative.eval (x p.1 p.2 3)| := by
    simpa only [hiddenPolynomial_derivative, hiddenPolynomial_eval_obs] using hf
  have htest := binTest_of_bounds (hiddenPolynomial R (obs B a p).1) hdeg hκ
    (div_pos ha hB) hB hvalue hderiv hcurv hderivfloor
  have hbin : ⌊x p.1 p.2 3 / (a / B)⌋ = ⌊B * x p.1 p.2 3 / a⌋ := by
    congr 1
    field_simp
  constructor
  · constructor
    · simpa [obs, x] using ht
    · simpa [obs, y, x] using hs
  · simpa only [obs, hbin] using htest

end Submission.Obl.k4_coarsened_outer_horizon_composition
