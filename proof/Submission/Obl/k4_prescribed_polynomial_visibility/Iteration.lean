import Submission.Obl.k4_prescribed_polynomial_visibility.Base
import Submission.Obl.k4_prescribed_polynomial_visibility.Mix

namespace Submission.Obl.k4_prescribed_polynomial_visibility

open MeasureTheory
open scoped ENNReal

/-- A one-step adaptive polynomial improvement, before taking convex averages. -/
def ImprovementOracle (n : ℕ) (C : ℝ) : Prop :=
  ∀ (m : ℕ) (c : Fin m → EuclideanSpace ℝ (Fin n))
    (V : Fin m → Seminorm ℝ (EuclideanSpace ℝ (Fin n))),
    (∀ q, Continuous (V q)) → (∀ q v, ‖v‖ ≤ V q v) →
    ∀ T : ℝ, 1 ≤ T → ∀ M : Fin m → ℝ,
    (∀ q, 0 ≤ M q) → (∑ q, M q) = 1 →
    ∃ p : MvPolynomial (Fin n) ℝ, (p.totalDegree : ℝ) ≤ C * T ∧
      ∀ q, 0 < M q → ENNReal.ofReal ((T ^ n * M q)⁻¹) < volume (unitBody (V q)) →
        ∃ v, V q v ≤ 1 ∧ (3 : ℝ) * 2 ^ (3 * n) ≤ polynomialVariation p (c q) v

/-- A finite probability ensemble meeting a specified degree and volume bound. -/
def HasEnsemble {n m : ℕ} (c : Fin m → EuclideanSpace ℝ (Fin n))
    (M : Fin m → ℝ) (d D : ℝ) : Prop :=
  ∃ (r : ℕ) (p : Fin r → MvPolynomial (Fin n) ℝ) (w : Fin r → ℝ)
    (hw : ∀ h, 0 ≤ w h), (∑ h, w h) = 1 ∧
      (∀ h, ((p h).totalDegree : ℝ) ≤ d) ∧
      ∀ q, 0 < M q → volume (unitBody (ensemble p w hw (c q))) ≤
        ENNReal.ofReal ((D ^ n * M q)⁻¹)

@[simp] theorem polynomialVariation_zero {n : ℕ} (c v : EuclideanSpace ℝ (Fin n)) :
    polynomialVariation 0 c v = 0 := by
  have h : arctanPolynomial (0 : MvPolynomial (Fin n) ℝ) = fun _ => (0 : ℝ) := by
    funext x
    simp [arctanPolynomial]
  simp [polynomialVariation, h]

@[simp] theorem ensemble_zero {n r : ℕ} (w : Fin r → ℝ) (hw : ∀ h, 0 ≤ w h)
    (c : EuclideanSpace ℝ (Fin n)) :
    ensemble (fun _ => (0 : MvPolynomial (Fin n) ℝ)) w hw c = normSeminorm ℝ _ := by
  ext v
  simp

theorem hasEnsemble_initial {n m : ℕ} (c : Fin m → EuclideanSpace ℝ (Fin n))
    (M : Fin m → ℝ) (hM : ∀ q, 0 ≤ M q) (hsum : ∑ q, M q = 1)
    (d : ℝ) (hd : 0 ≤ d) : HasEnsemble c M d (1 / 2) := by
  refine ⟨1, (fun _ => 0), (fun _ => 1), (fun _ => by norm_num), by simp, ?_, ?_⟩
  · intro h
    simpa using hd
  · intro q hq
    simpa only [ensemble_zero] using initial_volume_bound M hM hsum q hq

theorem hasEnsemble_mono_degree {n m : ℕ} (c : Fin m → EuclideanSpace ℝ (Fin n))
    (M : Fin m → ℝ) {d d' D : ℝ} (hdd' : d ≤ d') (h : HasEnsemble c M d D) :
    HasEnsemble c M d' D := by
  obtain ⟨r, p, w, hw, hs, hd, hv⟩ := h
  exact ⟨r, p, w, hw, hs, (fun i => (hd i).trans hdd'), hv⟩

/-- One averaging step doubles the achieved scale. -/
theorem hasEnsemble_double {n m : ℕ} (C : ℝ) (hOracle : ImprovementOracle n C)
    (c : Fin m → EuclideanSpace ℝ (Fin n)) (M : Fin m → ℝ)
    (hM : ∀ q, 0 ≤ M q) (hsum : ∑ q, M q = 1)
    {d D : ℝ} (hD : 0 < D) (hT : 1 ≤ 4 * D) (h : HasEnsemble c M d D) :
    HasEnsemble c M (max d (4 * C * D)) (2 * D) := by
  obtain ⟨r, p, w, hw, hs, hd, hv⟩ := h
  obtain ⟨P, hP, himprove⟩ := hOracle m c (fun q => ensemble p w hw (c q))
    (fun q => continuous_ensemble p w hw (c q))
    (fun q v => norm_le_ensemble p w hw (c q) v) (4 * D) hT M hM hsum
  let p' := mixPolynomials P p
  let w' := mixWeights w
  let hw' := mixWeights_nonneg w hw
  refine ⟨r + 1, p', w', hw', sum_mixWeights w hs, ?_, ?_⟩
  · apply mixPolynomials_degree_le
    · have hP' : (P.totalDegree : ℝ) ≤ 4 * C * D := by nlinarith [hP]
      exact hP'.trans (le_max_right _ _)
    · exact fun i => (hd i).trans (le_max_left _ _)
  · intro q hq
    let V := ensemble p w hw (c q)
    let S := polynomialVariationSeminorm P (c q) (integrableOn_polynomialVariation P (c q))
    let Q := ensemble p' w' hw' (c q)
    have hQ : ∀ v, V v + S v ≤ 2 * Q v := by
      intro v
      exact le_two_mul_mixed_ensemble P p w hw (c q) v
    by_cases hactive : ENNReal.ofReal (((4 * D) ^ n * M q)⁻¹) < volume (unitBody V)
    · obtain ⟨v, hVv, hSv⟩ := himprove q hq hactive
      have hSv' : 3 * (8 : ℝ) ^ n ≤ S v := by
        have hpow : (2 : ℝ) ^ (3 * n) = (8 : ℝ) ^ n := by
          rw [pow_mul]
          norm_num
        simpa only [S, polynomialVariationSeminorm_apply, hpow] using hSv
      have hshrink := volume_unitBody_average_shrink V S Q hQ v hVv hSv'
      apply (ENNReal.mul_le_mul_iff_right
        (a := (2 : ℝ≥0∞) ^ n) (by positivity) (by finiteness)).mp
      calc
        (2 : ℝ≥0∞) ^ n * volume (unitBody Q) ≤ volume (unitBody V) := hshrink
        _ ≤ ENNReal.ofReal ((D ^ n * M q)⁻¹) := hv q hq
        _ = (2 : ℝ≥0∞) ^ n * ENNReal.ofReal (((2 * D) ^ n * M q)⁻¹) :=
          (two_pow_mul_reciprocal D (M q) hD hq).symm
    · have hinactive : volume (unitBody V) ≤ ENNReal.ofReal (((4 * D) ^ n * M q)⁻¹) :=
        le_of_not_gt hactive
      have hscale : volume (unitBody Q) ≤ (2 : ℝ≥0∞) ^ n * volume (unitBody V) := by
        simpa using volume_unitBody_le_of_le_mul V Q 2 (by norm_num)
          (old_le_two_mul_mixed_ensemble P p w hw (c q))
      calc
        volume (unitBody Q) ≤ (2 : ℝ≥0∞) ^ n * volume (unitBody V) := hscale
        _ ≤ (2 : ℝ≥0∞) ^ n * ENNReal.ofReal (((4 * D) ^ n * M q)⁻¹) :=
          mul_le_mul_right hinactive _
        _ = ENNReal.ofReal (((2 * D) ^ n * M q)⁻¹) := by
          rw [show 4 * D = 2 * (2 * D) by ring]
          exact two_pow_mul_reciprocal (2 * D) (M q) (by positivity) hq

/-- The iterative averaging construction, at geometric scales. -/
theorem hasEnsemble_geometric {n m : ℕ} (C : ℝ) (hC : 0 < C)
    (hOracle : ImprovementOracle n C) (c : Fin m → EuclideanSpace ℝ (Fin n))
    (M : Fin m → ℝ) (hM : ∀ q, 0 ≤ M q) (hsum : ∑ q, M q = 1) (k : ℕ) :
    HasEnsemble c M (2 * C * (2 : ℝ) ^ k) ((2 : ℝ) ^ k / 2) := by
  induction k with
  | zero =>
    simpa using hasEnsemble_initial c M hM hsum (2 * C) (by positivity)
  | succ k ih =>
    have ha : (0 : ℝ) < 2 ^ k := by positivity
    have ha1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hT : (1 : ℝ) ≤ 4 * ((2 : ℝ) ^ k / 2) := by linarith
    have hh := hasEnsemble_double C hOracle c M hM hsum (by positivity) hT ih
    have hD : 2 * ((2 : ℝ) ^ k / 2) = (2 : ℝ) ^ (k + 1) / 2 := by
      rw [pow_succ]
      ring
    have hd : max (2 * C * (2 : ℝ) ^ k) (4 * C * ((2 : ℝ) ^ k / 2)) ≤
        2 * C * (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      apply max_le <;> nlinarith [mul_pos hC ha]
    exact hasEnsemble_mono_degree c M hd (by simpa only [hD] using hh)

/-- An adaptive one-step improvement supplies the full finite prescribed ensemble. -/
theorem prescribed_ensemble_of_improvement (n : ℕ) (C : ℝ) (hC : 0 < C)
    (hOracle : ImprovementOracle n C) :
    ∃ L : ℝ, 0 < L ∧ ∀ (m : ℕ) (c : Fin m → EuclideanSpace ℝ (Fin n))
      (M : Fin m → ℝ), (∀ q, 0 ≤ M q) → (∑ q, M q) = 1 →
      ∃ D : ℝ, (m : ℝ) + 1 ≤ D ∧ HasEnsemble c M (L * D) D := by
  refine ⟨4 * C, by positivity, ?_⟩
  intro m c M hM hsum
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 * ((m : ℝ) + 1))
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨(2 : ℝ) ^ k / 2, by linarith, ?_⟩
  have hh := hasEnsemble_geometric C hC hOracle c M hM hsum k
  convert hh using 1
  ring

end Submission.Obl.k4_prescribed_polynomial_visibility
