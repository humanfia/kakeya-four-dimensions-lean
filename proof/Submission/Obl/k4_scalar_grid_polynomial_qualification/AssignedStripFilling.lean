import Submission.Obl.k4_scalar_grid_polynomial_qualification.BaseCells
import Submission.Obl.k4_scalar_grid_polynomial_qualification.StripFilling

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory
open scoped NNReal ENNReal
open Submission.Lib.K4ContinuousKakeya

/-- The abstract planar filling kernel applies to the disjoint base squares
assigned by the original fine physical states. -/
theorem assigned_base_strip_filling
    (θ : Measure ScalarLine) [IsFiniteMeasure θ]
    (inc : Measure ScalarIncidence) [IsFiniteMeasure inc]
    {C K ρ p b β η H R : ℝ} (hC0 : 0 ≤ C) (hMK : FiniteMK 2 C)
    (hK : 0 < K) (hρ : 0 < ρ) (hp : 0 < p) (hb : 0 < b) (hbp : b ≤ p)
    (hβ : 0 < β) (hη : 0 < η) (hH : 0 ≤ H)
    (U : ℝ≥0) (hU : 3 * (U : ℝ) ≤ K) (hinc : inc ≤ U • θ.prod volume)
    (Λ : Set ScalarLine) (hΛ : MeasurableSet Λ)
    (hΛbound : ∀ l ∈ Λ, |l.2 0| ≤ H)
    (s : Finset (Fin 2 → ℤ)) (m : (Fin 2 → ℤ) → ℝ)
    (hER : ∀ q ∈ s, baseSquare p q ⊆ Metric.closedBall 0 R)
    (hm : 0 < ∑ q ∈ s, m q)
    (hprior : (θ Λ).toReal ≤ K * (∑ q ∈ s, m q) / ρ)
    (hsucc : ∀ q ∈ s, ENNReal.ofReal (η * m q ^ 2) ≤
      Measure.pi (fun _ : Fin 2 => inc)
        {z | (∀ i, (z i).1 ∈ Λ ∧ baseObservation b (z i) ∈ baseSquare p q) ∧
          β ≤ |Matrix.det (Matrix.of fun i j : Fin 2 => BaseLine.direction ((z i).1.2 1) j)|}) :
    β * η * (ρ / p) ^ 2 ≤ 100 * C * K ^ 4 * (s.card : ℝ) := by
  classical
  let a : ScalarLine → BaseLine.Plane :=
    fun l => if |l.2 0| ≤ H then BaseLine.intercept l else 0
  have hset : MeasurableSet {l : ScalarLine | |l.2 0| ≤ H} :=
    measurableSet_le (((measurable_pi_apply 0).comp measurable_snd).abs) measurable_const
  have ha : Measurable a :=
    Measurable.ite hset BaseLine.measurable_intercept measurable_const
  have he : Measurable (fun l : ScalarLine => BaseLine.direction (l.2 1)) :=
    BaseLine.continuous_direction.measurable.comp ((measurable_pi_apply 1).comp measurable_snd)
  have hB (l : ScalarLine) : ‖a l‖ ≤ H := by
    dsimp only [a]
    split_ifs with hl
    · have hsq : ‖BaseLine.intercept l‖ ^ 2 = (l.2 0) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [BaseLine.intercept, Fin.sum_univ_two]
      nlinarith [norm_nonneg (BaseLine.intercept l), sq_abs (l.2 0), abs_nonneg (l.2 0)]
    · simpa only [norm_zero] using hH
  let c : ℝ≥0 := Real.toNNReal (K * p)
  have hc : (c : ℝ) = K * p := Real.coe_toNNReal _ (by positivity)
  have hscalar : U * Real.toNNReal (p + 2 * b) ≤ c := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), hc]
    nlinarith [U.coe_nonneg]
  have hpush (q : Fin 2 → ℤ) :
      (inc.restrict {z | z.1 ∈ Λ ∧ baseObservation b z ∈ baseSquare p q}).map Prod.fst ≤
        c • θ.restrict Λ := by
    refine (baseSquare_pushforward_cap θ inc U hinc hp hb Λ hΛ q).trans ?_
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply, Measure.smul_apply]
    change ((U * Real.toNNReal (p + 2 * b) : ℝ≥0) : ℝ≥0∞) * (θ.restrict Λ) A ≤
      (c : ℝ≥0∞) * (θ.restrict Λ) A
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hscalar) zero_le
  have htube (q : Fin 2 → ℤ) (z : ScalarIncidence) (hz : z.1 ∈ Λ)
      (hobs : baseObservation b z ∈ baseSquare p q) :
      baseSquare p q ⊆ tube (5 * p) (a z.1) (BaseLine.direction (z.1.2 1)) := by
    dsimp only [a]
    rw [ite_eq_left (hΛbound z.1 hz)]
    exact baseSquare_subset_tube hp hb hbp z.1 z.2 q hobs
  have hvol (q : Fin 2 → ℤ) : p ^ 2 ≤ (volume (baseSquare p q)).toReal := by
    rw [volume_baseSquare, ENNReal.toReal_pow, ENNReal.toReal_ofReal hp.le]
  have hEd : (s : Set (Fin 2 → ℤ)).PairwiseDisjoint (baseSquare p) := by
    intro q _ q' _ hqq'
    exact pairwiseDisjoint_baseSquare hp (mem_univ q) (mem_univ q') hqq'
  have h := plane_strip_filling θ inc hC0 hMK hK (by norm_num : (0 : ℝ) < 5)
    hp hρ hβ hη c hc (baseObservation b) (measurable_baseObservation b) a
    (fun l => BaseLine.direction (l.2 1)) ha he (fun l => BaseLine.direction_norm (l.2 1))
    hB R Λ hΛ s (baseSquare p) m (fun q _ => measurableSet_baseSquare p q)
    hEd hER (fun q _ => hvol q)
    hm hprior (fun q _ => hpush q) (fun q _ z hz hobs => htube q z hz hobs) hsucc
  calc
    _ ≤ 4 * C * 5 ^ 2 * K ^ 4 * (s.card : ℝ) := h
    _ = _ := by ring

end Submission.Obl.k4_scalar_grid_polynomial_qualification
