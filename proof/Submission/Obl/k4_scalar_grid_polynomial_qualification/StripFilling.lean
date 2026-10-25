import Submission.Lib.K4ContinuousKakeya.Incidence

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory
open scoped NNReal ENNReal
open Submission.Lib.K4ContinuousKakeya

/-- Plane Kakeya turns a determinant floor in each base cell into a filling
bound. The entering trajectory and incidence measures remain unnormalized.
The prior bound is the one obtained after deleting short line/strip entries. -/
theorem plane_strip_filling {α ι : Type*} [MeasurableSpace α]
    (θ : Measure α) [IsFiniteMeasure θ] (inc : Measure (α × ℝ)) [IsFiniteMeasure inc]
    {C K D p ρ β η : ℝ} (hC0 : 0 ≤ C) (hC : FiniteMK 2 C)
    (hK : 0 < K) (hD : 0 < D) (hp : 0 < p) (hρ : 0 < ρ)
    (hβ : 0 < β) (hη : 0 < η)
    (c : ℝ≥0) (hcValue : (c : ℝ) = K * p)
    (Φ : α × ℝ → EuclideanSpace ℝ (Fin 2)) (hΦ : Measurable Φ)
    (a e : α → EuclideanSpace ℝ (Fin 2)) (ha : Measurable a) (he : Measurable e)
    (he1 : ∀ l, ‖e l‖ = 1) {B : ℝ} (hB : ∀ l, ‖a l‖ ≤ B) (R : ℝ)
    (Λ : Set α) (hΛ : MeasurableSet Λ) (s : Finset ι)
    (E : ι → Set (EuclideanSpace ℝ (Fin 2))) (m : ι → ℝ)
    (hEm : ∀ j ∈ s, MeasurableSet (E j)) (hEd : (s : Set ι).PairwiseDisjoint E)
    (hER : ∀ j ∈ s, E j ⊆ Metric.closedBall 0 R)
    (hvol : ∀ j ∈ s, p ^ 2 ≤ (volume (E j)).toReal)
    (hm : 0 < ∑ j ∈ s, m j)
    (hprior : (θ Λ).toReal ≤ K * (∑ j ∈ s, m j) / ρ)
    (hpush : ∀ j ∈ s,
      (inc.restrict {ω | ω.1 ∈ Λ ∧ Φ ω ∈ E j}).map Prod.fst ≤
        c • θ.restrict Λ)
    (htube : ∀ j ∈ s, ∀ ω : α × ℝ, ω.1 ∈ Λ → Φ ω ∈ E j → ∀ x ∈ E j,
      x ∈ tube (D * p) (a ω.1) (e ω.1))
    (hsucc : ∀ j ∈ s, ENNReal.ofReal (η * m j ^ 2) ≤
      Measure.pi (fun _ : Fin 2 => inc)
        {ω | (∀ i, (ω i).1 ∈ Λ ∧ Φ (ω i) ∈ E j) ∧
          β ≤ |Matrix.det (Matrix.of fun i k : Fin 2 => e (ω i).1 k)|}) :
    β * η * (ρ / p) ^ 2 ≤ 4 * C * D ^ 2 * K ^ 4 * (s.card : ℝ) := by
  classical
  have hc : 0 < c := by
    change 0 < (c : ℝ)
    rw [hcValue]
    exact mul_pos hK hp
  have hcReal : (c : ENNReal).toReal = K * p := by
    rw [ENNReal.coe_toReal, hcValue]
  have h := incidence_kakeya (n := 2) (by norm_num) hC0 hC θ inc Φ hΦ a e ha he
    he1 hB (mul_pos hD hp) R Λ hΛ s E hEm hEd hER c hc hpush htube β
    (fun j => ENNReal.ofReal (η * m j ^ 2)) hsucc
  simp only [Nat.cast_ofNat, show ((1 : ℝ) / ((2 : ℝ) - 1)) = 1 by norm_num,
    ENNReal.rpow_one, Fin.prod_univ_two] at h
  have hball : volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R) ≠ ⊤ :=
    ne_of_lt measure_closedBall_lt_top
  have hEfin (j : ι) (hj : j ∈ s) : volume (E j) ≠ ⊤ :=
    ne_top_of_le_ne_top hball (measure_mono (hER j hj))
  have hc0 : (c : ENNReal) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hc.ne')
  have htermfin (j : ι) (hj : j ∈ s) :
      volume (E j) * (ENNReal.ofReal β * ENNReal.ofReal (η * m j ^ 2) /
        (c : ENNReal) ^ 2) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (hEfin j hj) (ENNReal.div_ne_top (by finiteness) hc0)
  have hr := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_sum htermfin] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    hcReal, ENNReal.toReal_ofReal hβ.le,
    ENNReal.toReal_ofReal (show 0 ≤ 2 ^ 2 * C * (D * p) ^ 2 by positivity),
    ENNReal.toReal_ofReal (mul_nonneg hη.le (sq_nonneg _))] at hr
  have hreal : ∑ j ∈ s, (volume (E j)).toReal * (β * (η * m j ^ 2) / (K * p) ^ 2) ≤
      4 * C * (D * p) ^ 2 * (θ Λ).toReal ^ 2 := by
    convert hr using 1
    ring
  have henergy : (β * η / K ^ 2) * (∑ j ∈ s, m j ^ 2) ≤
      4 * C * (D * p) ^ 2 * (K * (∑ j ∈ s, m j) / ρ) ^ 2 := by
    calc
      _ = ∑ j ∈ s, p ^ 2 * (β * (η * m j ^ 2) / (K * p) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        field_simp
      _ ≤ ∑ j ∈ s, (volume (E j)).toReal * (β * (η * m j ^ 2) / (K * p) ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (hvol j hj) (by positivity)
      _ ≤ 4 * C * (D * p) ^ 2 * (θ Λ).toReal ^ 2 := hreal
      _ ≤ _ := by gcongr
  have hcs := sq_sum_le_card_mul_sum_sq (s := s) (f := m)
  have hscaled : β * η * ρ ^ 2 * (∑ j ∈ s, m j) ^ 2 ≤
      4 * C * D ^ 2 * K ^ 4 * p ^ 2 * (s.card : ℝ) * (∑ j ∈ s, m j) ^ 2 := by
    have hs := mul_le_mul_of_nonneg_left hcs (show 0 ≤ β * η / K ^ 2 by positivity)
    have he := mul_le_mul_of_nonneg_left henergy (show 0 ≤ (s.card : ℝ) by positivity)
    have hjoin : (β * η / K ^ 2) * (∑ j ∈ s, m j) ^ 2 ≤
        (s.card : ℝ) * (4 * C * (D * p) ^ 2 * (K * (∑ j ∈ s, m j) / ρ) ^ 2) :=
      hs.trans (by convert he using 1; ring)
    have hmul := mul_le_mul_of_nonneg_left hjoin (show 0 ≤ K ^ 2 * ρ ^ 2 by positivity)
    convert hmul using 1 <;> field_simp [hK.ne', hρ.ne']
  have hmass0 : 0 < (∑ j ∈ s, m j) ^ 2 := sq_pos_of_pos hm
  have hcancel := (mul_le_mul_iff_left₀ hmass0).mp hscaled
  rw [div_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  convert hcancel using 1
  ring

end Submission.Obl.k4_scalar_grid_polynomial_qualification
