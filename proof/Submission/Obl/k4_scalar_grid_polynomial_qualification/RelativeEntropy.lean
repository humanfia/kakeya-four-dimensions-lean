import Submission.Obl.k4_scalar_grid_polynomial_qualification.Entropy
import LeanPool.ZhangYeungInequality.PFR.Mathlib.Analysis.SpecialFunctions.NegMulLog

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Entropy

open scoped BigOperators

/-- Relative entropy on a finite alphabet. Absolute continuity is supplied in
the lemmas that use it, so zero reference atoms cause no ambiguity. -/
noncomputable def relativeEntropy {S : Type*} [Fintype S] (p q : S → ℝ) : ℝ :=
  ∑ s, p s * Real.log (p s / q s)

noncomputable def finiteEntropy {S : Type*} [Fintype S] (p : S → ℝ) : ℝ :=
  ∑ s, Real.negMulLog (p s)

theorem relativeEntropy_nonneg {S : Type*} [Fintype S] (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s)
    (hpsum : ∑ s, p s = 1) (hqsum : ∑ s, q s = 1)
    (habs : ∀ s, q s = 0 → p s = 0) :
    0 ≤ relativeEntropy p q := by
  simpa only [hpsum, hqsum, div_self one_ne_zero, Real.log_one, mul_zero,
    relativeEntropy] using
    Real.sum_mul_log_div_leq (s := Finset.univ) (a := p) (b := q)
      (fun s _ => hp s) (fun s _ => hq s) (fun s _ => habs s)

/-- A likelihood-ratio ceiling bounds relative entropy by its logarithm. -/
theorem relativeEntropy_le_log {S : Type*} [Fintype S] (p q : S → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) (hpsum : ∑ s, p s = 1)
    {C : ℝ} (_hC : 0 < C) (hdom : ∀ s, p s ≤ C * q s) :
    relativeEntropy p q ≤ Real.log C := by
  calc
    relativeEntropy p q ≤ ∑ s, p s * Real.log C := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : p s = 0
      · simp [hs]
      have hps : 0 < p s := lt_of_le_of_ne (hp s) (Ne.symm hs)
      have hqs : 0 < q s := by
        by_contra h
        have hz : q s = 0 := le_antisymm (not_lt.mp h) (hq s)
        have hle : p s ≤ 0 := by simpa only [hz, mul_zero] using hdom s
        exact (not_lt_of_ge hle) hps
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log (div_pos hps hqs) ((div_le_iff₀ hqs).2 (hdom s))) (hp s)
    _ = Real.log C := by rw [← Finset.sum_mul, hpsum, one_mul]

theorem weighted_log_div {a b : ℝ} (habs : b = 0 → a = 0) :
    a * Real.log (a / b) = a * Real.log a - a * Real.log b := by
  by_cases ha : a = 0
  · simp [ha]
  have hb : b ≠ 0 := fun hb => ha (habs hb)
  rw [Real.log_div ha hb, mul_sub]

/-- The elementary expansion of relative entropy separates Shannon entropy
from the cross entropy against the reference law. -/
theorem relativeEntropy_eq {S : Type*} [Fintype S] (p q : S → ℝ)
    (habs : ∀ s, q s = 0 → p s = 0) :
    relativeEntropy p q = -finiteEntropy p - ∑ s, p s * Real.log (q s) := by
  simp only [relativeEntropy, weighted_log_div (habs _), Finset.sum_sub_distrib,
    finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]

noncomputable def leftMarginal {A B : Type*} [Fintype B] (p : A × B → ℝ) (a : A) : ℝ :=
  ∑ b, p (a, b)

noncomputable def rightMarginal {A B : Type*} [Fintype A] (p : A × B → ℝ) (b : B) : ℝ :=
  ∑ a, p (a, b)

theorem weighted_log_mul {a b c : ℝ} (habs : b * c = 0 → a = 0) :
    a * Real.log (b * c) = a * Real.log b + a * Real.log c := by
  by_cases ha : a = 0
  · simp [ha]
  have hb : b ≠ 0 := fun hb => ha (habs (by simp [hb]))
  have hc : c ≠ 0 := fun hc => ha (habs (by simp [hc]))
  rw [Real.log_mul hb hc, mul_add]

/-- Relative entropy against a product reference splits into mutual
information and the two marginal relative entropies. -/
theorem relativeEntropy_product_decomposition {A B : Type*} [Fintype A] [Fintype B]
    (p : A × B → ℝ) (q : A → ℝ) (r : B → ℝ)
    (habs : ∀ a b, q a * r b = 0 → p (a, b) = 0) :
    relativeEntropy p (fun x => q x.1 * r x.2) =
      (finiteEntropy (leftMarginal p) + finiteEntropy (rightMarginal p) - finiteEntropy p) +
      relativeEntropy (leftMarginal p) q + relativeEntropy (rightMarginal p) r := by
  have hleft (a : A) (ha : q a = 0) : leftMarginal p a = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    exact habs a b (by simp [ha])
  have hright (b : B) (hb : r b = 0) : rightMarginal p b = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact habs a b (by simp [hb])
  have hqcross : (∑ x : A × B, p x * Real.log (q x.1)) =
      ∑ a, leftMarginal p a * Real.log (q a) := by
    simp only [Fintype.sum_prod_type, leftMarginal, Finset.sum_mul]
  have hrcross : (∑ x : A × B, p x * Real.log (r x.2)) =
      ∑ b, rightMarginal p b * Real.log (r b) := by
    simp only [Fintype.sum_prod_type, rightMarginal, Finset.sum_mul]
    exact Finset.sum_comm
  have hcross : (∑ x : A × B, p x * Real.log (q x.1 * r x.2)) =
      (∑ a, leftMarginal p a * Real.log (q a)) +
        ∑ b, rightMarginal p b * Real.log (r b) := by
    simp only [weighted_log_mul (habs _ _), Finset.sum_add_distrib, hqcross, hrcross]
  rw [relativeEntropy_eq p _ (fun x => habs x.1 x.2),
    relativeEntropy_eq _ q hleft, relativeEntropy_eq _ r hright, hcross]
  ring

/-- Product domination controls mutual information without changing the
reference marginals after conditioning or selection. -/
theorem finite_mutual_information_le_log {A B : Type*} [Fintype A] [Fintype B]
    (p : A × B → ℝ) (q : A → ℝ) (r : B → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ a, 0 ≤ q a) (hr : ∀ b, 0 ≤ r b)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ a, q a = 1) (hrsum : ∑ b, r b = 1)
    {C : ℝ} (hC : 0 < C) (hdom : ∀ x, p x ≤ C * (q x.1 * r x.2)) :
    finiteEntropy (leftMarginal p) + finiteEntropy (rightMarginal p) - finiteEntropy p ≤
      Real.log C := by
  have habs (a : A) (b : B) (h : q a * r b = 0) : p (a, b) = 0 := by
    exact le_antisymm (by simpa only [h, mul_zero] using hdom (a, b)) (hp (a, b))
  have hleft (a : A) (ha : q a = 0) : leftMarginal p a = 0 := by
    exact Finset.sum_eq_zero (fun b _ => habs a b (by simp [ha]))
  have hright (b : B) (hb : r b = 0) : rightMarginal p b = 0 := by
    exact Finset.sum_eq_zero (fun a _ => habs a b (by simp [hb]))
  have hleftsum : ∑ a, leftMarginal p a = 1 := by
    simpa only [leftMarginal, ← Fintype.sum_prod_type] using hpsum
  have hrightsum : ∑ b, rightMarginal p b = 1 := by
    rw [show (∑ b, rightMarginal p b) = ∑ a, leftMarginal p a by
      exact Finset.sum_comm]
    exact hleftsum
  have hKLleft := relativeEntropy_nonneg (leftMarginal p) q
    (fun a => Finset.sum_nonneg (fun b _ => hp (a, b))) hq hleftsum hqsum hleft
  have hKLright := relativeEntropy_nonneg (rightMarginal p) r
    (fun b => Finset.sum_nonneg (fun a _ => hp (a, b))) hr hrightsum hrsum hright
  have hKL := relativeEntropy_le_log p (fun x => q x.1 * r x.2) hp
    (fun x => mul_nonneg (hq x.1) (hr x.2)) hpsum hC hdom
  rw [relativeEntropy_product_decomposition p q r habs] at hKL
  linarith

open MeasureTheory ProbabilityTheory Set

theorem finiteEntropy_measure {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsProbabilityMeasure μ] :
    finiteEntropy (fun s => μ.real {s}) = measureEntropy μ := by
  symm
  exact measureEntropy_of_isProbabilityMeasure_finite (A := Finset.univ) (by simp)

theorem probability_atom_sum {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (μ : Measure S) [IsProbabilityMeasure μ] :
    ∑ s, μ.real {s} = 1 := by
  rw [sum_measureReal_singleton]
  simp

theorem leftMarginal_measure {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure (A × B)) [IsFiniteMeasure μ] :
    leftMarginal (fun x => μ.real {x}) = fun a => (μ.map Prod.fst).real {a} := by
  funext a
  rw [map_measureReal_apply measurable_fst (measurableSet_singleton a)]
  simp only [leftMarginal, Measure.real, measure_preimage_fst_singleton_eq_sum,
    ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)]

theorem rightMarginal_measure {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure (A × B)) [IsFiniteMeasure μ] :
    rightMarginal (fun x => μ.real {x}) = fun b => (μ.map Prod.snd).real {b} := by
  funext b
  rw [map_measureReal_apply measurable_snd (measurableSet_singleton b)]
  simp only [rightMarginal, Measure.real, measure_preimage_snd_singleton_eq_sum,
    ENNReal.toReal_sum (fun _ _ => measure_ne_top μ _)]

/-- The product-domination information bound expressed directly for
finite-valued probability laws and their original reference laws. -/
theorem measure_mutual_information_le_log {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure (A × B)) (ν : Measure A) (ξ : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    {C : ℝ} (hC : 0 < C)
    (hdom : ∀ x, μ.real {x} ≤ C * (ν.real {x.1} * ξ.real {x.2})) :
    measureMutualInfo μ ≤ Real.log C := by
  have h := finite_mutual_information_le_log
    (fun x => μ.real {x}) (fun a => ν.real {a}) (fun b => ξ.real {b})
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) (probability_atom_sum μ)
    (probability_atom_sum ν) (probability_atom_sum ξ) hC hdom
  simpa only [leftMarginal_measure, rightMarginal_measure, finiteEntropy_measure,
    measureMutualInfo_def] using h

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Entropy
