import Mathlib

/-!
# The data of a forbidden two-color configuration

This record packages exactly the assumptions in the frozen theorem, including
its almost-sure support condition. It introduces no extra regularity hypotheses.
-/

namespace Submission.Obl.k4_two_color_matching

open Set MeasureTheory
open scoped ENNReal BigOperators

/-- The retained events: close values with a separated derivative of order at most `D`. -/
def matchingEvent {n₁ n₂ : ℕ} (D : ℕ) (N η : ℝ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) :
    Set ((Fin n₁ × Fin n₂) × ℝ) :=
  {p | p.2 ∈ Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ N ^ (-η) ≤
      |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}

/-- A counterexample at a single scale and a single input loss. -/
structure MatchingConfig (D J : ℕ) (d η N : ℝ) where
  n₁ : ℕ
  n₂ : ℕ
  f₁ : Fin n₁ → ℝ → ℝ
  f₂ : Fin n₂ → ℝ → ℝ
  π₁ : Fin n₁ → ℝ
  π₂ : Fin n₂ → ℝ
  μ : Measure ((Fin n₁ × Fin n₂) × ℝ)
  size₁ : (n₁ : ℝ) ≤ N ^ (d + η)
  size₂ : (n₂ : ℝ) ≤ N ^ (d + η)
  smooth₁ : ∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Ioo (-1 : ℝ) 2)
  smooth₂ : ∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Ioo (-1 : ℝ) 2)
  deriv₁ : ∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Icc (0 : ℝ) 1,
    |iteratedDeriv j (f₁ i) t| ≤ N ^ η
  deriv₂ : ∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Icc (0 : ℝ) 1,
    |iteratedDeriv j (f₂ i) t| ≤ N ^ η
  prior₁_nonneg : ∀ i : Fin n₁, 0 ≤ π₁ i
  prior₂_nonneg : ∀ i : Fin n₂, 0 ≤ π₂ i
  prior₁_sum : (∑ i : Fin n₁, π₁ i) = 1
  prior₂_sum : (∑ i : Fin n₂, π₂ i) = 1
  probability : IsProbabilityMeasure μ
  marginal₁ : ∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E →
    μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * volume E
  marginal₂ : ∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E →
    μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * volume E
  support : μ (matchingEvent D N η f₁ f₂)ᶜ = 0

lemma matchingEvent_mono_loss {n₁ n₂ : ℕ} (D : ℕ) {N η ε : ℝ} (hN : 1 ≤ N)
    (hηε : η ≤ ε) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) :
    matchingEvent D N η f₁ f₂ ⊆ matchingEvent D N ε f₁ f₂ := by
  rintro p ⟨ht, hv, j, hj, hjD, hgap⟩
  refine ⟨ht, hv.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    j, hj, hjD, ?_⟩
  exact (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hηε)).trans hgap

/-- Enlarging the loss preserves every assumption of the forbidden configuration. -/
noncomputable def MatchingConfig.weakenLoss {D J : ℕ} {d η ε N : ℝ}
    (C : MatchingConfig D J d η N) (hN : 1 ≤ N) (hηε : η ≤ ε) :
    MatchingConfig D J d ε N where
  n₁ := C.n₁
  n₂ := C.n₂
  f₁ := C.f₁
  f₂ := C.f₂
  π₁ := C.π₁
  π₂ := C.π₂
  μ := C.μ
  size₁ := C.size₁.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  size₂ := C.size₂.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  smooth₁ := C.smooth₁
  smooth₂ := C.smooth₂
  deriv₁ := fun i j hj t ht => (C.deriv₁ i j hj t ht).trans
    (Real.rpow_le_rpow_of_exponent_le hN hηε)
  deriv₂ := fun i j hj t ht => (C.deriv₂ i j hj t ht).trans
    (Real.rpow_le_rpow_of_exponent_le hN hηε)
  prior₁_nonneg := C.prior₁_nonneg
  prior₂_nonneg := C.prior₂_nonneg
  prior₁_sum := C.prior₁_sum
  prior₂_sum := C.prior₂_sum
  probability := C.probability
  marginal₁ := by
    intro i E hE
    apply (C.marginal₁ i E hE).trans
    gcongr
    exact C.prior₁_nonneg i
  marginal₂ := by
    intro i E hE
    apply (C.marginal₂ i E hE).trans
    gcongr
    exact C.prior₂_nonneg i
  support := measure_mono_null (compl_subset_compl.mpr
    (matchingEvent_mono_loss D hN hηε C.f₁ C.f₂)) C.support

lemma MatchingConfig.ae_event {D J : ℕ} {d η N : ℝ} (C : MatchingConfig D J d η N) :
    ∀ᵐ p ∂C.μ, p ∈ matchingEvent D N η C.f₁ C.f₂ := by
  exact ae_iff.mpr C.support

lemma MatchingConfig.ae_time {D J : ℕ} {d η N : ℝ} (C : MatchingConfig D J d η N) :
    ∀ᵐ p ∂C.μ, p.2 ∈ Icc (0 : ℝ) 1 :=
  C.ae_event.mono fun _p hp => hp.1

lemma MatchingConfig.time_domination {D J : ℕ} {d η N : ℝ}
    (C : MatchingConfig D J d η N) (hN : 0 ≤ N) (E : Set ℝ) (hE : MeasurableSet E) :
    C.μ {p | p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η) * volume E := by
  have hcover : {p : (Fin C.n₁ × Fin C.n₂) × ℝ | p.2 ∈ E} =
      ⋃ i : Fin C.n₁, {p | p.1.1 = i ∧ p.2 ∈ E} := by
    ext p
    simp
  rw [hcover]
  calc
    C.μ (⋃ i : Fin C.n₁, {p | p.1.1 = i ∧ p.2 ∈ E}) ≤
        ∑ i : Fin C.n₁, C.μ {p | p.1.1 = i ∧ p.2 ∈ E} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : Fin C.n₁, ENNReal.ofReal (N ^ η * C.π₁ i) * volume E :=
      Finset.sum_le_sum fun i hi => C.marginal₁ i E hE
    _ = ENNReal.ofReal (N ^ η) * volume E := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg]
      · rw [← Finset.mul_sum, C.prior₁_sum, mul_one]
      · intro i hi
        exact mul_nonneg (Real.rpow_nonneg hN _) (C.prior₁_nonneg i)

end Submission.Obl.k4_two_color_matching
