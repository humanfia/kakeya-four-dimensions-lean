import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_matching_gap_regularization

open MeasureTheory Set
open scoped ENNReal

/-- Derivatives are only used on the interval where smoothness is assumed. -/
noncomputable def localDeriv (j : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (Icc (0 : ℝ) 1).piecewise (iteratedDeriv j f) (fun _ => 0)

lemma localDeriv_eq {j : ℕ} {f : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    localDeriv j f t = iteratedDeriv j f t := by
  simp [localDeriv, ht]

lemma measurable_localDeriv {J j : ℕ} {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (J + 1) f (Ioo (-1 : ℝ) 2)) (hj : j ≤ J + 1) :
    Measurable (localDeriv j f) := by
  have hcont : ContinuousOn (iteratedDerivWithin j f (Ioo (-1 : ℝ) 2))
      (Ioo (-1 : ℝ) 2) :=
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) isOpen_Ioo.uniqueDiffOn
  have hder : ContinuousOn (iteratedDeriv j f) (Ioo (-1 : ℝ) 2) :=
    hcont.congr (iteratedDerivWithin_of_isOpen isOpen_Ioo).symm
  apply (hder.mono ?_).measurable_piecewise continuous_const.continuousOn measurableSet_Icc
  intro t ht
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma measurable_localGap {n₁ n₂ J j : ℕ}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (hf₁ : ∀ i, ContDiffOn ℝ (J + 1) (f₁ i) (Ioo (-1 : ℝ) 2))
    (hf₂ : ∀ i, ContDiffOn ℝ (J + 1) (f₂ i) (Ioo (-1 : ℝ) 2)) (hj : j ≤ J + 1) :
    Measurable (fun p : (Fin n₁ × Fin n₂) × ℝ =>
      |localDeriv j (f₁ p.1.1) p.2 - localDeriv j (f₂ p.1.2) p.2|) := by
  apply Measurable.abs
  apply Measurable.sub
  · exact measurable_from_prod_countable_right fun i => measurable_localDeriv (hf₁ i.1) hj
  · exact measurable_from_prod_countable_right fun i => measurable_localDeriv (hf₂ i.2) hj

/-- Finite color/time marginals dominated by Lebesgue measure have no time
atoms, even when the original event predicates are not assumed measurable. -/
lemma time_singleton_null {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (color : α → ι) (time : α → ℝ) (C : ι → ℝ≥0∞)
    (hdom : ∀ (i : ι) (E : Set ℝ), MeasurableSet E →
      μ {p | color p = i ∧ time p ∈ E} ≤ C i * volume E) (x : ℝ) :
    μ {p | time p = x} = 0 := by
  have hcell : ∀ i, μ {p | color p = i ∧ time p ∈ ({x} : Set ℝ)} = 0 := by
    intro i
    apply le_antisymm _ bot_le
    simpa using hdom i {x} (measurableSet_singleton x)
  have hcover : {p | time p = x} ⊆ ⋃ i, {p | color p = i ∧ time p ∈ ({x} : Set ℝ)} := by
    intro p hp
    exact mem_iUnion.2 ⟨color p, rfl, hp⟩
  apply le_antisymm _ bot_le
  calc
    μ {p | time p = x} ≤ μ (⋃ i, {p | color p = i ∧ time p ∈ ({x} : Set ℝ)}) := measure_mono hcover
    _ ≤ ∑ i, μ {p | color p = i ∧ time p ∈ ({x} : Set ℝ)} := measure_iUnion_fintype_le _ _
    _ = 0 := Finset.sum_eq_zero fun i _ => hcell i

end Submission.Obl.k4_matching_gap_regularization
