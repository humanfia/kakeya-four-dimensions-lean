/-
Adapted from: here:o107
Written in this tree by x0353.
-/
import Mathlib
import Submission.Lib.K4HorizontalCoercivity.HorizontalInterpolation

/-! Three actual velocity witnesses under an interval mass ceiling. -/

namespace Submission.Lib.K4HorizontalCoercivity

open MeasureTheory Set
open scoped ENNReal

/-- Two small velocity intervals cannot cover the retained law. No conditional
probability or change of prior is needed to select the actual witnesses. -/
theorem exists_three_velocity_witnesses
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) (v : Ω → ℝ)
    (r : ℝ) (b : ℝ≥0∞)
    (hcap : ∀ w : ℝ, μ (A ∩ {p | |v p - w| ≤ r}) ≤ b)
    (hmass : b + b < μ A) :
    ∃ p₀ ∈ A, ∃ p₁ ∈ A, ∃ p₂ ∈ A,
      r < |v p₀ - v p₁| ∧ r < |v p₀ - v p₂| ∧ r < |v p₁ - v p₂| := by
  classical
  have hne : A.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    simp [h] at hmass
  obtain ⟨p₀, hp₀⟩ := hne
  have hex₁ : ∃ p₁ ∈ A, r < |v p₁ - v p₀| := by
    by_contra h
    have hsub : A ⊆ A ∩ {p | |v p - v p₀| ≤ r} := by
      intro p hp
      refine ⟨hp, ?_⟩
      by_contra hn
      exact h ⟨p, hp, lt_of_not_ge hn⟩
    have hb : μ A ≤ b + b :=
      ((measure_mono hsub).trans (hcap (v p₀))).trans (le_add_right le_rfl)
    exact hmass.not_ge hb
  obtain ⟨p₁, hp₁, h₁₀⟩ := hex₁
  have hex₂ : ∃ p₂ ∈ A, r < |v p₂ - v p₀| ∧ r < |v p₂ - v p₁| := by
    by_contra h
    have hsub : A ⊆ (A ∩ {p | |v p - v p₀| ≤ r}) ∪
        (A ∩ {p | |v p - v p₁| ≤ r}) := by
      intro p hp
      by_cases h₀ : |v p - v p₀| ≤ r
      · exact Or.inl ⟨hp, h₀⟩
      · right
        refine ⟨hp, ?_⟩
        by_contra h₁
        exact h ⟨p, hp, lt_of_not_ge h₀, lt_of_not_ge h₁⟩
    have hb : μ A ≤ b + b :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans
        (add_le_add (hcap (v p₀)) (hcap (v p₁))))
    exact hmass.not_ge hb
  obtain ⟨p₂, hp₂, h₂₀, h₂₁⟩ := hex₂
  refine ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, ?_, ?_, ?_⟩
  · simpa only [abs_sub_comm] using h₁₀
  · simpa only [abs_sub_comm] using h₂₀
  · simpa only [abs_sub_comm] using h₂₁

/-- Interval nonconcentration provides actual witnesses for quadratic interpolation. -/
theorem horizontal_quadratic_interpolation_of_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω) (v : Ω → ℝ)
    (a b c K E : ℝ) (hK : 1 ≤ K) (hE : 0 ≤ E) (cap : ℝ≥0∞)
    (hcap : ∀ w : ℝ, μ (A ∩ {p | |v p - w| ≤ K⁻¹}) ≤ cap)
    (hmass : cap + cap < μ A) (hv : ∀ p ∈ A, |v p| ≤ K)
    (hval : ∀ p ∈ A, |a + b * v p + c * (v p) ^ 2| ≤ E) :
    |a| + |b| + |c| ≤ 32 * K ^ 4 * E := by
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, h₀₁, h₀₂, h₁₂⟩ :=
    exists_three_velocity_witnesses μ A v K⁻¹ cap hcap hmass
  have h₁₀ : K⁻¹ < |v p₁ - v p₀| := by simpa only [abs_sub_comm] using h₀₁
  have h₂₀ : K⁻¹ < |v p₂ - v p₀| := by simpa only [abs_sub_comm] using h₀₂
  have h₂₁ : K⁻¹ < |v p₂ - v p₁| := by simpa only [abs_sub_comm] using h₁₂
  let w : Fin 3 → ℝ := ![v p₀, v p₁, v p₂]
  apply horizontal_quadratic_interpolation a b c K E hK hE w
  · intro i
    fin_cases i <;> simp only [w]
    all_goals first | exact hv p₀ hp₀ | exact hv p₁ hp₁ | exact hv p₂ hp₂
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [w]
    all_goals
      first
      | exact (hij rfl).elim
      | exact h₀₁.le
      | exact h₀₂.le
      | exact h₁₂.le
      | exact h₁₀.le
      | exact h₂₀.le
      | exact h₂₁.le
  · intro i
    fin_cases i <;> simp only [w]
    all_goals first | exact hval p₀ hp₀ | exact hval p₁ hp₁ | exact hval p₂ hp₂

end Submission.Lib.K4HorizontalCoercivity
