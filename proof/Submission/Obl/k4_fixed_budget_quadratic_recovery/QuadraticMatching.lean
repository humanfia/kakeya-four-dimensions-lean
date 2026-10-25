/- Adapted within this LOT tree from o120/x0402, commit 70956fccdfd7e9924a3fa094355c65a03c16ee9c,
Submission/Obl/k4_unbounded_width_exclusion/QuadraticMatching.lean. -/
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticCoefficients
import Submission.Lib.K4QuadSheetMatching.Matching

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Finset Set
open scoped Classical
open Submission.Lib.K4QuadSheetMatching

theorem quadratic_coefficients_unit_square {c : Fin 6 → ℝ} {H : ℝ}
    (h : ∀ z ∈ unitSq, |quadraticValue c z.1 z.2| ≤ H) :
    ∀ i, |c i| ≤ 864 * H := by
  intro i
  calc
    _ ≤ 8 * (108 * H) := quadratic_coefficients_bound (by
      intro t ht z hz
      exact qev_ext_bound h (t, z) (Or.inl ⟨ht, ⟨hz.1, by linarith [hz.2]⟩⟩)) i
    _ = _ := by ring

theorem quadratic_coefficients_of_not_separated {c c' : Fin 6 → ℝ} {H : ℝ}
    (h : ¬ ∃ z ∈ unitSq, H ≤ |quadraticValue c z.1 z.2 - quadraticValue c' z.1 z.2|) :
    ∀ i, |c i - c' i| ≤ 864 * H := by
  apply quadratic_coefficients_unit_square (c := c - c')
  intro z hz
  change |qev (c - c') z.1 z.2| ≤ H
  rw [qev_sub]
  exact (lt_of_not_ge (fun he => h ⟨z, hz, he⟩)).le

/-- The contradiction form of local matching bounds all globally
separated pairs at once, under their original unnormalized pair law. -/
theorem quadratic_separated_pair_mass
    (hTC : TwoColorStatement) {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
    ∀ (n₁ n₂ : ℕ) (c₁ : Fin n₁ → Fin 6 → ℝ) (c₂ : Fin n₂ → Fin 6 → ℝ)
      (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ)
      (ρ : Fin n₁ × Fin n₂ → Measure (ℝ × ℝ)),
    (∀ i, IsFiniteMeasure (ρ i)) →
    (n₁ : ℝ) ≤ R ^ (d + ε) → (n₂ : ℝ) ≤ R ^ (d + ε) →
    (∀ i, ∀ z ∈ unitSq, |quadraticValue (c₁ i) z.1 z.2| ≤ R ^ ε) →
    (∀ j, ∀ z ∈ unitSq, |quadraticValue (c₂ j) z.1 z.2| ≤ R ^ ε) →
    (∀ i, 0 ≤ π₁ i) → (∀ j, 0 ≤ π₂ j) → ∑ i, π₁ i = 1 → ∑ j, π₂ j = 1 →
    (∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ j, ρ (i, j) B ≤ ENNReal.ofReal (R ^ ε * π₁ i) * volume B) →
    (∀ j (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ i, ρ (i, j) B ≤ ENNReal.ofReal (R ^ ε * π₂ j) * volume B) →
    (∀ i, ∀ᵐ z ∂ρ i, z ∈ unitSq ∧
      |quadraticValue (c₁ i.1) z.1 z.2 - quadraticValue (c₂ i.2) z.1 z.2| ≤
        R ^ (-1 + ε)) →
    (∑ i, if (∃ w ∈ unitSq, R ^ (-ε) ≤
      |quadraticValue (c₁ i.1) w.1 w.2 - quadraticValue (c₂ i.2) w.1 w.2|)
      then ρ i univ else 0) < ENNReal.ofReal (R ^ (-ε)) := by
  obtain ⟨ε, hε, R₀, hR₀, hmatch⟩ := quad_sheet_matching hTC hd hd1
  refine ⟨ε, hε, R₀, hR₀, ?_⟩
  intro R hR n₁ n₂ c₁ c₂ π₁ π₂ ρ hfin hn₁ hn₂ hb₁ hb₂ hp₁ hp₂ hs₁ hs₂ hm₁ hm₂ hnear
  classical
  let bad : Fin n₁ × Fin n₂ → Prop := fun i => ∃ w ∈ unitSq,
    R ^ (-ε) ≤ |quadraticValue (c₁ i.1) w.1 w.2 - quadraticValue (c₂ i.2) w.1 w.2|
  let σ : Fin n₁ × Fin n₂ → Measure (ℝ × ℝ) := fun i => if bad i then ρ i else 0
  have hσle (i : Fin n₁ × Fin n₂) : σ i ≤ ρ i := by
    dsimp [σ]
    split_ifs
    · exact le_rfl
    · exact bot_le
  have hσfin (i : Fin n₁ × Fin n₂) : IsFiniteMeasure (σ i) := by
    have := hfin i
    exact isFiniteMeasure_of_le (ρ i) (hσle i)
  by_contra hsmall
  apply hmatch R hR n₁ n₂ c₁ c₂ π₁ π₂ σ hσfin hn₁ hn₂ hb₁ hb₂ hp₁ hp₂ hs₁ hs₂
  · intro i B hB
    exact (Finset.sum_le_sum (fun j _ => hσle (i, j) B)).trans (hm₁ i B hB)
  · intro j B hB
    exact (Finset.sum_le_sum (fun i _ => hσle (i, j) B)).trans (hm₂ j B hB)
  · have hσuniv (i : Fin n₁ × Fin n₂) : σ i univ =
        if bad i then ρ i univ else 0 := by
      by_cases hi : bad i <;> simp [σ, hi]
    simp_rw [hσuniv]
    exact le_of_not_gt hsmall
  · intro i
    by_cases hi : bad i
    · rw [show σ i = ρ i by simp only [σ, hi, ite_true]]
      filter_upwards [hnear i] with z hz
      exact ⟨hz.1, hz.2, hi⟩
    · simp [σ, hi]

end Submission.Obl.k4_fixed_budget_quadratic_recovery
