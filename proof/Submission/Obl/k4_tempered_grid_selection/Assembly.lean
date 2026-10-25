import Submission.Obl.k4_tempered_grid_selection.AnalyticSelection

namespace Submission.Obl.k4_tempered_grid_selection

open MeasureTheory Set Filter

/-- The format-preservation step for arbitrary common-label predicates. -/
def FormatSelection : Prop :=
  ∀ (N K K₀ : ℕ → ℝ) (ν : ℕ → Measure (ℕ × (Fin 6 → ℝ)))
    (E : ℕ → Set Incidence) (H : ℕ) (R U : ℝ) (T : ℕ → Set Label),
    (∀ k, 2 ≤ N k) →
    (∃ M D : ℕ, ∀ k, TemperedProblem (N k) M D (K k) (ν k) (E k)) →
    (∀ k, K k ≤ K₀ k) →
    (∀ k, ENNReal.ofReal ((K₀ k)⁻¹) ≤
      incidenceMeasure (ν k) (E k ∩ commonLabel (N k) H R U ⁻¹' T k) univ) →
    ∃ M D : ℕ, ∀ k, TemperedProblem (N k) M D (K₀ k) (ν k)
      (E k ∩ commonLabel (N k) H R U ⁻¹' T k)

/-- Analytic selection and preservation of the finite polynomial format give
exactly the required bounded grid-exponent conclusion. -/
theorem selection_from_format (hformat : FormatSelection)
    (N K : ℕ → ℝ) (ν : ℕ → Measure (ℕ × (Fin 6 → ℝ))) (E : ℕ → Set Incidence)
    (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : Subpower N K)
    (hF : ∃ M D : ℕ, ∀ k, TemperedProblem (N k) M D (K k) (ν k) (E k))
    (R U : ℝ) (hR : 0 < R) (hU : 0 < U)
    (hflat : AbsoluteContinuity N ν E R U ∧
      ∃ (C H : ℕ) (g : ℕ → ℝ → ℝ → Label → ℝ),
        Approximation N (fun k => incidenceMeasure (ν k) (E k)) R U C H g) :
    ∃ (K₀ : ℕ → ℝ) (E₀ : ℕ → Set Incidence),
      Subpower N K₀ ∧ (∀ k, K k ≤ K₀ k ∧ E₀ k ⊆ E k) ∧
      (∃ M D : ℕ, ∀ k, TemperedProblem (N k) M D (K₀ k) (ν k) (E₀ k)) ∧
      ∃ (A : ℕ) (a : ℕ → ℚ → ℚ → ℝ),
        (∀ k q s, |a k q s| ≤ (A : ℝ)) ∧
        GridTypical N (fun k => incidenceMeasure (ν k) (E₀ k)) R U a := by
  obtain ⟨M, D, hF⟩ := hF
  obtain ⟨hac, C, H, g, happrox⟩ := hflat
  have hE (k : ℕ) : MeasurableSet (E k) := (hF k).2.2.1
  have hmass (k : ℕ) : incidenceMeasure (ν k) (E k) univ ≤ 1 := by
    letI := (hF k).1
    exact k4_profile_density_bounds.selected_mass_le_one (ν k) (E k) (hF k).2.2.2.1
  have hlower (k : ℕ) : ENNReal.ofReal ((K k)⁻¹) ≤ incidenceMeasure (ν k) (E k) univ := by
    rcases hF k with ⟨_, _, _, _, _, _, _, hm⟩
    exact hm
  obtain ⟨K₀, T, a, hK₀, hKK₀, hretain, ha, htyp⟩ :=
    analytic_selection N K ν E hN hNt hK hE hmass hlower R U hR hU hac C H g happrox
  refine ⟨K₀, (fun k => E k ∩ commonLabel (N k) H R U ⁻¹' T k), hK₀,
    (fun k => ⟨hKK₀ k, inter_subset_left⟩), ?_, C, a, ha, htyp⟩
  exact hformat N K K₀ ν E H R U T hN ⟨M, D, hF⟩ hKK₀ hretain

end Submission.Obl.k4_tempered_grid_selection
