import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Selection

/-!
# Assembly

Flattening supplies the table approximation, whole-cell selection supplies
semialgebraic sub-events with typical windows at the rational depths, and the
profile compactness of `ProfileAssembly` passes to a subsequence with a full pure
profile. Priors and weights are only reindexed.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter

/-- Pure multi-world homogenization, given scalar joint base flattening. -/
theorem homogenization_of_flattening (hflat : ScalarFlatteningStatement)
    (p : Problem) (hp : RawScalar p) :
    ∃ (φ : ℕ → ℕ) (K : ℕ → ℝ) (M D : ℕ)
      (E : (k : ℕ) → Fin (p.1 (φ k)) → Set Incidence)
      (ρ : (k : ℕ) → Fin (p.1 (φ k)) → ℝ → Observation → ENNReal)
      (F : ℝ → ℝ),
      StrictMono φ ∧ (∀ k a, E k a ⊆ event p (φ k) a) ∧
        RawScalar (selectedProblem p φ K M D E ρ F) ∧
        PureProfile (selectedProblem p φ K M D E ρ F) := by
  obtain ⟨C, H, g, happ⟩ := hflat p hp
  obtain ⟨K₁, M₁, D₁, E₁, hE₁, hraw, hd, hgrid⟩ := whole_cell_selection p hp happ
  obtain ⟨φ, F, hφ, hraw', hpure⟩ := pure_profile_from_grid hraw hd hgrid
  exact ⟨φ, K₁ ∘ φ, M₁, D₁, (fun k => E₁ (φ k)),
    (fun k => density (withEvents p K₁ M₁ D₁ E₁) (φ k)), F, hφ,
    (fun k a => hE₁ (φ k) a), hraw', hpure⟩

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
