import Submission.Obl.k4_pair_bin_atlas_assembly.PairFacts
import Submission.Obl.k4_quadratic_atlas_normalization.StepInterface

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Filter MeasureTheory
open Submission.Obl.k4_quadratic_atlas_normalization

/-- A finite atlas construction with polynomial format budgets chosen before
the requested cofinal slack. Its input slack may be decreased. -/
def FiniteAssembly (C₂ c₂ : ℝ) : Prop :=
  ∀ L a h : ℝ, 0 < L → 0 < a → a < c₂ * L →
  ∀ M D Mb Me De : ℕ, ∃ M' D' : ℕ,
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
  ∀ Nk : ℝ, N₀ ≤ Nk → ∀ Wk : ℕ,
  ∀ (ωk : Fin Wk → ℝ) (νk : Fin Wk → Measure Trajectory)
    (Ek : Fin Wk → Set Incidence) (Bk : Fin Wk → ℝ),
  (∀ w, 0 ≤ ωk w) → (∑ w, ωk w) = 1 →
  (∀ w, IsProbabilityMeasure (νk w)) →
  (∀ w, 0 < Bk w ∧ Bk w ≤ Nk ^ Mb ∧ (Bk w)⁻¹ ≤ Nk ^ Mb) →
  (∀ w, MeasurableSet (Ek w) ∧ ∀ i, fmt 7 (Nk ^ Me) De
    {z : Fin 7 → ℝ | ((i, fun j : Fin 6 => z j.castSucc), z 6) ∈ Ek w}) →
  PairData Nk Wk ωk νk Ek Bk L a h M D η →
    RoughAt Nk Wk ωk νk Ek Bk L (C₂ * a) h M' D' ε

/-- A finite construction passes to the original cofinal sequence without
changing any law or world index. -/
theorem realization_of_finiteAssembly {C₂ c₂ : ℝ}
    (hC₂ : 0 < C₂) (hc₂ : 0 < c₂) (hfinite : FiniteAssembly C₂ c₂) : Realization := by
  refine ⟨C₂, c₂, hC₂, hc₂, ?_⟩
  intro N W ω ν E B L a h ha haL hp
  obtain ⟨M, D, hsamples⟩ := paired_has_samples hp
  obtain ⟨hN, hNt, hL, hω, hωsum, hν, ⟨Mb, hB⟩, ⟨Me, De, hE⟩, _⟩ := hp
  obtain ⟨M', D', hconstruct⟩ := hfinite L a h hL ha haL M D Mb Me De
  apply roughSys_iff.mpr
  refine ⟨M', D', ?_⟩
  intro ε hε
  obtain ⟨η, hη, hηε, N₀, hN₀, hat⟩ := hconstruct ε hε
  have hlarge : ∀ᶠ k in atTop, N₀ ≤ N k := hNt.eventually (eventually_ge_atTop N₀)
  apply ((hsamples η hη).and_eventually hlarge).mono
  rintro k ⟨⟨p⟩, hk⟩
  exact hat (N k) hk (W k) (ω k) (ν k) (E k) (B k)
    (hω k) (hωsum k) (hν k) (hB k) (hE k) p

end Submission.Obl.k4_pair_bin_atlas_assembly
