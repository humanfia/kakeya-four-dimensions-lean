import Submission.Obl.k4_scalar_marked_profile_selection.Interface

noncomputable section

namespace Submission.Obl.k4_scalar_marked_profile_selection

open MeasureTheory Filter

theorem subpower_comp {N K : ℕ → ℝ} (hK : Subpower N K)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : Subpower (N ∘ φ) (K ∘ φ) := by
  exact ⟨fun k => hK.1 (φ k), fun ε hε => hφ.tendsto_atTop.eventually (hK.2 ε hε)⟩

theorem homogeneous_comp {N : ℕ → ℝ} {s V : ℝ} {μ : ℕ → Measure Incidence}
    {F : ℝ → ℝ → ℝ} (h : homogeneous N s V μ F)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    homogeneous (N ∘ φ) s V (μ ∘ φ) F := by
  rcases h with ⟨g, G, hg, hG, hgp, hGp⟩
  refine ⟨fun k => g (φ k), fun k => G (φ k),
    fun k => hg (φ k), fun k => hG (φ k), ?_, ?_⟩
  · intro r τ hr hrs hτ
    obtain ⟨c, hc, hwin⟩ := hgp r τ hr hrs hτ
    exact ⟨c, hc, hφ.tendsto_atTop.eventually hwin⟩
  · intro r u τ hr hrs hu huV hτ
    obtain ⟨c, hc, hwin⟩ := hGp r u τ hr hrs hu huV hτ
    exact ⟨c, hc, hφ.tendsto_atTop.eventually hwin⟩

end Submission.Obl.k4_scalar_marked_profile_selection
