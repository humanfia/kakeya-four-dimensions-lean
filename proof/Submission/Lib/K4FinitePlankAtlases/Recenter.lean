import Submission.Lib.K4FinitePlankAtlases.PlankFrame

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open Set

/-- Recenter at a contained bounded trajectory. Doubling the two widths gives a
valid whole-time chart with bounded center and speed and the same chosen axes. -/
theorem recenter_full_plank {ι : Type*} [DecidableEq ι] (b u : ι → Plane)
    (S : Finset ι) (hS : S.Nonempty) (hbu : ∀ i ∈ S, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1)
    {c w e₁ e₂ : Plane} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0)
    (hfit : ∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a ∧
      |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β) :
    ∃ c' w' : Plane, ‖c'‖ ≤ 1 ∧ ‖w'‖ ≤ 1 ∧ ∀ i ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin ((plankFrame (2 * a) (2 * β) e₁ e₂)⁻¹)
        (b i + t • u i - c' - t • w')‖ ≤ 2 := by
  obtain ⟨i₀, hi₀⟩ := hS
  refine ⟨b i₀, u i₀, (hbu i₀ hi₀).1, (hbu i₀ hi₀).2, ?_⟩
  intro i hi t ht
  have heq : b i + t • u i - b i₀ - t • u i₀ =
      (b i + t • u i - c - t • w) - (b i₀ + t • u i₀ - c - t • w) := by abel
  rw [heq]
  apply plankFrame_fit (by positivity) (by positivity) h₁ h₂ ho
  · rw [inner_sub_left]
    exact (abs_sub _ _).trans (by linarith [(hfit i hi t ht).1, (hfit i₀ hi₀ t ht).1])
  · rw [inner_sub_left]
    exact (abs_sub _ _).trans (by linarith [(hfit i hi t ht).2, (hfit i₀ hi₀ t ht).2])

/-- The recentering costs only a fixed factor four in the true spatial Jacobian. -/
theorem recentered_plank_jacobian {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {e₁ e₂ : Plane} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0) :
    |Matrix.det (plankFrame (2 * a) (2 * β) e₁ e₂)| = 4 * a * β := by
  rw [plankFrame_abs_det (by positivity) (by positivity) h₁ h₂ ho]
  ring

end Submission.Lib.K4FinitePlankAtlases
