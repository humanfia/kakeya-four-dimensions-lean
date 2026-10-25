import Submission.Obl.k4_two_color_matching.LossReduction

/-! Choose a cofinal subsequence realizing countably many fixed-tolerance
eventual requirements at one positive vanishing tolerance. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open Filter

theorem vanishing_error_subsequence (P : ℝ → ℕ → Prop)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, P ε k) :
    ∃ (ψ : ℕ → ℕ) (error : ℕ → ℝ), StrictMono ψ ∧ (∀ k, 0 < error k) ∧
      (∀ k, error k ≤ 1) ∧ Tendsto error atTop (nhds 0) ∧ ∀ k, P (error k) (ψ k) := by
  let error := Submission.Obl.k4_two_color_matching.lossExponent
  have he : ∀ k, 0 < error k := Submission.Obl.k4_two_color_matching.lossExponent_pos
  have he1 : ∀ k, error k ≤ 1 := by
    intro k
    dsimp [error, Submission.Obl.k4_two_color_matching.lossExponent]
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ) + 1)).mpr
    simp
  have helim : Tendsto error atTop (nhds 0) :=
    Submission.Obl.k4_two_color_matching.lossExponent_tendsto
  obtain ⟨ψ, hψ, hh⟩ := extraction_forall_of_eventually (fun k => hP (error k) (he k))
  exact ⟨ψ, error, hψ, he, he1, helim, hh⟩

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
