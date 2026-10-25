/- Adapted from this LOT tree, o151, session x0508, commit 274d45f,
   Submission/Obl/k4_known_atlas_normalization_composition/AssignmentComposition.lean. Earlier provenance comments are retained. -/
import Submission.Obl.k4_native_finite_terminal_atlas_lift.DyadicComposition

namespace Submission.Obl.k4_native_finite_terminal_atlas_lift

/-- Parent assignments are disjoint only at equal original world and parent
block. Child disjointness supplies the other case after dyadic concatenation. -/
theorem composite_assignments_separated {m n W T U : ℕ}
    (γ₀ : Fin m → Fin W) (j₀ : Fin m → Fin (2 ^ T))
    (A₀ : Fin m → Set Trajectory) (θ : Fin m → Trajectory → Trajectory)
    (γ₁ : Fin n → Fin m) (j₁ : Fin n → Fin (2 ^ U)) (A₁ : Fin n → Set Trajectory)
    (h₀ : ∀ b b', b ≠ b' → γ₀ b = γ₀ b' → j₀ b = j₀ b' → Disjoint (A₀ b) (A₀ b'))
    (h₁ : ∀ b b', b ≠ b' → γ₁ b = γ₁ b' → j₁ b = j₁ b' → Disjoint (A₁ b) (A₁ b')) :
    ∀ b b', b ≠ b' → γ₀ (γ₁ b) = γ₀ (γ₁ b') →
      compositeBlock (j₀ (γ₁ b)) (j₁ b) = compositeBlock (j₀ (γ₁ b')) (j₁ b') →
      Disjoint (A₀ (γ₁ b) ∩ θ (γ₁ b) ⁻¹' A₁ b) (A₀ (γ₁ b') ∩ θ (γ₁ b') ⁻¹' A₁ b') := by
  intro b b' hbb hγ hj
  obtain ⟨hj₀, hj₁⟩ := compositeBlock_injective hj
  apply Set.disjoint_left.mpr
  intro l hl hl'
  by_cases hpar : γ₁ b = γ₁ b'
  · have hdis := Set.disjoint_left.mp (h₁ b b' hbb hpar hj₁)
    apply hdis hl.2
    change θ (γ₁ b) l ∈ A₁ b'
    rw [hpar]
    exact hl'.2
  · exact Set.disjoint_left.mp (h₀ _ _ hpar hγ hj₀) hl.1 hl'.1

end Submission.Obl.k4_native_finite_terminal_atlas_lift
