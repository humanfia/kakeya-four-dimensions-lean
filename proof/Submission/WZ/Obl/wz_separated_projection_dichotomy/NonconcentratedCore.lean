-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.NonconcentratedCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.LineCounting
import Submission.WZ.Obl.wz_separated_projection_dichotomy.IndexedGeometry

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set

/-- The finite nonconcentrated projection input at one scale. No point
separation is imposed; all regularity is expressed by counting bounds. -/
def NonconcentratedAt (δ ℓ ζ α ε : ℝ) : Prop :=
  ∀ (F G U : Finset Plane) (H : Finset Triple),
    ClosedFiniteFrostman δ (δ ^ (-ℓ)) F →
    ClosedFiniteFrostman δ (δ ^ (-ℓ)) G →
    ClosedFiniteFrostman δ (δ ^ (-ℓ)) U →
    IndexedLineFrostman δ (δ ^ (-ℓ)) ζ (fun b : G => (b : Plane)) →
    IndexedLineFrostman δ (δ ^ (-ℓ)) ζ (fun x : U => (x : Plane)) →
    (∀ b ∈ G, ∀ x ∈ U, 1 / 2 ≤ ‖b - x‖ ∧ ‖b - x‖ ≤ 8) →
    H ⊆ F ×ˢ (G ×ˢ U) → H.Nonempty →
    δ ^ α * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ) →
    CoverLower δ (DotSet (↑H : Set Triple)) (δ ^ (ε - 1))

def NonconcentratedPrinciple : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ ℓ : ℝ, 0 < ℓ ∧
    ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → ∃ α δ₀ : ℝ, 0 < α ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → NonconcentratedAt δ ℓ ζ α ε

end WangZahlLot.Obl.wz_separated_projection_dichotomy
