-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CenteredNonconcCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.BoundedNonconcCore

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

/-- The bounded nonconcentrated input in coordinates whose common strip may
have a nonzero center. This form accommodates anisotropic normalization. -/
def CenteredNonconcentratedAt (δ ℓ ζ α ε : ℝ) : Prop :=
  ∀ (F G U : Finset Plane) (H : Finset Triple) (b : Plane),
    (∀ x ∈ F, ‖x‖ ≤ 5) → (∀ x ∈ G, ‖x - b‖ ≤ 5) → (∀ x ∈ U, ‖x - b‖ ≤ 5) →
    ClosedFiniteFrostman δ (δ ^ (-ℓ)) F →
    ClosedFiniteFrostman δ (δ ^ (-ℓ)) G →
    ClosedFiniteFrostman δ (δ ^ (-ℓ)) U →
    IndexedLineFrostman δ (δ ^ (-ℓ)) ζ (fun b : G => (b : Plane)) →
    IndexedLineFrostman δ (δ ^ (-ℓ)) ζ (fun x : U => (x : Plane)) →
    (∀ x ∈ G, ∀ y ∈ U, 1 / 2 ≤ ‖x - y‖) →
    H ⊆ F ×ˢ (G ×ˢ U) → H.Nonempty →
    δ ^ α * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ) →
    CoverLower δ (DotSet (↑H : Set Triple)) (δ ^ (ε - 1))

def CenteredNonconcentratedPrinciple : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ ℓ : ℝ, 0 < ℓ ∧
    ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → ∃ α δ₀ : ℝ, 0 < α ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → CenteredNonconcentratedAt δ ℓ ζ α ε

end WangZahlLot.Obl.wz_separated_projection_dichotomy
