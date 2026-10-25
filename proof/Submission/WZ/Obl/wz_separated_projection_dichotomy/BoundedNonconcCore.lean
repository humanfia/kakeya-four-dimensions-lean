-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.BoundedNonconcCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.NonconcentratedCore

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

/-- A bounded finite input, with separation imposed only when `sep` is true.
The cross separation of one quarter matches the set interface of Prop. 8.5. -/
def BoundedNonconcentratedAt (sep : Bool) (δ ℓ ζ α ε : ℝ) : Prop :=
  ∀ (F G U : Finset Plane) (H : Finset Triple),
    (∀ x ∈ F, ‖x‖ ≤ 4) → (∀ x ∈ G, ‖x‖ ≤ 4) → (∀ x ∈ U, ‖x‖ ≤ 4) →
    (sep = true → ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ dist x y) →
    (sep = true → ∀ x ∈ G, ∀ y ∈ G, x ≠ y → δ ≤ dist x y) →
    (sep = true → ∀ x ∈ U, ∀ y ∈ U, x ≠ y → δ ≤ dist x y) →
    ClosedFiniteFrostman δ (δ ^ (-ℓ)) F →
    ClosedFiniteFrostman δ (δ ^ (-ℓ)) G →
    ClosedFiniteFrostman δ (δ ^ (-ℓ)) U →
    IndexedLineFrostman δ (δ ^ (-ℓ)) ζ (fun b : G => (b : Plane)) →
    IndexedLineFrostman δ (δ ^ (-ℓ)) ζ (fun x : U => (x : Plane)) →
    (∀ b ∈ G, ∀ x ∈ U, 1 / 4 ≤ ‖b - x‖) →
    H ⊆ F ×ˢ (G ×ˢ U) → H.Nonempty →
    δ ^ α * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ) →
    CoverLower δ (DotSet (↑H : Set Triple)) (δ ^ (ε - 1))

def BoundedNonconcentratedPrinciple (sep : Bool) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ ℓ : ℝ, 0 < ℓ ∧
    ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → ∃ α δ₀ : ℝ, 0 < α ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → BoundedNonconcentratedAt sep δ ℓ ζ α ε

end WangZahlLot.Obl.wz_separated_projection_dichotomy
