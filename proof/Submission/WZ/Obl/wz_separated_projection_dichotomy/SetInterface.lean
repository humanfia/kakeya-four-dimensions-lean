-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.SetInterface.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FromSeparated
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CardLines

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

/-- The exact finite-set interface supplied by session x0289 for Proposition 8.9. -/
def SeparatedSetStatement : Prop :=
∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (F G G' : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Fr δ (δ ^ (-η)) F → Fr δ (δ ^ (-η)) G → Fr δ (δ ^ (-η)) G' → (∀ a ∈ F, 1 / 2 ≤ ‖a‖ ∧ ∀ a' ∈ F, dist a a' ≤ 1 / 10) → (∀ b ∈ G, ∀ b' ∈ G, dist b b' ≤ 1 / 10) → (∀ b ∈ G', ∀ b' ∈ G', dist b b' ≤ 1 / 10) → (∀ b ∈ G, ∀ b' ∈ G', 1 / 2 ≤ dist b b') → H ⊆ F ×ˢ (G ×ˢ G') → H.Nonempty → δ ^ η * F.ncard * G.ncard * G'.ncard ≤ H.ncard → (∃ e e' : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 ∧ ‖e'‖ = 1 ∧ inner ℝ e e' = 0 ∧ ∃ c c' : ℝ, δ ^ (ε - 1) ≤ ({a ∈ F | |inner ℝ a e - c| < δ}.ncard : ℝ) ∧ δ ^ (ε - 1) ≤ ({b ∈ G | |inner ℝ b e' - c'| < δ}.ncard : ℝ)) ∨ ∃ ρ a L : ℝ, δ ≤ ρ ∧ δ ^ (-η) * ρ ≤ L ∧ ∀ (m : ℕ) (cc : Fin m → ℝ), Set.Icc a (a + L) ∩ {t : ℝ | ∃ h ∈ H, t = inner ℝ h.1 (h.2.1 - h.2.2)} ⊆ (⋃ j, Metric.closedBall (cc j) ρ) → (L / ρ) ^ (1 - ε) ≤ (m : ℝ)

end WangZahlLot.Obl.wz_separated_projection_dichotomy
