-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FrozenAdapter
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_separated_projection_dichotomy`

Proposition 8.9 of Wang-Zahl (sticky Kakeya, Section 8.3) in counting form,
from Proposition 8.5.  The reduction (anisotropic rescaling, localization to
strips, coarsening of scales) is the Section 8 development of session x0272
on o103, ported into this obligation's namespace; it proves the needed
projection estimates itself, so the Kaufman premise is not used.
-/

theorem WangZahlLot.wz_separated_projection_dichotomy : (∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ C d : ℝ, 0 < δ → δ ≤ δ₀ → 1 ≤ C → 0 < d → ∀ (F Λ : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), F.Finite → Λ.Finite → (∀ θ ∈ Λ, ‖θ‖ = 1) → (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((F ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * F.ncard ∧ ((Λ ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * Λ.ncard) → H ⊆ Λ ×ˢ F → H.Nonempty → d * Λ.ncard * F.ncard ≤ H.ncard → ∃ θ ∈ Λ, ∀ (m : ℕ) (cc : Fin m → ℝ), {t : ℝ | ∃ a, (θ, a) ∈ H ∧ t = inner ℝ θ a} ⊆ (⋃ j, Metric.closedBall (cc j) δ) → d ^ 3 * δ ^ (ε - 1) ≤ C ^ 2 * m) → (∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∃ α δ₀ : ℝ, 0 < α ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (F G G' : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Fr δ (δ ^ (-κ)) F → Fr δ (δ ^ (-κ)) G → Fr δ (δ ^ (-κ)) G' → (∀ b ∈ G, ∀ b' ∈ G', 1 / 4 ≤ dist b b') → (∀ (e : EuclideanSpace ℝ (Fin 2)) (c r : ℝ), ‖e‖ = 1 → δ ≤ r → ({b ∈ G | |inner ℝ b e - c| < r}.ncard : ℝ) ≤ (δ ^ (-κ) * r) ^ ζ * G.ncard ∧ ({b ∈ G' | |inner ℝ b e - c| < r}.ncard : ℝ) ≤ (δ ^ (-κ) * r) ^ ζ * G'.ncard) → H ⊆ F ×ˢ (G ×ˢ G') → H.Nonempty → δ ^ α * F.ncard * G.ncard * G'.ncard ≤ H.ncard → ∀ (m : ℕ) (cc : Fin m → ℝ), {t : ℝ | ∃ h ∈ H, t = inner ℝ h.1 (h.2.1 - h.2.2)} ⊆ (⋃ j, Metric.closedBall (cc j) δ) → δ ^ (ε - 1) ≤ (m : ℝ)) → ∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (F G G' : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Fr δ (δ ^ (-η)) F → Fr δ (δ ^ (-η)) G → Fr δ (δ ^ (-η)) G' → (∀ a ∈ F, 1 / 2 ≤ ‖a‖ ∧ ∀ a' ∈ F, dist a a' ≤ 1 / 10) → (∀ b ∈ G, ∀ b' ∈ G, dist b b' ≤ 1 / 10) → (∀ b ∈ G', ∀ b' ∈ G', dist b b' ≤ 1 / 10) → (∀ b ∈ G, ∀ b' ∈ G', 1 / 2 ≤ dist b b') → H ⊆ F ×ˢ (G ×ˢ G') → H.Nonempty → δ ^ η * F.ncard * G.ncard * G'.ncard ≤ H.ncard → (∃ e e' : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 ∧ ‖e'‖ = 1 ∧ inner ℝ e e' = 0 ∧ ∃ c c' : ℝ, δ ^ (ε - 1) ≤ ({a ∈ F | |inner ℝ a e - c| < δ}.ncard : ℝ) ∧ δ ^ (ε - 1) ≤ ({b ∈ G | |inner ℝ b e' - c'| < δ}.ncard : ℝ)) ∨ ∃ ρ a L : ℝ, δ ≤ ρ ∧ δ ^ (-η) * ρ ≤ L ∧ ∀ (m : ℕ) (cc : Fin m → ℝ), Set.Icc a (a + L) ∩ {t : ℝ | ∃ h ∈ H, t = inner ℝ h.1 (h.2.1 - h.2.2)} ⊆ (⋃ j, Metric.closedBall (cc j) ρ) → (L / ρ) ^ (1 - ε) ≤ (m : ℝ) := by
  intro _hKaufman hP85
  exact WangZahlLot.Obl.wz_separated_projection_dichotomy.separated_set_statement_of_set_nonconcentrated
    (WangZahlLot.Obl.wz_separated_projection_dichotomy.boundedSetNonconcentratedPrinciple_of_frozen hP85)
