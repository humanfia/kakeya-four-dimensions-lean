-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.FrozenReduction
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_ad_dichotomy_from_separated`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated`, where others can
reuse them, or make them `private`. Only this file and `WangZahlLot/Obl/wz_ad_dichotomy_from_separated/`
belong to this obligation.
-/

theorem WangZahlLot.wz_ad_dichotomy_from_separated : (∀ Fr, Fr = (fun (δ C : ℝ) (X : Set (EuclideanSpace ℝ (Fin 2))) => X.Finite ∧ (∀ x ∈ X, ‖x‖ ≤ 4 ∧ ∀ y ∈ X, x ≠ y → δ ≤ dist x y) ∧ ∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), δ ≤ r → ((X ∩ Metric.closedBall x r).ncard : ℝ) ≤ C * r * X.ncard) → ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ (F G G' : Set (EuclideanSpace ℝ (Fin 2))) (H : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))), Fr δ (δ ^ (-η)) F → Fr δ (δ ^ (-η)) G → Fr δ (δ ^ (-η)) G' → (∀ a ∈ F, 1 / 2 ≤ ‖a‖ ∧ ∀ a' ∈ F, dist a a' ≤ 1 / 10) → (∀ b ∈ G, ∀ b' ∈ G, dist b b' ≤ 1 / 10) → (∀ b ∈ G', ∀ b' ∈ G', dist b b' ≤ 1 / 10) → (∀ b ∈ G, ∀ b' ∈ G', 1 / 2 ≤ dist b b') → H ⊆ F ×ˢ (G ×ˢ G') → H.Nonempty → δ ^ η * F.ncard * G.ncard * G'.ncard ≤ H.ncard → (∃ e e' : EuclideanSpace ℝ (Fin 2), ‖e‖ = 1 ∧ ‖e'‖ = 1 ∧ inner ℝ e e' = 0 ∧ ∃ c c' : ℝ, δ ^ (ε - 1) ≤ ({a ∈ F | |inner ℝ a e - c| < δ}.ncard : ℝ) ∧ δ ^ (ε - 1) ≤ ({b ∈ G | |inner ℝ b e' - c'| < δ}.ncard : ℝ)) ∨ ∃ ρ a L : ℝ, δ ≤ ρ ∧ δ ^ (-η) * ρ ≤ L ∧ ∀ (m : ℕ) (cc : Fin m → ℝ), Set.Icc a (a + L) ∩ {t : ℝ | ∃ h ∈ H, t = inner ℝ h.1 (h.2.1 - h.2.2)} ⊆ (⋃ j, Metric.closedBall (cc j) ρ) → (L / ρ) ^ (1 - ε) ≤ (m : ℝ)) → ∀ε:ℝ,0<ε→∃η δ₀:ℝ,0<η∧0<δ₀∧∀δ:ℝ,0<δ→δ≤δ₀→∀F G:Set (EuclideanSpace ℝ (Fin 2)),(∀a ∈ F,∀i:Fin 2,0≤a i∧a i≤1)→(∀b ∈ G,∀i:Fin 2,0≤b i∧b i≤1)→(∀(x:(EuclideanSpace ℝ (Fin 2))) (ρ r:ℝ),δ≤ρ→ρ≤r→∃(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),F∩Metric.ball x r⊆(⋃ j,Metric.closedBall (cc j) ρ)∧(m:ℝ)≤δ^(-η)*(r/ρ))→(∀(x:(EuclideanSpace ℝ (Fin 2))) (ρ r:ℝ),δ≤ρ→ρ≤r→∃(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),G∩Metric.ball x r⊆(⋃ j,Metric.closedBall (cc j) ρ)∧(m:ℝ)≤δ^(-η)*(r/ρ))→((∃(e b₀:(EuclideanSpace ℝ (Fin 2))) (c:ℝ),‖e‖=1∧(∀(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),Metric.thickening δ {a|inner ℝ a e=c}∩F⊆(⋃ j,Metric.closedBall (cc j) δ)→δ^(ε-1)≤(m:ℝ))∧(∀(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),Metric.thickening δ (Set.range (fun t:ℝ=>b₀+t • e))∩G⊆(⋃ j,Metric.closedBall (cc j) δ)→δ^(ε-1)≤(m:ℝ)))∨(∀Q:Set (EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)),Q⊆F ×ˢ (G ×ˢ G)→(∀(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2))),Q⊆(⋃ j,Metric.closedBall (cc j) δ)→δ^(η-3)≤(m:ℝ))→∃ρ a L:ℝ,δ≤ρ∧δ^(-η)*ρ≤L∧∀(m:ℕ) (cc:Fin m→ℝ),Set.Icc a (a+L)∩{t:ℝ|∃h ∈ Q,t=inner ℝ h.1 (h.2.1-h.2.2)}⊆(⋃ j,Metric.closedBall (cc j) ρ)→(L/ρ)^(1-ε)≤(m:ℝ))) := by
  exact fun h => WangZahlLot.Obl.wz_ad_dichotomy_from_separated.from_proposition_eight_nine h
