-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_projection_dichotomy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_kaufman_projection_count
import Submission.WZ.Obl.wz_osw_thin_tubes_bootstrap
import Submission.WZ.Obl.wz_nonconcentrated_dot_products
import Submission.WZ.Obl.wz_separated_projection_dichotomy
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_ad_projection_dichotomy`

Sticky Theorem 5.2 (Section 8 form), split along sticky Section 8:

* `wz_kaufman_projection_count`: Kaufman's projection theorem (Thm 8.2);
* `wz_osw_thin_tubes_bootstrap`: the Orponen-Shmerkin-Wang bootstrapping lemma (Prop 8.6');
* `wz_nonconcentrated_dot_products`: Kaufman and OSW imply Prop 8.5;
* `wz_separated_projection_dichotomy`: Kaufman and Prop 8.5 imply Prop 8.9;
* `wz_ad_dichotomy_from_separated`: Prop 8.9 implies the theorem below.

The implication children take their premises verbatim, so the proof is a composition.
-/

theorem WangZahlLot.wz_ad_projection_dichotomy : ∀ε:ℝ,0<ε→∃η δ₀:ℝ,0<η∧0<δ₀∧∀δ:ℝ,0<δ→δ≤δ₀→∀F G:Set (EuclideanSpace ℝ (Fin 2)),(∀a ∈ F,∀i:Fin 2,0≤a i∧a i≤1)→(∀b ∈ G,∀i:Fin 2,0≤b i∧b i≤1)→(∀(x:(EuclideanSpace ℝ (Fin 2))) (ρ r:ℝ),δ≤ρ→ρ≤r→∃(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),F∩Metric.ball x r⊆(⋃ j,Metric.closedBall (cc j) ρ)∧(m:ℝ)≤δ^(-η)*(r/ρ))→(∀(x:(EuclideanSpace ℝ (Fin 2))) (ρ r:ℝ),δ≤ρ→ρ≤r→∃(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),G∩Metric.ball x r⊆(⋃ j,Metric.closedBall (cc j) ρ)∧(m:ℝ)≤δ^(-η)*(r/ρ))→((∃(e b₀:(EuclideanSpace ℝ (Fin 2))) (c:ℝ),‖e‖=1∧(∀(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),Metric.thickening δ {a|inner ℝ a e=c}∩F⊆(⋃ j,Metric.closedBall (cc j) δ)→δ^(ε-1)≤(m:ℝ))∧(∀(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2))),Metric.thickening δ (Set.range (fun t:ℝ=>b₀+t • e))∩G⊆(⋃ j,Metric.closedBall (cc j) δ)→δ^(ε-1)≤(m:ℝ)))∨(∀Q:Set (EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)),Q⊆F ×ˢ (G ×ˢ G)→(∀(m:ℕ) (cc:Fin m→(EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2))),Q⊆(⋃ j,Metric.closedBall (cc j) δ)→δ^(η-3)≤(m:ℝ))→∃ρ a L:ℝ,δ≤ρ∧δ^(-η)*ρ≤L∧∀(m:ℕ) (cc:Fin m→ℝ),Set.Icc a (a+L)∩{t:ℝ|∃h ∈ Q,t=inner ℝ h.1 (h.2.1-h.2.2)}⊆(⋃ j,Metric.closedBall (cc j) ρ)→(L/ρ)^(1-ε)≤(m:ℝ))) :=
  WangZahlLot.wz_ad_dichotomy_from_separated
    (WangZahlLot.wz_separated_projection_dichotomy WangZahlLot.wz_kaufman_projection_count
      (WangZahlLot.wz_nonconcentrated_dot_products WangZahlLot.wz_kaufman_projection_count
        WangZahlLot.wz_osw_thin_tubes_bootstrap))
