/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit f3582cb1, file OriginalWorldPreparationFromBudgets.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalSampleWorld
import Submission.Obl.k4_scalar_graph_residual_discovery.DiscoveryBudgetStatement
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldDiscoveryAssembly

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

/-- Pure numerical budget existence gives the entire original-world
preparation statement, with graph precision fixed before accuracies. -/
theorem original_world_preparation_of_budgets
    (hbudget : DiscoveryBudgetExistenceStatement) : OriginalWorldPreparationStatement := by
  intro hMK D hpar hbase hcaps hpack H θ E₀ hprep
  rcases hpar with ⟨hN, hNt, hK, hd, hd₁, hκ, _, hS⟩
  obtain ⟨Cmk, hCmk, hMK₂⟩ := hMK 2 (by norm_num) (by norm_num)
  have hmesh := (Classical.choose_spec hprep.2).1
  have hscale := hpack.original_block_scale hN hK.1
  intro M hM cζ hcζ L hL
  obtain ⟨C, C₁, _, hC₁, L', hLL', hL', hC₁L, hbudgets⟩ :=
    hbudget D.N D.K H (D.prepMesh hprep) (fun k => ((2 : ℝ) ^ D.T k 1)⁻¹)
      hN hNt hK hprep.1 hmesh D.d D.κ D.S hd hd₁.le hκ hS
      (fun _ => by positivity) hscale M hM cζ hcζ L hL Cmk hCmk
  refine ⟨L', hLL', hL', ?_⟩
  intro Hg B G E hgraph ε _ α hα δ hδ φ hφ hdense
  obtain ⟨J₁, J₂, hJ₁, hJ₂, T, hT, hbud⟩ :=
    hbudgets Hg hgraph.1 B hgraph.2.1 α hα δ hδ
  have hsample := ScalarData.original_world_of_discovery_budget hprep hgraph hbase hcaps hpack hN
    hd hd₁.le Cmk hCmk.le hMK₂ M C₁ C J₁ J₂ hC₁ hJ₁ hJ₂ hC₁L ε δ α cζ hδ T hT
  have hlate : ∀ᶠ j in atTop, ∃ w : OriginalJetWorld D H B G E M ε (φ j),
      w.K ≤ D.N (φ j) ^ α ∧
        D.N (φ j) ^ (-D.κ) / w.K ≤ ((2 : ℝ) ^ D.T (φ j) 1)⁻¹ ∧
        ((2 : ℝ) ^ D.T (φ j) 1)⁻¹ ≤ w.K * D.N (φ j) ^ (-D.κ) ∧
        w.ζ ≤ (((2 : ℝ) ^ D.T (φ j) 1)⁻¹) ^ cζ := by
    filter_upwards [hφ.eventually hbud, hφ.eventually hsample, hφ.eventually hscale] with j hb hw hs
    obtain ⟨budget⟩ := hb
    obtain ⟨w, hwK, hwζ⟩ := hw budget (hdense j)
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · simpa only [hwK] using budget.constant_budget
    · rw [hwK]
      exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith [hN (φ j)]) _)
        (by linarith [hK.1 (φ j)] : 0 < D.K (φ j)) budget.original_budget).trans hs.1
    · rw [hwK]
      exact hs.2.trans (mul_le_mul_of_nonneg_right budget.original_budget
        (Real.rpow_nonneg (by linarith [hN (φ j)]) _))
    · simpa only [hwζ] using budget.floor_margin
  exact hlate.frequently

theorem polynomialDiscovery_of_discovery_budgets
    (hjets : Jets.HigherJetsStatement) (hbudget : DiscoveryBudgetExistenceStatement) :
    PolynomialDiscoveryStatement :=
  polynomialDiscovery_of_original_preparation hjets (original_world_preparation_of_budgets hbudget)

end Submission.Obl.k4_scalar_graph_residual_discovery
