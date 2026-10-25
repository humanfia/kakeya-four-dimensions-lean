/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldDiscoveryAssembly.lean.
   Helper namespace and imports renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldPreparation
import Submission.Obl.k4_scalar_graph_residual_discovery.PacketScale

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open MeasureTheory

/-- The exact remaining geometric assertion: construct actual original
coefficient worlds arbitrarily late along any dense failed subsequence.
The floor exponent and graph precision precede all accuracy budgets. -/
def OriginalWorldPreparationStatement : Prop :=
  (∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∃ C : ℝ, 0 < C ∧
    Submission.Lib.K4ContinuousKakeya.FiniteMK n C) →
  ∀ D : ScalarData, D.Parameters → D.base → D.caps → D.packets →
    ∀ (H : ℕ → ℝ) (θ : (k : ℕ) → Fin (D.W k) → Measure ScalarLine)
      (E₀ : (k : ℕ) → Fin (D.W k) → Set ScalarIncidence),
      D.prepData H θ E₀ → D.OriginalWorldPreparation H E₀

/-- The geometric world producer and higher jets suffice for the exact
analytic discovery statement used in the frozen qualification theorem. -/
theorem polynomialDiscovery_of_original_preparation
    (hjets : Jets.HigherJetsStatement) (hworld : OriginalWorldPreparationStatement) :
    PolynomialDiscoveryStatement := by
  intro hMK D hpar hbase hcaps hpack H θ E₀ hprep
  have hN : ∀ k, 1 ≤ D.N k := fun k => by linarith [hpar.1 k]
  have hscale := hpack.original_block_scale hpar.1 hpar.2.2.1.1
  exact ScalarData.polynomialDiscovery_of_original_world_preparation hjets D H hN hpar.2.1
    hprep.1 hpar.2.2.1 hpar.2.2.2.1 hpar.2.2.2.2.1 hpar.2.2.2.2.2.1
    (hscale.mono (fun _ h => h.2)) E₀ (hworld hMK D hpar hbase hcaps hpack H θ E₀ hprep)

end Submission.Obl.k4_scalar_graph_residual_discovery
