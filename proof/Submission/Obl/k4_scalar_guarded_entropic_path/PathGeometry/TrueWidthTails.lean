/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrueWidthTails.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.NarrowMasks
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.LiteralCoarsening

/-! Narrow-width deletion for the actual ambient true atlas of a tracked
normalization. Its literal coarsened outer problem supplies angular laws. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueNormalization

open MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting

noncomputable section

variable {p q : Code} {r h : ℝ}

/-- The SAME retained full true atlas is terminal in the literal outer
problem. Only the auxiliary angular density differs from the parent. -/
def terminalAmbientChart (a : TrueNormalization p q r r h) (cap : ℝ) (k : ℕ) :
    ChartW (PathNodes.literalCoarsen p r cap) a.ambientExponent r r
      (h + a.ambientLoss k) (a.ambientLoss k) true (a.witness.sample k) :=
  ⟨a.witness.T k, W q k, a.witness.world k, a.witness.block k,
    a.witness.assignment k, a.ambientSelected k, a.witness.center k, a.witness.speed k,
    a.witness.width k, a.witness.polynomial k, a.ambientLists k, a.ambient_charts k⟩

/-- A local true critical layer has power-small ORIGINAL narrow-packet
masks for every positive angular reading in its literal outer problem. -/
theorem narrow_masks_powerSmall (a : TrueNormalization p q r r h) {cap u : ℝ}
    (houter : Exact (PathNodes.literalCoarsen p r cap))
    (hu : 0 < u) (huU : u ≤ U (PathNodes.literalCoarsen p r cap)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ g, ENNReal.ofReal (ω p (a.witness.sample k) g) *
        mu p (a.witness.sample k) g
          (NarrowWidths.narrowUnion (a.terminalAmbientChart cap k) (N q k ^ (-u)) g)) ≤
            ENNReal.ofReal (N q k ^ (-c)) := by
  have hε0 (k : ℕ) : 0 ≤ a.ambientLoss k :=
    (a.witness.loss_pos k).le.trans (le_max_right _ _)
  obtain ⟨c, hc, hbound⟩ := NarrowWidths.narrowUnion_powerSmall houter a.witness.sample
    a.witness.sample_strictMono a.ambientExponent h a.ambientLoss a.ambientLoss_tendsto
    hε0 (a.terminalAmbientChart cap) hu huU
  refine ⟨c, hc, hbound.mono ?_⟩
  intro k hk
  rw [(a.witness.charts k).1]
  exact hk

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueNormalization
