import Submission.Obl.k4_wide_three_layer_scalar_inputs.Layers
import Submission.Obl.k4_wide_three_layer_scalar_inputs.InheritedBridge
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.Datum

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open MeasureTheory

noncomputable section

/-- The comparison kernels consume exactly these same labels, graphs,
original laws and reference weights. -/
abbrev ComparedLayers.comparisonDatum {α : Type} [MeasurableSpace α] {cfg : Data α}
    {k : ℕ} {ε R χ D s u : ℝ} {depth : Fin 3 → ℝ}
    (L : ComparedLayers cfg k ε R χ D depth s u) :
    Inherited.Core.LayerDatum cfg.comparisonData k ε R χ D depth where
  ρs := L.ρs
  np := L.np
  C := L.C
  qp := L.qp
  G := L.G
  le_rho := L.le_rho
  mass := L.mass
  cover := L.cover
  meas := L.meas
  disj := L.disj
  piece := L.piece
  sum := L.sum

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
