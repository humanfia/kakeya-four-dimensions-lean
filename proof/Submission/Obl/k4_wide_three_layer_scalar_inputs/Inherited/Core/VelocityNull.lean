/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit 525ce8d3c8ed1d02854b5f6c797e220d2ac13ddd, file Submission/Obl/k4_horizontal_wide_interval_return/Core/LayerCompare.lean.
Only the palette-nullness lemma retained; namespace/imports renamed. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core.Basics
namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core
open MeasureTheory Set Submission.Lib.K4MovingMeshBoxes
variable {α : Type} [MeasurableSpace α]
theorem velocityBin_null {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    {N K d r s' v' : ℝ} (hcap : JointCapAt μ π b N K d r s' v') (v₀ : ℤ)
    (hπ : π {w | ⌊w / N ^ (-v')⌋ = v₀} = 0) :
    μ {p | ⌊b p.1 3 / N ^ (-v')⌋ = v₀} = 0 := by
  have hsub : {p : α × ℝ | ⌊b p.1 3 / N ^ (-v')⌋ = v₀} ⊆
      ⋃ q : Fin 3 → ℤ, ⋃ a : ℤ, {p | baseMesh (N ^ (-r)) (basePt b p) = q ∧
        ⌊hidden b p / N ^ (-s')⌋ = a ∧ ⌊b p.1 3 / N ^ (-v')⌋ = v₀} := by
    intro p hp
    exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨_, rfl, rfl, hp⟩⟩
  refine measure_mono_null hsub (measure_iUnion_null fun q => measure_iUnion_null fun a => ?_)
  refine le_antisymm ((hcap q a v₀).trans (le_of_eq ?_)) bot_le
  rw [hπ, mul_zero]

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core
