import Submission.Obl.k4_scalar_guarded_entropic_path.ViewLayers
import Submission.Obl.k4_scalar_guarded_entropic_path.StageAssembly
import Submission.Obl.k4_scalar_guarded_entropic_path.Info.Canonical

/-! Canonical raw stages are made directly from actual original parent
views and the one common retained final law. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView

open MeasureTheory Set PathMeasures
open Submission.Obl.k4_scalar_linear_critical_extremizers

noncomputable section

variable {root final : Code} {D S₀ η : ℝ}

def toRawStage (a : OriginalView root final D S₀ η) (k : ℕ)
    (scale H buffer B : ℝ) (M : ℕ) (ε : ℝ)
    (E : Set (Fin (Split.W final k) × State)) (node : ℝ → Fin a.count)
    (layers : Fin a.count → Layer (Split.W a.parent (a.suffixChain.sample k)))
    (m : ℕ) (Mb : ℤ) (α : ℝ) : RawStage where
  p := a.parent
  sample := a.suffixChain.sample k
  scale := scale
  H := H
  buffer := buffer
  B := B
  M := M
  count := a.count
  node := node
  depth j := a.depth j / scale
  time j := (a.time j + ε) / scale
  layers := layers
  σ := a.suffixChain.selectedWorldLaw k E
  m := m
  n _ := Info.canonN m Mb
  X _ := Info.canonX (Split.N a.parent (a.suffixChain.sample k) ^ scale) m Mb
  Y _ := Info.canonY m Mb
  Z _ := Info.canonZ m Mb
  q _ j := Info.canonQ m j
  c _ j := Info.canonC m j
  α := α
  π₀ g := Info.velocityPalette (a.suffixChain.selectedWorldLaw k E g)

theorem toRawStage_layer_good (a : OriginalView root final D S₀ η) (k : ℕ)
    {scale H buffer B ε v d κ α : ℝ} {M m : ℕ} {Mb : ℤ}
    (E : Set (Fin (Split.W final k) × State)) (node : ℝ → Fin a.count)
    (layers : Fin a.count → Layer (Split.W a.parent (a.suffixChain.sample k)))
    (hscale : 0 < scale)
    (htolerance : Real.log H / Real.log (Split.N a.parent (a.suffixChain.sample k)) = v)
    (hgood : ∀ j, a.OriginalLayerGood k M ε v H B d κ
      (a.suffixChain.selectedWorldLaw k E) j (layers j)) :
    ∀ j, (a.toRawStage k scale H buffer B M ε E node layers m Mb α).LayerGood d κ j := by
  have hNtwo : 2 ≤ Code.N a.parent (a.suffixChain.sample k) :=
    a.parent_exact.1.1 (a.suffixChain.sample k)
  have hN : 0 < Code.N a.parent (a.suffixChain.sample k) := by linarith
  have htolerance' : Real.log H / Real.log (Code.N a.parent (a.suffixChain.sample k)) = v :=
    htolerance
  have hcancel (x : ℝ) : scale * (x / scale) = x := by field_simp
  have hpower (x : ℝ) : (Code.N a.parent (a.suffixChain.sample k) ^ scale) ^
      (κ * (x / scale)) = Code.N a.parent (a.suffixChain.sample k) ^ (κ * x) := by
    rw [← Real.rpow_mul hN.le]
    congr 1
    field_simp
  intro j
  change Fin a.count at j
  dsimp only [RawStage.LayerGood, toRawStage, RawStage.N₀, RawStage.N]
  rw [hcancel (a.depth j), hcancel (a.time j + ε), htolerance', hpower (a.depth j)]
  exact ⟨div_nonneg (a.depth_bounds j).1 hscale.le, (a.depth_bounds j).2, hgood j⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalView
