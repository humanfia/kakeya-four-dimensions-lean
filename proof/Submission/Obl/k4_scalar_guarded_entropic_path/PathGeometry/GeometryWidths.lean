import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PreparedViews
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GeometryCharts

/-! Width preparation controls any fixed actual selected row. Keeping
the deterministic row matters when its normalization reads velocity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

namespace ChartGeometry

def Geometry.narrow {p : Code} {k : ℕ} (g : Geometry p k) (ε u : ℝ)
    (a : Fin (W p k)) : Set State :=
  {z | ∃ i, g.world i = a ∧ z ∈ g.selected i ∧
    2 * N p k ^ ε * g.width i * (2 : ℝ) ^ g.generation ≤ N p k ^ (-u)}

theorem width_of_not_narrow {p : Code} {k : ℕ} (g : Geometry p k)
    {ε u H : ℝ} (hN : 0 < N p k) (hH : 2 * N p k ^ (ε + u) ≤ H)
    (a : Fin (W p k)) (z : State) (d : Fin g.count) (hworld : g.world d = a)
    (hsel : z ∈ g.selected d) (hwidth : 0 ≤ g.width d) (hnarrow : z ∉ g.narrow ε u a) :
    (H * (2 : ℝ) ^ g.generation)⁻¹ ≤ g.width d := by
  apply Submission.Obl.k4_scalar_guarded_entropic_path.width_of_not_narrow hN hwidth hH
  exact lt_of_not_ge (fun hn => hnarrow ⟨d, hworld, hsel, hn⟩)

end ChartGeometry

namespace PreparedViews

variable {α : Type*} [Fintype α] {root final : Code} {D S₀ η : ℝ}

/-- On the literal prepared set, every selected actual row is wide.
No assertion about points outside the original path support is needed. -/
theorem fixed_row_width (views : α → OriginalView root final D S₀ η)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent) (k : ℕ)
    (a : α) (j : Fin (views a).count) (P : (views a).ChartAt (ε a) k j)
    (hchoice : (views a).chartChoice (ε a) j k = some P)
    (hgeometry : ChartGeometry.ofChart P = (views a).geometry k j)
    (z : Fin (W final k) × State) (hz : z ∈ core views ε u tests k)
    (d : Fin ((views a).geometry k j).count)
    (hworld : ((views a).geometry k j).world d = ((views a).suffixChain.pullback k z).1)
    (hselected : ((views a).suffixChain.pullback k z).2 ∈ ((views a).geometry k j).selected d)
    (hwidth : 0 ≤ ((views a).geometry k j).width d)
    (H : ℝ) (hH : 2 * N (views a).parent ((views a).suffixChain.sample k) ^
      (ε a + u a) ≤ H) :
    (H * (2 : ℝ) ^ ((views a).geometry k j).generation)⁻¹ ≤
      ((views a).geometry k j).width d := by
  have hevents : taggedEvent
      (WidthGeometry.narrowEvent ((views a).layerAt (ε a) j k) (ε a) (u a)) =
      taggedEvent (((views a).geometry k j).narrow (ε a) (u a)) := by
    rw [(views a).layerAt_of_choice (ε a) j k P hchoice, ← hgeometry]
    rfl
  have hnot : (views a).suffixChain.pullback k z ∉ taggedEvent
      (WidthGeometry.narrowEvent ((views a).layerAt (ε a) j k) (ε a) (u a)) := by
    intro hb
    exact hz (Set.mem_iUnion.mpr ⟨.inl ⟨a, j⟩, hb⟩)
  rw [hevents] at hnot
  exact ChartGeometry.width_of_not_narrow _
    (by linarith [(views a).parent_exact.1.1 ((views a).suffixChain.sample k)]) hH _ _ _
    hworld hselected hwidth hnot

/-- Every deterministic selected-row readout on the common law keeps
its full-block width. This applies in particular to rootRow. -/
theorem fixed_row_width_ae (views : α → OriginalView root final D S₀ η)
    (ε u : α → ℝ) (tests : (a : α) → DensityTests (views a).parent) (k : ℕ)
    (ρ : Measure (Fin (W final k) × State))
    (hρ : ρ ≤ (normalizedWorldMixture final k).restrict (core views ε u tests k))
    (a : α) (j : Fin (views a).count) (P : (views a).ChartAt (ε a) k j)
    (hchoice : (views a).chartChoice (ε a) j k = some P)
    (hgeometry : ChartGeometry.ofChart P = (views a).geometry k j)
    (row : Fin (W final k) × State → Fin ((views a).geometry k j).count)
    (hworld : ∀ᵐ z ∂ρ, ((views a).geometry k j).world (row z) =
      ((views a).suffixChain.pullback k z).1)
    (hselected : ∀ᵐ z ∂ρ, ((views a).suffixChain.pullback k z).2 ∈
      ((views a).geometry k j).selected (row z))
    (hwidth : ∀ d, 0 ≤ ((views a).geometry k j).width d)
    (H : ℝ) (hH : 2 * N (views a).parent ((views a).suffixChain.sample k) ^
      (ε a + u a) ≤ H) :
    ∀ᵐ z ∂ρ, (H * (2 : ℝ) ^ ((views a).geometry k j).generation)⁻¹ ≤
      ((views a).geometry k j).width (row z) := by
  have hevents : taggedEvent
      (WidthGeometry.narrowEvent ((views a).layerAt (ε a) j k) (ε a) (u a)) =
      taggedEvent (((views a).geometry k j).narrow (ε a) (u a)) := by
    rw [(views a).layerAt_of_choice (ε a) j k P hchoice, ← hgeometry]
    rfl
  have hn := preimage_null views ε u tests k ρ hρ (.inl ⟨a, j⟩)
  change ρ ((views a).suffixChain.pullback k ⁻¹'
    taggedEvent (WidthGeometry.narrowEvent ((views a).layerAt (ε a) j k) (ε a) (u a))) = 0 at hn
  rw [hevents] at hn
  have hnot : ∀ᵐ z ∂ρ, ((views a).suffixChain.pullback k z).2 ∉
      ((views a).geometry k j).narrow (ε a) (u a)
        ((views a).suffixChain.pullback k z).1 := by
    apply ae_iff.mpr
    simpa only [not_not, taggedEvent, Set.preimage, Set.mem_ofPred_eq] using hn
  filter_upwards [hworld, hselected, hnot] with z hw hs hn
  exact ChartGeometry.width_of_not_narrow _
    (by linarith [(views a).parent_exact.1.1 ((views a).suffixChain.sample k)]) hH _ _ _ hw hs
    (hwidth _) hn

end PreparedViews

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
