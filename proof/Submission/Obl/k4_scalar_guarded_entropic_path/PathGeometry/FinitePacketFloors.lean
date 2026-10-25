import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.WorldPacketFloors
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootGeometryFloors

/-! Restore all chart and whole-world floors in one finite menu. The
menu may contain different original parents, on the same final law. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open PathMeasures

noncomputable section

namespace PacketFamily

def CurrentFloors {z : Code} (family : PacketFamily z) (k : ℕ) (H : ℝ)
    (η : Measure (Fin (W z k) × State)) (E : Set (Fin (W z k) × State)) : Prop :=
  ∀ i : family.Index k, 0 < ω family.parent (family.view.sample k) (family.world k i) →
    E ∩ family.cell k i = ∅ ∨
      (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (family.duration k) *
        ν family.parent (family.view.sample k) (family.world k i) (family.assignment k i) ≤
          family.view.submeasureWorldLaw k (η.restrict E) (family.world k i) (family.priorCell k i)

end PacketFamily

/-- The existing finite-index simultaneous pruning is unchanged when
its rows are indexed by an arbitrary finite menu. -/
theorem simultaneous_finite_packet_floors {α : Type*} [Fintype α] {z : Code}
    (hz : Exact z) (families : α → PacketFamily z) (k : ℕ) (R H : ℝ)
    (hR : ∀ a, (families a).view.referenceFactor k ≤ R)
    (η : Measure (Fin (W z k) × State)) (hη : η ≤ normalizedWorldMixture z k)
    (A : Set (Fin (W z k) × State)) (hA : MeasurableSet A) :
    ∃ E : Set (Fin (W z k) × State), MeasurableSet E ∧ E ⊆ A ∧
      η A ≤ η E + (Fintype.card α : ℝ≥0∞) * (ENNReal.ofReal R / ENNReal.ofReal H) ∧
      ∀ a, (families a).CurrentFloors k H η E := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let menu : Fin (Fintype.card α) → PacketFamily z := fun i => families (e.symm i)
  obtain ⟨E, hE, hEA, hmass, hfloors⟩ := simultaneous_budgeted_packet_floors hz menu R H
    (fun i => hR (e.symm i)) η hη A hA
  refine ⟨E, hE, hEA, hmass, ?_⟩
  intro a
  have hf : (menu (e a)).CurrentFloors k H η E := hfloors (e a)
  simpa only [menu, e.symm_apply_apply] using hf

/-- A prepared common half-probability core and one simultaneous loss
of at most one quarter leave all final floors on one quarter core. -/
theorem exists_quarter_packet_core {α : Type*} [Fintype α] {z : Code}
    (hz : Exact z) (families : α → PacketFamily z) (k : ℕ) (R H : ℝ)
    (hR : ∀ a, (families a).view.referenceFactor k ≤ R)
    (A : Set (Fin (W z k) × State)) (hA : MeasurableSet A)
    (hhalf : ENNReal.ofReal (1 / 2 : ℝ) ≤ normalizedWorldMixture z k A)
    (hloss : (Fintype.card α : ℝ≥0∞) * (ENNReal.ofReal R / ENNReal.ofReal H) ≤
      ENNReal.ofReal (1 / 4 : ℝ)) :
    ∃ E : Set (Fin (W z k) × State), MeasurableSet E ∧ E ⊆ A ∧
      ENNReal.ofReal (1 / 4 : ℝ) ≤ normalizedWorldMixture z k E ∧
      ∀ a, (families a).CurrentFloors k H (normalizedWorldMixture z k) E := by
  obtain ⟨E, hE, hEA, hmass, hfloors⟩ := simultaneous_finite_packet_floors hz families k R H
    hR (normalizedWorldMixture z k) le_rfl A hA
  refine ⟨E, hE, hEA, ?_, hfloors⟩
  apply ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (1 / 4 : ℝ)) ENNReal.ofReal_ne_top
  calc
    ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    _ ≤ _ := hhalf.trans (hmass.trans (add_le_add le_rfl hloss))

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning
