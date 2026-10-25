import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FinitePacketFloors
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PreparedViews

/-! One common mask restores both the unchanged original chart-packet
floors and the whole-world floors, for every candidate simultaneously. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)

noncomputable section

def ChartFloors {p z : Code} (view : RefinementChain p z) (k : ℕ)
    {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag (view.sample k)) (H : ℝ)
    (E : Set (Fin (W z k) × State)) : Prop :=
  ∀ d : Fin Q.n, 0 < ω p (view.sample k) (Q.γ d) →
    E ∩ (view.pullback k ⁻¹' ({Q.γ d} ×ˢ (Q.A d ×ˢ I Q.T (Q.j d)))) = ∅ ∨
      (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ Q.T)⁻¹) *
        ν p (view.sample k) (Q.γ d) (Q.A d) ≤
          view.selectedWorldLaw k E (Q.γ d) (Q.A d ×ˢ I Q.T (Q.j d))

theorem chartFloors_geometry {p z : Code} (view : RefinementChain p z) (k : ℕ)
    {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag (view.sample k))
    (g : ChartGeometry.Geometry p (view.sample k)) (hg : ChartGeometry.ofChart Q = g)
    (H : ℝ) (E : Set (Fin (W z k) × State)) (hf : ChartFloors view k Q H E) :
    RootPacketFamilies.GeometryFloors view k g H E := by
  subst g
  exact hf

theorem chartFloors_of_atSample {p z : Code} (hp : Exact p)
    (view : RefinementChain p z) (k : ℕ) {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag (view.sample k)) (H : ℝ)
    (E : Set (Fin (W z k) × State))
    (hf : (PacketFamily.atSample hp view k Q).CurrentFloors k H
      (normalizedWorldMixture z k) E) : ChartFloors view k Q H E := by
  let F : PacketSample p (view.sample k) → Prop := fun data =>
    ∀ d : Fin data.count, 0 < ω p (view.sample k) (data.world d) →
      E ∩ (view.pullback k ⁻¹'
        ({data.world d} ×ˢ (data.assignment d ×ˢ data.timeBlock d))) = ∅ ∨
        (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal data.duration *
          ν p (view.sample k) (data.world d) (data.assignment d) ≤
            view.selectedWorldLaw k E (data.world d) (data.assignment d ×ˢ data.timeBlock d)
  have hf' : F (Function.update (fun j => PacketSample.empty p (view.sample j))
      k (PacketSample.ofChart hp Q) k) := hf
  rw [Function.update_self] at hf'
  exact hf'

variable {α : Type*} [Fintype α] {root final : Code} {D S₀ η : ℝ}

abbrev CommonFloorIndex (views : α → OriginalView root final D S₀ η) :=
  ((a : α) × Fin (views a).count) ⊕ α

def commonFloorMenu (views : α → OriginalView root final D S₀ η)
    (ε : α → ℝ) (k : ℕ)
    (Q : (a : α) → (j : Fin (views a).count) → (views a).ChartAt (ε a) k j) :
    CommonFloorIndex views → PacketFamily final
  | .inl j => PacketFamily.atSample (views j.1).parent_exact (views j.1).suffixChain k (Q j.1 j.2)
  | .inr a => PacketFamily.worlds (views a).parent_exact (views a).suffixChain

/-- Every original chart and every original world is pruned together.
All floors refer to the same residual of the same final probability. -/
theorem exists_common_quarter_core (views : α → OriginalView root final D S₀ η)
    (hz : Exact final) (ε : α → ℝ) (k : ℕ)
    (Q : (a : α) → (j : Fin (views a).count) → (views a).ChartAt (ε a) k j)
    (R H : ℝ) (hH : 0 < H)
    (hR : ∀ a, (views a).suffixChain.referenceFactor k ≤ R)
    (A : Set (Fin (W final k) × State)) (hA : MeasurableSet A)
    (hhalf : ENNReal.ofReal (1 / 2 : ℝ) ≤ normalizedWorldMixture final k A)
    (hloss : (Fintype.card (CommonFloorIndex views) : ℝ≥0∞) *
      (ENNReal.ofReal R / ENNReal.ofReal H) ≤ ENNReal.ofReal (1 / 4 : ℝ)) :
    ∃ E : Set (Fin (W final k) × State), MeasurableSet E ∧ E ⊆ A ∧
      ENNReal.ofReal (1 / 4 : ℝ) ≤ normalizedWorldMixture final k E ∧
      (∀ a j, ChartFloors (views a).suffixChain k (Q a j) H E) ∧
      ∀ a g, (views a).suffixChain.selectedWorldLaw k E g = 0 ∨
        ENNReal.ofReal H⁻¹ ≤ (views a).suffixChain.selectedWorldLaw k E g univ := by
  classical
  let families := commonFloorMenu views ε k Q
  have hRf : ∀ a, (families a).view.referenceFactor k ≤ R := by
    intro a
    cases a with
    | inl j => exact hR j.1
    | inr a => exact hR a
  obtain ⟨E, hE, hEA, hmass, hfloors⟩ := exists_quarter_packet_core hz families k R H hRf
    A hA hhalf hloss
  refine ⟨E, hE, hEA, hmass, ?_, ?_⟩
  · intro a j
    exact chartFloors_of_atSample (views a).parent_exact (views a).suffixChain k
      (Q a j) H E (hfloors (.inl ⟨a, j⟩))
  · intro a g
    exact current_world_floor_cases (views a).parent_exact hz (views a).suffixChain k H hH
      (normalizedWorldMixture final k) le_rfl E (hfloors (.inr a)) g

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning
