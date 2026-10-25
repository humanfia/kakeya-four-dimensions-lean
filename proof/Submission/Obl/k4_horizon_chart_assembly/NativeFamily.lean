import Submission.Obl.k4_horizon_chart_assembly.FiniteFamily
import Submission.Obl.k4_horizon_chart_assembly.GlobalBudget
import Submission.Obl.k4_horizon_chart_assembly.GroupAtlas

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory
open scoped ENNReal BigOperators
open Submission.Lib.K4FinitePlankAtlases (PhysicalPlank)

noncomputable section

def nativePacketSet {W T D m : ℕ} {S : Finset ((Fin 2 → ℤ) × ℤ)}
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) (K H q a : ℝ)
    (g : NativeGroupIndex W T S) (ps : Fin m → PhysicalPlank D) (i : Fin m) : Set Trajectory :=
  packetAssignment (nativeGroup (P g.1) (B g.1) K H ((g.2.1 : ℝ) * q) q a g.2.2.val)
    (groupIntercept q a ((g.2.1 : ℝ) * q) ((2 * K + 2) * q) g.2.2.val)
    (groupVelocity q ((2 * K + 2) * q)) ps i

def nativePacketEvent {W T D m : ℕ} {S : Finset ((Fin 2 → ℤ) × ℤ)}
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) (E : Fin W → Set Incidence)
    (K H q a : ℝ) (g : NativeGroupIndex W T S) (ps : Fin m → PhysicalPlank D) (i : Fin m) :
    Set Incidence :=
  selectedEvent (E g.1) (nativePacketSet P B K H q a g ps i) (P g.1) (B g.1 / K)
    ((g.2.1 : ℝ) * q) q

/-- Exact native packet arrays assemble into a finite atlas with the universal
`V^16` budget. The selected-mass sum is preserved as a lower bound. -/
theorem native_packet_family {W T D₀ Dmesh : ℕ} (S : Finset ((Fin 2 → ℤ) × ℤ))
    (H K τ₀ κ a n₀ : ℝ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) [∀ γ, IsProbabilityMeasure (ν γ)]
    (E : Fin W → Set Incidence) (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (hH : 2 ≤ H) (hK : 1 ≤ K) (hτ : 0 < τ₀) (ha : 0 < a)
    (hW : (W : ℝ) ≤ H) (hP : ∀ γ, (P γ).totalDegree ≤ 2)
    (m : NativeGroupIndex W T S → ℕ)
    (ps : (g : NativeGroupIndex W T S) → Fin (m g) → PhysicalPlank Dmesh)
    (c w : (g : NativeGroupIndex W T S) → Fin (m g) → Plane)
    (Q : (g : NativeGroupIndex W T S) → Fin (m g) → Matrix (Fin 2) (Fin 2) ℝ)
    (hcount : ∀ g : NativeGroupIndex W T S,
      (m g : ℝ) ≤ (Dmesh : ℝ) ^ 2 / (4 * τ₀) * (ν g.1).real
        (nativeGroup (P g.1) (B g.1) K H ((g.2.1 : ℝ) * ((2 : ℝ) ^ T)⁻¹)
          (((2 : ℝ) ^ T)⁻¹) a g.2.2.val))
    (hchart : ∀ (g : NativeGroupIndex W T S) (i : Fin (m g)),
      let q : ℝ := ((2 : ℝ) ^ T)⁻¹
      let t₀ : ℝ := (g.2.1 : ℝ) * q
      let Γ := g.2.2.val
      RawChart (packetEnvelope H K (2 * K + 2) q τ₀ Dmesh) (max D₀ 4) κ T (g.2.1 : ℝ) a
        (B g.1) (E g.1)
        (liftedBlockCenter (midpointGroupCenter q Γ) (c g i) (w g i) t₀ q ((2 * K + 2) * q))
        (liftedBlockSpeed (w g i) q ((2 * K + 2) * q)) (((2 * K + 2) * q) • Q g i)
        (shiftedTest (P g.1) (a * (Γ.2 : ℝ)))
        (nativePacketSet P B K H q a g (ps g) i) (nativePacketEvent P B E K H q a g (ps g) i)
        (ENNReal.ofReal (n₀ * |(((2 * K + 2) * q) • Q g i).det| / ((2 : ℝ) ^ T * κ)) ≤
          ((ν g.1).prod volume) (nativePacketEvent P B E K H q a g (ps g) i))) :
    BudgetAtlas W T (max D₀ 4) (atlasSize H K τ₀ Dmesh T ^ 16) κ a n₀
      (∑ g, ∑ i, ENNReal.ofReal (ω g.1) * ((ν g.1).prod volume)
        (nativePacketEvent P B E K H (((2 : ℝ) ^ T)⁻¹) a g (ps g) i)) ω ν E B := by
  classical
  let q : ℝ := ((2 : ℝ) ^ T)⁻¹
  let mid : Fin (2 ^ T) → ℝ := fun j => (j : ℝ) * q
  let U := nativeGroupAt (S := S) P B K H q a mid
  let A := fun (g : NativeGroupIndex W T S) (i : Fin (m g)) => nativePacketSet P B K H q a g (ps g) i
  let F := fun (g : NativeGroupIndex W T S) (i : Fin (m g)) => nativePacketEvent P B E K H q a g (ps g) i
  let cp := fun (g : NativeGroupIndex W T S) (i : Fin (m g)) => liftedBlockCenter (midpointGroupCenter q g.2.2.val)
    (c g i) (w g i) (mid g.2.1) q ((2 * K + 2) * q)
  let up := fun (g : NativeGroupIndex W T S) (i : Fin (m g)) => liftedBlockSpeed (w g i) q ((2 * K + 2) * q)
  let Qp := fun (g : NativeGroupIndex W T S) (i : Fin (m g)) => ((2 * K + 2) * q) • Q g i
  let Rp := fun (g : NativeGroupIndex W T S) (_i : Fin (m g)) => shiftedTest (P g.1) (a * (g.2.2.val.2 : ℝ))
  have hq : 0 < q := by dsimp [q]; positivity
  have hU : ∀ g, MeasurableSet (U g) := by
    intro g
    exact nativeGroup_measurable (P g.1) (hP g.1) (B g.1) (mid g.2.1)
      (by linarith) (by linarith) hq ha g.2.2.val
  have hsub : ∀ g i, A g i ⊆ U g := fun _ _ => inter_subset_left
  have hinside : ∀ g, Pairwise (fun i i' => Disjoint (A g i) (A g i')) := by
    intro g
    exact packetAssignment_disjoint (U g)
      (groupIntercept q a (mid g.2.1) ((2 * K + 2) * q) g.2.2.val)
      (groupVelocity q ((2 * K + 2) * q)) (ps g)
  have hb := global_atlas_budget (D := Dmesh) (T := T) hH hK hτ hW
  exact aggregate_budget_charts (Ccount := (Dmesh : ℝ) ^ 2 / (4 * τ₀)) W T (max D₀ 4)
    (packetEnvelope H K (2 * K + 2) q τ₀ Dmesh) (atlasSize H K τ₀ Dmesh T ^ 16) κ a n₀
    _ ω ν E B (fun g => g.1) (fun g => g.2.1) U m cp up Qp Rp A F
    hU (native_groups_fiber_disjoint S P B K H q a mid) hsub hinside
    (by positivity) hcount hb.2 hb.1 hchart le_rfl

end
end Submission.Obl.k4_horizon_chart_assembly
