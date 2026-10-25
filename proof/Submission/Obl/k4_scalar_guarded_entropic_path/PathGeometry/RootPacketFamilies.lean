/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/RootPacketFamilies.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.UniformRootCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartBudgets
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.BudgetedPacketFloors

/-! Feed the ACTUAL root charts into common-law packet-floor pruning.
Before their eventual availability a family is empty; no prior, weight or
common path law is changed, and no residual or candidate chooses the data. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPacketFamilies

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open PathMeasures PathPruning IntermediateLiftSupport

noncomputable section

structure SamplePackets (p : Code) (K : ℕ) where
  generation : ℕ
  count : ℕ
  world : Fin count → Fin (W p K)
  block : Fin count → Fin (2 ^ generation)
  assignment : Fin count → Set (ℕ × (Fin 5 → ℝ))
  measurable_assignment : ∀ d, MeasurableSet (assignment d)
  budget : (∑ d, ENNReal.ofReal (ω p K (world d)) *
    ENNReal.ofReal (((2 : ℝ) ^ generation)⁻¹) * ν p K (world d) (assignment d)) ≤ 1

def sampleOfChoice {p : Code} (hp : Exact p) {B K : ℕ} {r b h ε : ℝ}
    (choice : Option (ChartW p B r b h ε true K)) : SamplePackets p K :=
  match choice with
  | none =>
      { generation := 0
        count := 0
        world := Fin.elim0
        block := Fin.elim0
        assignment := Fin.elim0
        measurable_assignment d := Fin.elim0 d
        budget := by simp }
  | some Q =>
      { generation := Q.T
        count := Q.n
        world := Q.γ
        block := Q.j
        assignment := Q.A
        measurable_assignment d := (Q.hcd.2.2.1 d).1
        budget := ChartBudgets.assignment_budget_le_one hp Q }

/-- Empty early families are harmless. Every later piece is the actual
original chart's full assignment and exact original dyadic time block. -/
def familyOfChoices {p z : Code} (view : RefinementChain p z) (hp : Exact p)
    {B : ℕ} {r b h ε : ℝ}
    (choices : (k : ℕ) → Option (ChartW p B r b h ε true (view.sample k))) : PacketFamily z :=
  let data := fun k => sampleOfChoice hp (choices k)
  { parent := p
    view := view
    count k := (data k).count
    world k := (data k).world
    assignment k := (data k).assignment
    timeBlock k d := I (data k).generation ((data k).block d)
    duration k := ((2 : ℝ) ^ (data k).generation)⁻¹
    measurable_assignment k := (data k).measurable_assignment
    measurable_timeBlock _ _ := measurableSet_Icc
    budget k := (data k).budget }

/-- Selected-chart coverage implies coverage by the unchanged full-prior
cells used by the existing simultaneous pruning theorem. -/
theorem familyOfChoices_covers {p z : Code} (view : RefinementChain p z) (hp : Exact p)
    {B k : ℕ} {r b h ε : ℝ}
    (choices : (n : ℕ) → Option (ChartW p B r b h ε true (view.sample n)))
    (Q : ChartW p B r b h ε true (view.sample k)) (hchoice : choices k = some Q)
    (ρ : Measure (Fin (W z k) × PathMeasures.State))
    (hcover : ∀ᵐ u ∂ρ.map (view.pullback k), u ∈ chartRegion Q) :
    ∀ᵐ u ∂ρ, ∃ d : (familyOfChoices view hp choices).Index k,
      u ∈ (familyOfChoices view hp choices).cell k d := by
  filter_upwards [ae_of_ae_map (view.measurable_pullback k).aemeasurable hcover] with u hu
  obtain ⟨d, hworld, hC⟩ := hu
  change ∃ d : Fin (sampleOfChoice hp (choices k)).count,
    view.pullback k u ∈ {(sampleOfChoice hp (choices k)).world d} ×ˢ
      ((sampleOfChoice hp (choices k)).assignment d ×ˢ
        I (sampleOfChoice hp (choices k)).generation ((sampleOfChoice hp (choices k)).block d))
  rw [hchoice]
  exact ⟨d, hworld.symm, ((Q.hcd.2.2.2.2.1 d) hC).2⟩

open PathNodes PathNodes.TrueGridPath

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

abbrev GoodCharts (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (ε : ℝ) (k : ℕ) : Prop :=
  ∀ j : Fin targets.length, ∃ P : path.UniformRootTerminalChart i certs ε k j,
    ChartGeometry.ofChart P = path.rootGeometry i certs k j ∧
    ∀ ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State),
      ρ ≪ worldMixture (path.forget.finalFamily.problem i) k →
      ∀ᵐ u ∂ρ.map ((path.measuredChain i certs).pullback k), u ∈ chartRegion P

/-- The entire finite chart family is fixed before any later residual. -/
def rootChoices (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (ε : ℝ) (j : Fin targets.length) (k : ℕ) :
    Option (path.UniformRootTerminalChart i certs ε k j) := by
  classical
  exact if hk : GoodCharts path i certs ε k then some (Classical.choose (hk j)) else none

def rootPacketFamily (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (ε : ℝ) (j : Fin targets.length) :
    PacketFamily (path.forget.finalFamily.problem i) :=
  familyOfChoices (path.measuredChain i certs) (source.angular i).1
    (rootChoices path i certs ε j)

theorem eventually_rootChoices (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ j : Fin targets.length,
      ∃ P : path.UniformRootTerminalChart i certs ε k j,
        rootChoices path i certs ε j k = some P ∧
        ChartGeometry.ofChart P = path.rootGeometry i certs k j ∧
        ∀ ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State),
          ρ ≪ worldMixture (path.forget.finalFamily.problem i) k →
          ∀ᵐ u ∂ρ.map ((path.measuredChain i certs).pullback k), u ∈ chartRegion P := by
  filter_upwards [path.eventually_uniform_root_terminal_charts i certs hl ε hε] with k hk
  intro j
  have hgood : GoodCharts path i certs ε k := hk
  refine ⟨Classical.choose (hgood j), ?_, Classical.choose_spec (hgood j)⟩
  unfold rootChoices
  rw [dite_eq_left hgood]

theorem eventually_rootPacketFamily_covers (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (hl : path.forget.AllLayers i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (j : Fin targets.length)
      (ρ : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State)),
      ρ ≪ worldMixture (path.forget.finalFamily.problem i) k →
      ∀ᵐ u ∂ρ, ∃ d : (rootPacketFamily path i certs ε j).Index k,
        u ∈ (rootPacketFamily path i certs ε j).cell k d := by
  filter_upwards [eventually_rootChoices path i certs hl ε hε] with k hk
  intro j ρ hρ
  obtain ⟨P, hchoice, _, hcover⟩ := hk j
  exact familyOfChoices_covers (path.measuredChain i certs) (source.angular i).1
    (rootChoices path i certs ε j) P hchoice ρ (hcover ρ hρ)

theorem rootPacketFamily_view (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (ε : ℝ) (j : Fin targets.length) :
    (rootPacketFamily path i certs ε j).view = path.measuredChain i certs := rfl

/-- One common reference factor restores all final current root-packet
floors at once. Original full assignments and weights remain unchanged. -/
theorem simultaneous_root_packet_floors (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (ε : ℝ) (k : ℕ) (R H : ℝ)
    (hR : (path.measuredChain i certs).referenceFactor k ≤ R)
    (η : Measure (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State))
    (hη : η ≤ normalizedWorldMixture (path.forget.finalFamily.problem i) k)
    (A : Set (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State))
    (hA : MeasurableSet A) :
    ∃ E : Set (Fin (W (path.forget.finalFamily.problem i) k) × PathMeasures.State),
      MeasurableSet E ∧ E ⊆ A ∧
      η A ≤ η E + (targets.length : ENNReal) * (ENNReal.ofReal R / ENNReal.ofReal H) ∧
      ∀ (j : Fin targets.length) (d : (rootPacketFamily path i certs ε j).Index k),
        0 < ω (source.problem i) ((path.measuredChain i certs).sample k)
          ((rootPacketFamily path i certs ε j).world k d) →
        E ∩ (rootPacketFamily path i certs ε j).cell k d = ∅ ∨
          (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal ((rootPacketFamily path i certs ε j).duration k) *
            ν (source.problem i) ((path.measuredChain i certs).sample k)
              ((rootPacketFamily path i certs ε j).world k d)
              ((rootPacketFamily path i certs ε j).assignment k d) ≤
          (path.measuredChain i certs).submeasureWorldLaw k (η.restrict E)
            ((rootPacketFamily path i certs ε j).world k d)
            ((rootPacketFamily path i certs ε j).priorCell k d) := by
  exact simultaneous_budgeted_packet_floors (path.forget.finalFamily.angular i).1
    (fun j => rootPacketFamily path i certs ε j) R H (fun _ => hR) η hη A hA

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPacketFamilies
