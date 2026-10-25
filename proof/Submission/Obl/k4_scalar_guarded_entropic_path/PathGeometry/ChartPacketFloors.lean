import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.BudgetedPacketFloors
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChartBudgets

/-! Actual original-root chart rows supply the unchanged-prior packet
families for shared current-floor pruning across every potential parent. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_true_terminal_lifting (ChartW)
open PathMeasures

noncomputable section

/-- The original packet budget at a single actual original sample. -/
structure PacketSample (p : Code) (k : ℕ) where
  count : ℕ
  world : Fin count → Fin (W p k)
  assignment : Fin count → Set (ℕ × ScalarCoeff)
  timeBlock : Fin count → Set ℝ
  duration : ℝ
  measurable_assignment : ∀ i, MeasurableSet (assignment i)
  measurable_timeBlock : ∀ i, MeasurableSet (timeBlock i)
  budget : (∑ i, ENNReal.ofReal (ω p k (world i)) * ENNReal.ofReal duration *
    ν p k (world i) (assignment i)) ≤ 1

namespace PacketSample

variable {p : Code} {k : ℕ}

def empty (p : Code) (k : ℕ) : PacketSample p k where
  count := 0
  world := Fin.elim0
  assignment := Fin.elim0
  timeBlock := Fin.elim0
  duration := 1
  measurable_assignment i := Fin.elim0 i
  measurable_timeBlock i := Fin.elim0 i
  budget := by simp

/-- The reference budget uses each chart's full original assignment and
actual dyadic time, rather than its selected incidence mass. -/
def ofChart (hp : Exact p) {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag k) : PacketSample p k where
  count := Q.n
  world := Q.γ
  assignment := Q.A
  timeBlock i := I Q.T (Q.j i)
  duration := ((2 : ℝ) ^ Q.T)⁻¹
  measurable_assignment i := (Q.hcd.2.2.1 i).1
  measurable_timeBlock _ := measurableSet_Icc
  budget := ChartBudgets.assignment_budget_le_one hp Q

end PacketSample

namespace PacketFamily

variable {p z : Code}

def ofSamples (view : RefinementChain p z)
    (data : (j : ℕ) → PacketSample p (view.sample j)) : PacketFamily z where
  parent := p
  view := view
  count j := (data j).count
  world j := (data j).world
  assignment j := (data j).assignment
  timeBlock j := (data j).timeBlock
  duration j := (data j).duration
  measurable_assignment j := (data j).measurable_assignment
  measurable_timeBlock j := (data j).measurable_timeBlock
  budget j := (data j).budget

/-- A finite-stage chart need only be supplied at the actual sample at
which pruning is performed. Other sample entries are empty packets. -/
def atSample (hp : Exact p) (view : RefinementChain p z) (k : ℕ)
    {B : ℕ} {r b h ε : ℝ} {flag : Bool}
    (Q : ChartW p B r b h ε flag (view.sample k)) : PacketFamily z :=
  ofSamples view (Function.update (fun j => PacketSample.empty p (view.sample j))
    k (PacketSample.ofChart hp Q))

end PacketFamily

/-- One common deletion gives the final current duration floors in all
candidate-parent views, with cost depending on the number of layers and
one common reference factor, independently of all packet counts. -/
theorem simultaneous_original_chart_floors {z : Code} (hz : Exact z) {m k : ℕ}
    (p : Fin m → Code) (hp : ∀ a, Exact (p a))
    (view : (a : Fin m) → RefinementChain (p a) z)
    (B : Fin m → ℕ) (r b h ε : Fin m → ℝ) (flag : Fin m → Bool)
    (Q : (a : Fin m) → ChartW (p a) (B a) (r a) (b a) (h a) (ε a) (flag a)
      ((view a).sample k))
    (R H : ℝ) (hR : ∀ a, (view a).referenceFactor k ≤ R)
    (η : Measure (Fin (W z k) × State)) (hη : η ≤ normalizedWorldMixture z k)
    (A : Set (Fin (W z k) × State)) (hA : MeasurableSet A) :
    ∃ E : Set (Fin (W z k) × State), MeasurableSet E ∧ E ⊆ A ∧
      η A ≤ η E + (m : ℝ≥0∞) * (ENNReal.ofReal R / ENNReal.ofReal H) ∧
      ∀ (a : Fin m) (i : Fin (Q a).n),
        0 < ω (p a) ((view a).sample k) ((Q a).γ i) →
        E ∩ ((view a).pullback k ⁻¹'
          ({(Q a).γ i} ×ˢ ((Q a).A i ×ˢ I (Q a).T ((Q a).j i)))) = ∅ ∨
          (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal (((2 : ℝ) ^ (Q a).T)⁻¹) *
            ν (p a) ((view a).sample k) ((Q a).γ i) ((Q a).A i) ≤
              (view a).submeasureWorldLaw k (η.restrict E) ((Q a).γ i)
                ((Q a).A i ×ˢ I (Q a).T ((Q a).j i)) := by
  classical
  let layers : Fin m → PacketFamily z := fun a => PacketFamily.atSample (hp a) (view a) k (Q a)
  have hout := simultaneous_budgeted_packet_floors hz layers R H hR η hη A hA
  obtain ⟨E, hE, hEA, hmass, hfloor⟩ := hout
  refine ⟨E, hE, hEA, hmass, ?_⟩
  intro a
  let F : PacketSample (p a) ((view a).sample k) → Prop := fun data =>
    ∀ i : Fin data.count,
      0 < ω (p a) ((view a).sample k) (data.world i) →
      E ∩ ((view a).pullback k ⁻¹'
        ({data.world i} ×ˢ (data.assignment i ×ˢ data.timeBlock i))) = ∅ ∨
        (ENNReal.ofReal H)⁻¹ * ENNReal.ofReal data.duration *
          ν (p a) ((view a).sample k) (data.world i) (data.assignment i) ≤
            (view a).submeasureWorldLaw k (η.restrict E) (data.world i)
              (data.assignment i ×ˢ data.timeBlock i)
  have hf : F (Function.update (fun j => PacketSample.empty (p a) ((view a).sample j))
      k (PacketSample.ofChart (hp a) (Q a)) k) := hfloor a
  rw [Function.update_self] at hf
  exact hf

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning
