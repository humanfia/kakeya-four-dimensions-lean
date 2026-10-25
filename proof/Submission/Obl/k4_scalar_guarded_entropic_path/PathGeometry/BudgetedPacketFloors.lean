/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/BudgetedPacketFloors.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.StablePruning
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SubmeasurePaths

/-! Simultaneous current floors for arbitrary original packet families.
A family is specified in one of the existing common-law views and carries
its unchanged original weighted full-prior budget. In particular this
consumer supports composed-prefix assignments, not only single refinements. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open PathMeasures

noncomputable section

structure PacketFamily (z : Code) where
  parent : Code
  view : RefinementChain parent z
  count : ℕ → ℕ
  world : (k : ℕ) → Fin (count k) → Fin (W parent (view.sample k))
  assignment : (k : ℕ) → Fin (count k) → Set (ℕ × ScalarCoeff)
  timeBlock : (k : ℕ) → Fin (count k) → Set ℝ
  duration : ℕ → ℝ
  measurable_assignment : ∀ k i, MeasurableSet (assignment k i)
  measurable_timeBlock : ∀ k i, MeasurableSet (timeBlock k i)
  budget : ∀ k, (∑ i, ENNReal.ofReal (ω parent (view.sample k) (world k i)) *
    ENNReal.ofReal (duration k) * ν parent (view.sample k) (world k i) (assignment k i)) ≤ 1

namespace PacketFamily

abbrev Index {z : Code} (a : PacketFamily z) (k : ℕ) := Fin (a.count k)

def priorCell {z : Code} (a : PacketFamily z) (k : ℕ) (i : a.Index k) : Set State :=
  a.assignment k i ×ˢ a.timeBlock k i

theorem measurableSet_priorCell {z : Code} (a : PacketFamily z) (k : ℕ) (i : a.Index k) :
    MeasurableSet (a.priorCell k i) :=
  (a.measurable_assignment k i).prod (a.measurable_timeBlock k i)

def cell {z : Code} (a : PacketFamily z) (k : ℕ) (i : a.Index k) :
    Set (Fin (W z k) × State) :=
  a.view.pullback k ⁻¹' ({a.world k i} ×ˢ a.priorCell k i)

theorem measurableSet_cell {z : Code} (a : PacketFamily z) (k : ℕ) (i : a.Index k) :
    MeasurableSet (a.cell k i) :=
  ((measurableSet_singleton _).prod (a.measurableSet_priorCell k i)).preimage
    (a.view.measurable_pullback k)

def referenceMass {z : Code} (a : PacketFamily z) (k : ℕ) (i : a.Index k) : ℝ≥0∞ :=
  ENNReal.ofReal (ω a.parent (a.view.sample k) (a.world k i)) *
    ENNReal.ofReal (a.duration k) *
      ν a.parent (a.view.sample k) (a.world k i) (a.assignment k i)

/-- Each original family has one full-prior budget, independently of the
number of packets in it. -/
theorem referenceMass_sum_le_one {z : Code} (a : PacketFamily z) (k : ℕ) :
    ∑ i, a.referenceMass k i ≤ 1 := a.budget k

def probabilityFloor {z : Code} (a : PacketFamily z) (R H : ℝ) (k : ℕ) (i : a.Index k) :
    ℝ≥0∞ := (ENNReal.ofReal R / ENNReal.ofReal H) * a.referenceMass k i

theorem probabilityFloor_sum_le {z : Code} (a : PacketFamily z) (R H : ℝ) (k : ℕ) :
    ∑ i, a.probabilityFloor R H k i ≤ ENNReal.ofReal R / ENNReal.ofReal H := by
  simp only [probabilityFloor, ← Finset.mul_sum]
  calc
    _ ≤ (ENNReal.ofReal R / ENNReal.ofReal H) * 1 :=
      mul_le_mul' le_rfl (a.referenceMass_sum_le_one k)
    _ = _ := mul_one _

theorem current_floor_of_probabilityFloor {z : Code} (a : PacketFamily z) (hz : Exact z)
    (R H : ℝ) (k : ℕ) (hR : a.view.referenceFactor k ≤ R)
    (η : Measure (Fin (W z k) × State)) (hη : η ≤ normalizedWorldMixture z k)
    (E : Set (Fin (W z k) × State)) (i : a.Index k)
    (hω : 0 < ω a.parent (a.view.sample k) (a.world k i))
    (hfloor : a.probabilityFloor R H k i ≤ η (E ∩ a.cell k i)) :
    (ENNReal.ofReal H)⁻¹ *
      ENNReal.ofReal (a.duration k) *
        ν a.parent (a.view.sample k) (a.world k i) (a.assignment k i) ≤
          a.view.submeasureWorldLaw k (η.restrict E) (a.world k i) (a.priorCell k i) := by
  have hηE : η.restrict E ≤ normalizedWorldMixture z k := Measure.restrict_le_self.trans hη
  have hmass := a.view.submeasureWorldLaw_weighted_apply hz k hηE (a.world k i)
    (a.measurableSet_priorCell k i)
  change ENNReal.ofReal (ω a.parent (a.view.sample k) (a.world k i)) * _ =
    a.view.originalLaw k univ * (η.restrict E) (a.cell k i) at hmass
  rw [Measure.restrict_apply (a.measurableSet_cell k i), inter_comm] at hmass
  have hMR : 1 ≤ a.view.originalLaw k univ * ENNReal.ofReal R := by
    calc
      _ = a.view.originalLaw k univ * (a.view.originalLaw k univ)⁻¹ :=
        (ENNReal.mul_inv_cancel (a.view.originalLaw_mass_pos hz k).ne'
          ((a.view.originalLaw_mass_le_one hz k).trans_lt (by simp)).ne).symm
      _ = a.view.originalLaw k univ * ENNReal.ofReal (a.view.referenceFactor k) := by
        rw [a.view.ofReal_referenceFactor hz k]
      _ ≤ _ := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hR)
  have hweighted : ENNReal.ofReal (ω a.parent (a.view.sample k) (a.world k i)) *
      ((ENNReal.ofReal H)⁻¹ *
        ENNReal.ofReal (a.duration k) *
          ν a.parent (a.view.sample k) (a.world k i)
            (a.assignment k i)) ≤
      ENNReal.ofReal (ω a.parent (a.view.sample k) (a.world k i)) *
        a.view.submeasureWorldLaw k (η.restrict E) (a.world k i) (a.priorCell k i) := by
    calc
      _ = 1 * (ENNReal.ofReal (ω a.parent (a.view.sample k) (a.world k i)) *
          ((ENNReal.ofReal H)⁻¹ *
            ENNReal.ofReal (a.duration k) *
              ν a.parent (a.view.sample k) (a.world k i)
                (a.assignment k i))) := (one_mul _).symm
      _ ≤ (a.view.originalLaw k univ * ENNReal.ofReal R) *
          (ENNReal.ofReal (ω a.parent (a.view.sample k) (a.world k i)) *
            ((ENNReal.ofReal H)⁻¹ *
              ENNReal.ofReal (a.duration k) *
                ν a.parent (a.view.sample k) (a.world k i)
                  (a.assignment k i))) := mul_le_mul' hMR le_rfl
      _ = a.view.originalLaw k univ * a.probabilityFloor R H k i := by
        simp only [probabilityFloor, referenceMass, div_eq_mul_inv]
        ac_rfl
      _ ≤ a.view.originalLaw k univ * η (E ∩ a.cell k i) := mul_le_mul' le_rfl hfloor
      _ = _ := hmass.symm
  have hω₀ := (ENNReal.ofReal_pos.mpr hω).ne'
  have hc := mul_le_mul'
    (show (ENNReal.ofReal (ω a.parent (a.view.sample k) (a.world k i)))⁻¹ ≤
      (ENNReal.ofReal (ω a.parent (a.view.sample k) (a.world k i)))⁻¹ from le_rfl) hweighted
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hω₀ ENNReal.ofReal_ne_top, one_mul] using hc

end PacketFamily

/-- All current floors are restored under the final selected law at once.
The omission cost depends on the number of layers, even if their individual
packet families have polynomially many entries. -/
theorem simultaneous_budgeted_packet_floors {z : Code} (hz : Exact z) {m k : ℕ}
    (layers : Fin m → PacketFamily z) (R H : ℝ)
    (hR : ∀ a, (layers a).view.referenceFactor k ≤ R)
    (η : Measure (Fin (W z k) × State)) (hη : η ≤ normalizedWorldMixture z k)
    (A : Set (Fin (W z k) × State)) (hA : MeasurableSet A) :
    ∃ E : Set (Fin (W z k) × State), MeasurableSet E ∧ E ⊆ A ∧
      η A ≤ η E + (m : ℝ≥0∞) * (ENNReal.ofReal R / ENNReal.ofReal H) ∧
      ∀ (a : Fin m) (i : (layers a).Index k),
        0 < ω (layers a).parent ((layers a).view.sample k) ((layers a).world k i) →
        E ∩ (layers a).cell k i = ∅ ∨
          (ENNReal.ofReal H)⁻¹ *
            ENNReal.ofReal ((layers a).duration k) *
              ν (layers a).parent ((layers a).view.sample k) ((layers a).world k i)
                ((layers a).assignment k i) ≤
                  (layers a).view.submeasureWorldLaw k (η.restrict E)
                    ((layers a).world k i) ((layers a).priorCell k i) := by
  classical
  let Index := Σ a : Fin m, (layers a).Index k
  let Cells : Index → Set (Fin (W z k) × State) := fun i => (layers i.1).cell k i.2
  let τ : Index → ℝ≥0∞ := fun i => (layers i.1).probabilityFloor R H k i.2
  have hbudget : ∑ i : Index, τ i ≤
      (m : ℝ≥0∞) * (ENNReal.ofReal R / ENNReal.ofReal H) := by
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ _a : Fin m, ENNReal.ofReal R / ENNReal.ofReal H :=
        Finset.sum_le_sum fun a _ => (layers a).probabilityFloor_sum_le R H k
      _ = _ := by simp
  obtain ⟨E, hE, hEA, hmass, hfloor⟩ := simultaneous_cell_pruning η Cells τ Finset.univ
    (fun i _ => (layers i.1).measurableSet_cell k i.2) A hA
  refine ⟨E, hE, hEA, hmass.trans (add_le_add le_rfl hbudget), ?_⟩
  intro a i hω
  rcases hfloor ⟨a, i⟩ (Finset.mem_univ _) with hempty | hprob
  · exact Or.inl hempty
  · exact Or.inr ((layers a).current_floor_of_probabilityFloor hz R H k (hR a) η hη E i hω hprob)


end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathPruning
