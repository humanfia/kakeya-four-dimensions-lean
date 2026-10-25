import Mathlib

/-!
Adapted from: here:o114 (session x0383).

Assembly of the preliminary labels after the source parameters have been fixed.
The source's identity is omitted from the output label. An assignment is a fiber
of the single bin selected by that source, followed by geometric eligibility.
-/

namespace Submission.Lib.K4RepresentativeAssembly

open MeasureTheory Set

variable {X T Ω α β : Type*}

/-- The compatibility list supplied by the old observation lists all the bins
supplied by its possible old labels. -/
def composedList [DecidableEq β] (L : Finset α) (compat : α → Finset β) : Finset β :=
  L.biUnion compat

theorem mem_composedList [DecidableEq β] {L : Finset α} {compat : α → Finset β}
    {a : α} {b : β} (ha : a ∈ L) (hb : b ∈ compat a) :
    b ∈ composedList L compat := Finset.mem_biUnion.mpr ⟨a, ha, hb⟩

/-- Combining the old list and the compatibility table multiplies their size
bounds. This applies to the frame list and then to the neighboring anchor bins. -/
theorem card_composedList_le [DecidableEq β] (L : Finset α) (compat : α → Finset β)
    {K : ℝ} (hcompat : ∀ a ∈ L, ((compat a).card : ℝ) ≤ K) :
    ((composedList L compat).card : ℝ) ≤ (L.card : ℝ) * K := by
  calc
    _ ≤ ∑ a ∈ L, ((compat a).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ L, K := Finset.sum_le_sum hcompat
    _ = _ := by simp [nsmul_eq_mul]

/-- A trajectory has only one source-selected bin in its new time block. -/
def binAssignment (tag : X → Option β) (eligible : β → X → Prop) (b : β) : Set X :=
  {x | tag x = some b ∧ eligible b x}

theorem binAssignment_pairwise (tag : X → Option β) (eligible : β → X → Prop) :
    Pairwise (fun b c => Disjoint (binAssignment tag eligible b)
      (binAssignment tag eligible c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hbc (Option.some.inj (hx.1.symm.trans hy.1))

/-- The later-time event only uses the original event, geometric assignment and
observation list. Analytical deletion masks need not appear in this event. -/
def assembledEvent (E : Set (X × T)) (tag : X → Option β)
    (eligible : β → X → Prop) (obs : X × T → Ω) (lst : Ω → Finset β) (b : β) :
    Set (X × T) :=
  {p | p ∈ E ∧ p.1 ∈ binAssignment tag eligible b ∧ b ∈ lst (obs p)}

theorem assembledEvent_subset (E : Set (X × T)) (tag : X → Option β)
    (eligible : β → X → Prop) (obs : X × T → Ω) (lst : Ω → Finset β) (b : β) :
    assembledEvent E tag eligible obs lst b ⊆ E := fun _ hp => hp.1

theorem assembledEvent_assignment (E : Set (X × T)) (tag : X → Option β)
    (eligible : β → X → Prop) (obs : X × T → Ω) (lst : Ω → Finset β) (b : β)
    {p : X × T} (hp : p ∈ assembledEvent E tag eligible obs lst b) :
    p.1 ∈ binAssignment tag eligible b ∧ b ∈ lst (obs p) := hp.2

theorem measurableSet_assembledEvent [MeasurableSpace X] [MeasurableSpace T]
    {E : Set (X × T)} (tag : X → Option β) (eligible : β → X → Prop)
    (obs : X × T → Ω) (lst : Ω → Finset β) (b : β)
    (hE : MeasurableSet E) (hA : MeasurableSet (binAssignment tag eligible b))
    (hlst : MeasurableSet {p | b ∈ lst (obs p)}) :
    MeasurableSet (assembledEvent E tag eligible obs lst b) :=
  hE.inter ((hA.preimage measurable_fst).inter hlst)

theorem assembledEvent_pairwise (E : Set (X × T)) (tag : X → Option β)
    (eligible : β → X → Prop) (obs : X × T → Ω) (lst : Ω → Finset β) :
    Pairwise (fun b c => Disjoint (assembledEvent E tag eligible obs lst b)
      (assembledEvent E tag eligible obs lst c)) := by
  intro b c hbc
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact Set.disjoint_left.mp (binAssignment_pairwise tag eligible hbc) hp.2.1 hq.2.1

/-- Every frozen successful incidence is contained in the geometrically defined
output event of its bin. Thus enlarging away the analytical masks preserves mass. -/
theorem successfulMass_le_assembledMass [MeasurableSpace X] [MeasurableSpace T]
    [Fintype β] (μ : Measure (X × T))
    (E S : Set (X × T)) (tag : X → Option β) (eligible : β → X → Prop)
    (obs : X × T → Ω) (lst : Ω → Finset β)
    (hS : ∀ p ∈ S, ∃ b, p ∈ E ∧ tag p.1 = some b ∧ eligible b p.1 ∧
      b ∈ lst (obs p)) :
    μ S ≤ ∑ b, μ (assembledEvent E tag eligible obs lst b) := by
  have hsub : S ⊆ ⋃ b, assembledEvent E tag eligible obs lst b := by
    intro p hp
    obtain ⟨b, hE, htag, heligible, hlist⟩ := hS p hp
    exact Set.mem_iUnion.mpr ⟨b, hE, ⟨htag, heligible⟩, hlist⟩
  exact (measure_mono hsub).trans (measure_iUnion_fintype_le μ _)

end Submission.Lib.K4RepresentativeAssembly
