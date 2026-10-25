-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.SlicedWitnesses; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Lib.K4FinalLawSelection

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal

noncomputable section

abbrev SliceIndex {ι Q : Type*} (menus : ι → Finset Q) := Σ i, {q : Q // q ∈ menus i}

def sliceEvent {Ω ι Q : Type*} (menus : ι → Finset Q)
    (E : ι → Set Ω) (code : Ω → Q) (e : SliceIndex menus) : Set Ω :=
  E e.1 ∩ code ⁻¹' {e.2.val}

theorem measurableSet_sliceEvent {Ω ι Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (menus : ι → Finset Q) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (code : Ω → Q) (hcode : Measurable code) (e : SliceIndex menus) :
    MeasurableSet (sliceEvent menus E code e) :=
  (hE e.1).inter (hcode (measurableSet_singleton _))

/-- Original disjoint assignments remain disjoint when sliced by one
literal source code. -/
theorem sliceEvent_disjoint {Ω ι Q : Type*}
    (menus : ι → Finset Q) (E : ι → Set Ω)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) (code : Ω → Q) :
    Pairwise (fun e f : SliceIndex menus =>
      Disjoint (sliceEvent menus E code e) (sliceEvent menus E code f)) := by
  rintro ⟨i, q⟩ ⟨j, r⟩ hne
  apply Set.disjoint_left.mpr
  intro ω hω hω'
  by_cases hij : i = j
  · subst j
    have hq : code ω = q.val := hω.2
    have hr : code ω = r.val := hω'.2
    have heq : q = r := Subtype.ext (hq.symm.trans hr)
    subst r
    exact hne rfl
  · exact (Set.disjoint_left.mp (hdisj hij)) hω.1 hω'.1

theorem slice_reference_sum {ι Q : Type*} [Fintype ι]
    (menus : ι → Finset Q) (w : ι → ℝ≥0∞) :
    (∑ e : SliceIndex menus, w e.1) = ∑ i, ((menus i).card : ℝ≥0∞) * w i := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]

/-- Slicing the original labels by an actual measurable domain code keeps
a finite cover of the whole current law. -/
theorem sliceEvent_cover {Ω ι Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (menus : ι → Finset Q) (E : ι → Set Ω) (code : Ω → Q)
    (hcover : ∀ᵐ ω ∂μ, ∃ i, ω ∈ E i)
    (hmenu : ∀ i ω, ω ∈ E i → code ω ∈ menus i) :
    ∀ᵐ ω ∂μ, ∃ e : SliceIndex menus, ω ∈ sliceEvent menus E code e := by
  filter_upwards [hcover] with ω hω
  obtain ⟨i, hi⟩ := hω
  exact ⟨⟨i, code ω, hmenu i ω hi⟩, hi, rfl⟩

/-- Store all sliced marginal witnesses under one common restriction.
Subsequent pair restrictions are free to have arbitrarily small individual
entry masses; their stored witnesses and original weights stay separate. -/
theorem exists_stored_sliced_witnesses {Ω ι Q C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Fintype ι]
    (μ : Measure Ω) (menus : ι → Finset Q) (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (code : Ω → Q) (hcode : Measurable code)
    (w : ι → ℝ≥0∞) (δ : ℝ≥0∞) (layer : C → ι → Prop)
    (hcover : ∀ c, ∀ᵐ ω ∂μ, ∃ i, layer c i ∧ ω ∈ E i)
    (hmenu : ∀ i ω, ω ∈ E i → code ω ∈ menus i) :
    ∃ (σ : Measure Ω) (S : Finset (SliceIndex menus)), σ ≤ μ ∧
      μ univ ≤ σ univ + δ * ∑ i, ((menus i).card : ℝ≥0∞) * w i ∧
      (∀ e ∈ S, δ * w e.1 ≤ σ (sliceEvent menus E code e)) ∧
      (∀ c, ∀ᵐ ω ∂σ, ∃ e ∈ S, layer c e.1 ∧ ω ∈ sliceEvent menus E code e) := by
  classical
  obtain ⟨σ, S, hσ, hmass, -, hfloor, hretained⟩ :=
    Submission.Lib.K4FinalLawSelection.simultaneous_floor_layers
      Finset.univ (sliceEvent menus E code) (measurableSet_sliceEvent menus E hE code hcode)
      (fun e => δ * w e.1) μ (fun c e => layer c e.1) (by
        intro c
        filter_upwards [hcover c] with ω hω
        obtain ⟨i, hci, hi⟩ := hω
        let e : SliceIndex menus := ⟨i, code ω, hmenu i ω hi⟩
        exact ⟨e, Finset.mem_univ e, hci, hi, rfl⟩)
  have hcost : (∑ e : SliceIndex menus, δ * w e.1) =
      δ * ∑ i, ((menus i).card : ℝ≥0∞) * w i := by
    rw [← Finset.mul_sum, slice_reference_sum]
  rw [hcost] at hmass
  exact ⟨σ, S, hσ, hmass, hfloor, hretained⟩

end
end Submission.Obl.k4_general_compared_layers_velocity_lists
