import Submission.Obl.k4_scalar_grid_polynomial_qualification.ParameterRefinement
import Submission.Obl.k4_scalar_grid_polynomial_qualification.CoefficientZoom

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory
open Submission.Lib.K4ReferencePruning

noncomputable section

def productEntryReference {A Q V : Type*} [DecidableEq A] [MeasurableSpace V]
    (old : Q → ENNReal) (π : Measure V) (L : Q × V → Finset A)
    (e : A × (Q × V)) : ENNReal :=
  if e.1 ∈ L e.2 then old e.2.1 * π {e.2.2} else 0

/-- The product here is an OLD reference numerator, not an independence
claim for the current incidence law. -/
theorem sum_productEntryReference_le {A Q V : Type*} [DecidableEq A]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (old : Q → ENNReal) (π : Measure V) (L : Q × V → Finset A) (D : ENNReal)
    (hD : ∀ b, ((L b).card : ENNReal) ≤ D) :
    (∑' e, productEntryReference old π L e) ≤ D * ((∑' q, old q) * π univ) := by
  have hπ : ∑' v, π {v} = π univ := by
    simpa only [preimage_id, univ_inter] using
      (Submission.Obl.k4_crop_angular_finite_tail.measure_eq_tsum_label π
        measurable_id MeasurableSet.univ).symm
  have hprod : (∑' b : Q × V, old b.1 * π {b.2}) = (∑' q, old q) * π univ := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, hπ]
    exact ENNReal.tsum_mul_right
  simpa only [productEntryReference, hprod] using
    listed_reference_sum_le L (fun b => old b.1 * π {b.2}) D hD

/-- Sum all original state/palette reference weights before choosing and
normalizing one coefficient world. -/
theorem product_entry_reference_mass_budget {X A Q V : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A] [DecidableEq A]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ ν : Measure X) (oldState : X → Q) (hOld : Measurable oldState)
    (entry : X → A × (Q × V)) (hentry : Measurable entry)
    (π : Measure V) (L : Q × V → Finset A) (D η : ENNReal)
    (hD : ∀ b, ((L b).card : ENNReal) ≤ D) :
    μ univ ≤
      (μ.restrict (referenceKeep μ entry
        (productEntryReference (fun q => ν (oldState ⁻¹' {q})) π L) η)) univ +
          η * D * ν univ * π univ := by
  have hsum : (∑' q, ν (oldState ⁻¹' {q})) = ν univ := by
    simpa only [univ_inter] using
      (Submission.Obl.k4_crop_angular_finite_tail.measure_eq_tsum_label ν
        hOld MeasurableSet.univ).symm
  have hw := sum_productEntryReference_le (fun q => ν (oldState ⁻¹' {q})) π L D hD
  rw [hsum] at hw
  refine (reference_pruning_mass_budget μ entry hentry _ η).trans (add_le_add le_rfl ?_)
  exact (mul_le_mul_of_nonneg_left hw zero_le).trans_eq (by ring)

/-- Every retained listed entry has its floor under the restricted current
law, with the original state and palette factors still on the left side. -/
theorem retained_product_entry_floor {X A Q V : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSingletonClass A] [DecidableEq A]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (μ : Measure X) (entry : X → A × (Q × V)) (hentry : Measurable entry)
    (old : Q → ENNReal) (π : Measure V) (L : Q × V → Finset A) (η : ENNReal)
    {p : X} (hp : p ∈ referenceKeep μ entry (productEntryReference old π L) η)
    (hlisted : (entry p).1 ∈ L (entry p).2) :
    η * old (entry p).2.1 * π {(entry p).2.2} ≤
      (μ.restrict (referenceKeep μ entry (productEntryReference old π L) η))
        (entry ⁻¹' {entry p}) := by
  have hh : η * productEntryReference old π L (entry p) ≤ μ (entry ⁻¹' {entry p}) := hp
  rw [reference_kept_state_mass μ entry hentry _ η (entry p), ite_eq_left hh]
  simpa only [productEntryReference, ite_eq_left hlisted, mul_assoc] using hh

/-- A retained entry inherits the original fine-palette numerator divided
by its ORIGINAL coarse-palette weight. The current entry is never declared
independent of its palette. -/
theorem posterior_product_entry_cap {X A Q V J : Type*}
    [MeasurableSpace X] [MeasurableSpace A] [MeasurableSingletonClass A] [DecidableEq A]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace V] [MeasurableSingletonClass V] [MeasurableSpace J]
    (μ : Measure X) (entry : X → A × (Q × V)) (hentry : Measurable entry)
    (fineCode : X → J) (old : Q → ENNReal) (π : Measure V) (πfine : Measure J)
    (L : Q × V → Finset A) (C η : ENNReal) (hη0 : η ≠ 0) (hηtop : η ≠ ⊤)
    (hcap : ∀ e j, μ {p | entry p = e ∧ fineCode p = j} ≤ C * old e.2.1 * πfine {j})
    (e : A × (Q × V)) (hlisted : e.1 ∈ L e.2)
    (hP0 : π {e.2.2} ≠ 0) (hPtop : π {e.2.2} ≠ ⊤) (j : J) :
    (μ.restrict (referenceKeep μ entry (productEntryReference old π L) η))
        {p | entry p = e ∧ fineCode p = j} ≤
      ((C * πfine {j}) / (η * π {e.2.2})) *
        (μ.restrict (referenceKeep μ entry (productEntryReference old π L) η))
          (entry ⁻¹' {e}) := by
  classical
  let κ := μ.restrict (referenceKeep μ entry (productEntryReference old π L) η)
  have hmass := reference_kept_state_mass μ entry hentry (productEntryReference old π L) η e
  by_cases hkeep : η * productEntryReference old π L e ≤ μ (entry ⁻¹' {e})
  · have hmassEq : κ (entry ⁻¹' {e}) = μ (entry ⁻¹' {e}) := by
      simpa only [ite_eq_left hkeep] using hmass
    have hfloor : (η * π {e.2.2}) * old e.2.1 ≤ κ (entry ⁻¹' {e}) := by
      rw [hmassEq]
      calc
        _ = η * (old e.2.1 * π {e.2.2}) := by ring
        _ = η * productEntryReference old π L e := by
          rw [productEntryReference, ite_eq_left hlisted]
        _ ≤ _ := hkeep
    have hnum : κ {p | entry p = e ∧ fineCode p = j} ≤ (C * πfine {j}) * old e.2.1 := by
      calc
        _ ≤ μ {p | entry p = e ∧ fineCode p = j} := Measure.restrict_le_self _
        _ ≤ C * old e.2.1 * πfine {j} := hcap e j
        _ = _ := by ring
    exact Zoom.cap_of_palette_floor (mul_ne_zero hη0 hP0)
      (ENNReal.mul_ne_top hηtop hPtop) hnum hfloor
  · have hmassEq : κ (entry ⁻¹' {e}) = 0 := by simpa only [ite_eq_right hkeep] using hmass
    calc
      _ ≤ κ (entry ⁻¹' {e}) := measure_mono (fun _ hp => hp.1)
      _ = 0 := hmassEq
      _ ≤ _ := zero_le

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification
