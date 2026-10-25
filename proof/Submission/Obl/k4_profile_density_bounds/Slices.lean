import Mathlib
import Submission.Obl.k4_profile_density_bounds.Common

open MeasureTheory Set Filter
open scoped ENNReal

/-!
# Slices of observation sets

The reference measure `(volume ⊗ count) ⊗ count` on observations is the sum over the hidden
and velocity bins of the volumes of the base slices. Consequences: the base projection of a
measurable observation set has volume at most its reference measure, and a measure that is
dominated by `c * volume` on every cell is dominated by `c * reference`.
-/

namespace Submission.Obl.k4_profile_density_bounds

/-- The base slice of an observation set at hidden bin `h` and velocity bin `v`. -/
def slice (L : Set Observation) (h : ℤ) (v : Fin 2 → ℤ) : Set Base := {x | ((x, h), v) ∈ L}

lemma measurableSet_slice {L : Set Observation} (hL : MeasurableSet L) (h : ℤ) (v : Fin 2 → ℤ) :
    MeasurableSet (slice L h v) := by
  have : Measurable (fun x : Base => (((x, h), v) : Observation)) := by fun_prop
  exact this hL

/-- The reference measure of a measurable observation set is the sum over all hidden and velocity
bins of the volumes of its base slices. -/
lemma reference_eq_tsum {L : Set Observation} (hL : MeasurableSet L) :
    reference L = ∑' v : Fin 2 → ℤ, ∑' h : ℤ, volume (slice L h v) := by
  rw [reference, Measure.prod_apply_symm hL, lintegral_count]
  congr 1
  ext v
  have hv : MeasurableSet ((fun y : Base × ℤ => (y, v)) ⁻¹' L) := by
    have : Measurable (fun y : Base × ℤ => ((y, v) : Observation)) := by fun_prop
    exact this hL
  rw [Measure.prod_apply_symm hv, lintegral_count]
  rfl

/-- The base projection of an observation set. -/
def baseProj (L : Set Observation) : Set Base := {x | ∃ h v, ((x, h), v) ∈ L}

lemma baseProj_eq_iUnion (L : Set Observation) :
    baseProj L = ⋃ v : Fin 2 → ℤ, ⋃ h : ℤ, slice L h v := by
  ext x
  simp only [baseProj, slice, mem_ofPred_eq, mem_iUnion]
  exact ⟨fun ⟨h, v, hx⟩ => ⟨v, h, hx⟩, fun ⟨v, h, hx⟩ => ⟨h, v, hx⟩⟩

lemma measurableSet_baseProj {L : Set Observation} (hL : MeasurableSet L) :
    MeasurableSet (baseProj L) := by
  rw [baseProj_eq_iUnion]
  exact MeasurableSet.iUnion fun v => MeasurableSet.iUnion fun h => measurableSet_slice hL h v

/-- The base projection of a measurable observation set has volume at most its reference
measure (sum over the bins). -/
lemma volume_baseProj_le {L : Set Observation} (hL : MeasurableSet L) :
    volume (baseProj L) ≤ reference L := by
  rw [reference_eq_tsum hL, baseProj_eq_iUnion]
  calc volume (⋃ v : Fin 2 → ℤ, ⋃ h : ℤ, slice L h v)
      ≤ ∑' v : Fin 2 → ℤ, volume (⋃ h : ℤ, slice L h v) := measure_iUnion_le _
    _ ≤ ∑' v : Fin 2 → ℤ, ∑' h : ℤ, volume (slice L h v) :=
        ENNReal.tsum_le_tsum fun v => measure_iUnion_le _

/-- A measure on observations that gives every cell `B × {h} × {v}` mass at most `c * vol B`
gives every measurable set mass at most `c` times its reference measure. -/
lemma measure_le_mul_reference (Q : Measure Observation) (c : ℝ≥0∞)
    (hQ : ∀ B : Set Base, MeasurableSet B → ∀ (h : ℤ) (v : Fin 2 → ℤ),
      Q ((B ×ˢ {h}) ×ˢ {v}) ≤ c * volume B)
    {L : Set Observation} (hL : MeasurableSet L) : Q L ≤ c * reference L := by
  have hcover : L ⊆ ⋃ v : Fin 2 → ℤ, ⋃ h : ℤ, (slice L h v ×ˢ {h}) ×ˢ {v} := by
    rintro ⟨⟨x, h⟩, v⟩ hx
    simp only [mem_iUnion, mem_prod, mem_singleton_iff]
    exact ⟨v, h, ⟨hx, rfl⟩, rfl⟩
  calc Q L ≤ Q (⋃ v : Fin 2 → ℤ, ⋃ h : ℤ, (slice L h v ×ˢ {h}) ×ˢ {v}) := measure_mono hcover
    _ ≤ ∑' v : Fin 2 → ℤ, Q (⋃ h : ℤ, (slice L h v ×ˢ {h}) ×ˢ {v}) := measure_iUnion_le _
    _ ≤ ∑' v : Fin 2 → ℤ, ∑' h : ℤ, Q ((slice L h v ×ˢ {h}) ×ˢ {v}) :=
        ENNReal.tsum_le_tsum fun v => measure_iUnion_le _
    _ ≤ ∑' v : Fin 2 → ℤ, ∑' h : ℤ, c * volume (slice L h v) :=
        ENNReal.tsum_le_tsum fun v => ENNReal.tsum_le_tsum fun h =>
          hQ _ (measurableSet_slice hL h v) h v
    _ = c * reference L := by
        rw [reference_eq_tsum hL, ← ENNReal.tsum_mul_left]
        congr 1
        ext v
        rw [ENNReal.tsum_mul_left]

end Submission.Obl.k4_profile_density_bounds
