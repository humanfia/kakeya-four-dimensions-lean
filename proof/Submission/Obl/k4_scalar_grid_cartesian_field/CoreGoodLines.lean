-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreGoodLines.lean.
import Mathlib

/-!
# Lines avoiding null code classes

With a two-sided density of the incidence law against `θ ⊗ dt` on the graph
set `E`, almost every incidence lies on a line whose `E`-times avoid every
null class of a countable code (in practice: fine cube and coarse cube).
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set
open scoped ENNReal

section GoodLines

variable {α ι : Type*} [MeasurableSpace α] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [Countable ι]

/-- Incidences whose code class is null for `ρ|E`. -/
def nullCodeSet (ρ : Measure (α × ℝ)) (E : Set (α × ℝ)) (code : α × ℝ → ι) : Set (α × ℝ) :=
  {p | ρ.restrict E {p' | code p' = code p} = 0}

/-- Lines spending positive time of `E` in null code classes. -/
def badLines (ρ : Measure (α × ℝ)) (E : Set (α × ℝ)) (code : α × ℝ → ι) : Set α :=
  {l | volume {t | (l, t) ∈ E ∩ nullCodeSet ρ E code} ≠ 0}

theorem measurableSet_nullCodeSet (ρ : Measure (α × ℝ)) (E : Set (α × ℝ))
    (code : α × ℝ → ι) (hcode : Measurable code) :
    MeasurableSet (nullCodeSet ρ E code) := by
  have : nullCodeSet ρ E code = code ⁻¹' {i | ρ.restrict E (code ⁻¹' {i}) = 0} := rfl
  rw [this]
  exact hcode (Set.to_countable _).measurableSet

theorem nullCodeSet_null (ρ : Measure (α × ℝ)) (E : Set (α × ℝ))
    (code : α × ℝ → ι) :
    ρ.restrict E (nullCodeSet ρ E code) = 0 := by
  have : nullCodeSet ρ E code = code ⁻¹' {i | ρ.restrict E (code ⁻¹' {i}) = 0} := rfl
  rw [this, measure_preimage_eq_zero_iff_of_countable (Set.to_countable _)]
  intro i hi
  exact hi

theorem measurableSet_badLines (ρ : Measure (α × ℝ)) (E : Set (α × ℝ)) (hE : MeasurableSet E)
    (code : α × ℝ → ι) (hcode : Measurable code) :
    MeasurableSet (badLines ρ E code) := by
  have hm : MeasurableSet (E ∩ nullCodeSet ρ E code) :=
    hE.inter (measurableSet_nullCodeSet ρ E code hcode)
  have hf : Measurable fun l : α => volume (Prod.mk l ⁻¹' (E ∩ nullCodeSet ρ E code)) :=
    measurable_measure_prodMk_left hm
  exact hf (measurableSet_singleton 0).compl

/-- Bad lines carry no incidence mass on `E`. -/
theorem badLines_null (ρ : Measure (α × ℝ)) (θ : Measure α) [SFinite θ]
    (E : Set (α × ℝ)) (hE : MeasurableSet E) (code : α × ℝ → ι) (hcode : Measurable code)
    (Λ : ℝ)
    (hθρ : (θ.prod volume).restrict E ≤ ENNReal.ofReal Λ • ρ.restrict E)
    (hρθ : ρ.restrict E ≤ ENNReal.ofReal Λ • (θ.prod volume).restrict E) :
    ρ.restrict E (badLines ρ E code ×ˢ univ) = 0 := by
  have hm : MeasurableSet (E ∩ nullCodeSet ρ E code) :=
    hE.inter (measurableSet_nullCodeSet ρ E code hcode)
  -- the null classes are null for `θ ⊗ dt` on `E`
  have hprod : θ.prod volume (E ∩ nullCodeSet ρ E code) = 0 := by
    have h1 : (θ.prod volume).restrict E (nullCodeSet ρ E code) = 0 := by
      apply le_antisymm _ (zero_le)
      calc (θ.prod volume).restrict E (nullCodeSet ρ E code)
          ≤ (ENNReal.ofReal Λ • ρ.restrict E) (nullCodeSet ρ E code) := hθρ _
        _ = 0 := by
          rw [Measure.smul_apply, nullCodeSet_null, smul_zero]
    rwa [Measure.restrict_apply (measurableSet_nullCodeSet ρ E code hcode), inter_comm] at h1
  -- hence almost every line spends null time there
  have hθbad : θ (badLines ρ E code) = 0 := by
    have hae := (Measure.measure_prod_null hm).mp hprod
    rw [Filter.EventuallyEq, ae_iff] at hae
    exact hae
  have hbadm := measurableSet_badLines ρ E hE code hcode
  apply le_antisymm _ (zero_le)
  calc ρ.restrict E (badLines ρ E code ×ˢ univ)
      ≤ (ENNReal.ofReal Λ • (θ.prod volume).restrict E) (badLines ρ E code ×ˢ univ) := hρθ _
    _ ≤ ENNReal.ofReal Λ • θ.prod volume (badLines ρ E code ×ˢ univ) := by
        rw [Measure.smul_apply, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul' le_rfl (Measure.restrict_apply_le _ _)
    _ = 0 := by
        rw [Measure.prod_prod (μ := θ) (ν := (volume : Measure ℝ)), hθbad, zero_mul, smul_zero]

/-- On a good line, removing the null classes costs no time. -/
theorem volume_diff_null_of_not_bad (ρ : Measure (α × ℝ)) (E : Set (α × ℝ))
    (code : α × ℝ → ι) (l : α) (hl : l ∉ badLines ρ E code) (T : Set ℝ)
    (hT : T ⊆ {t | (l, t) ∈ E}) :
    volume (T \ {t | (l, t) ∈ nullCodeSet ρ E code}) = volume T := by
  rw [← Set.diff_inter_self_eq_diff]
  apply measure_diff_null
  simp only [badLines, ne_eq, mem_ofPred_eq, not_not] at hl
  apply measure_mono_null _ hl
  intro t ht
  exact ⟨hT ht.2, ht.1⟩

end GoodLines

end Submission.Obl.k4_scalar_grid_cartesian_field
