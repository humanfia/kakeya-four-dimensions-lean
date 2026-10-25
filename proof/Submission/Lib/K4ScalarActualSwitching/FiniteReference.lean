/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit eafdbfde084be1469a1b66de9c3cae4d6786d880,
Submission/Obl/k4_scalar_mesh_projection/FiniteReference.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Mathlib

namespace Submission.Lib.K4ScalarActualSwitching

open Set MeasureTheory
open scoped ENNReal

/-- A finite original start reference can be made a probability reference
while the successful path law stays unchanged. The original mass factor
is retained explicitly in its density ceiling. -/
theorem path_ceiling_with_probability_reference {Θ T : Type*}
    [MeasurableSpace Θ] [MeasurableSpace T]
    (ν : Measure Θ) [IsFiniteMeasure ν] [NeZero ν]
    (τ : Measure T) [SFinite τ] (ρ : Measure (Θ × T)) (C : ENNReal)
    (hρ : ρ ≤ C • ν.prod τ) :
    ρ ≤ (C * ν univ) • (((ν univ)⁻¹ • ν).prod τ) := by
  have hfactor : ν = ν univ • ((ν univ)⁻¹ • ν) := by
    rw [smul_smul, ENNReal.mul_inv_cancel (NeZero.ne (ν univ)) (measure_ne_top _ _), one_smul]
  calc
    ρ ≤ C • ν.prod τ := hρ
    _ = C • (ν univ • ((ν univ)⁻¹ • ν)).prod τ :=
      congrArg (fun ζ : Measure Θ => C • ζ.prod τ) hfactor
    _ = (C * ν univ) • (((ν univ)⁻¹ • ν).prod τ) := by
      rw [Measure.prod_smul_left, smul_smul]

/-- The fixed-reference base ceiling pays exactly the inverse original
mass. This rescales only the reference used by an endpoint estimate. -/
theorem base_ceiling_with_probability_reference {Θ B : Type*}
    [MeasurableSpace Θ] [MeasurableSpace B]
    (ν : Measure Θ) [IsFiniteMeasure ν] [NeZero ν]
    (x : Θ → B) (hx : Measurable x) (σ : Measure B) (M : ENNReal)
    (hbase : ν.map x ≤ M • σ) :
    ((ν univ)⁻¹ • ν).map x ≤ (M / ν univ) • σ := by
  rw [Measure.map_smul _ hx.aemeasurable]
  calc
    _ ≤ (ν univ)⁻¹ • (M • σ) := smul_le_smul_left _ hbase
    _ = (M / ν univ) • σ := by
      rw [smul_smul, div_eq_mul_inv, mul_comm]

/-- Both ceilings in real units, suitable for an endpoint estimate whose
reference is a probability measure. Its successful law `ρ` is unchanged. -/
theorem finite_reference_real_bounds {Θ T B : Type*}
    [MeasurableSpace Θ] [MeasurableSpace T] [MeasurableSpace B]
    (ν : Measure Θ) [IsFiniteMeasure ν] [NeZero ν]
    (τ : Measure T) [SFinite τ] (ρ : Measure (Θ × T))
    (x : Θ → B) (hx : Measurable x) (σ : Measure B) (L M : ℝ) (hL : 0 ≤ L)
    (hρ : ρ ≤ ENNReal.ofReal L • ν.prod τ)
    (hbase : ν.map x ≤ ENNReal.ofReal M • σ) :
    let m := (ν univ).toReal
    let ν₀ := (ν univ)⁻¹ • ν
    IsProbabilityMeasure ν₀ ∧ 0 < m ∧
      ρ ≤ ENNReal.ofReal (L * m) • ν₀.prod τ ∧
      ν₀.map x ≤ ENNReal.ofReal (M / m) • σ := by
  let m := (ν univ).toReal
  have hm : 0 < m := ENNReal.toReal_pos (NeZero.ne (ν univ)) (measure_ne_top _ _)
  have hmass : ENNReal.ofReal m = ν univ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hprod := path_ceiling_with_probability_reference ν τ ρ (ENNReal.ofReal L) hρ
  have hproj := base_ceiling_with_probability_reference ν x hx σ (ENNReal.ofReal M) hbase
  have hprodscalar : ENNReal.ofReal (L * m) = ENNReal.ofReal L * ν univ := by
    rw [ENNReal.ofReal_mul hL, hmass]
  have hprojscalar : ENNReal.ofReal (M / m) = ENNReal.ofReal M / ν univ := by
    rw [ENNReal.ofReal_div_of_pos hm, hmass]
  exact ⟨inferInstance, hm, by simpa only [← hprodscalar] using hprod,
    by simpa only [← hprojscalar] using hproj⟩

end Submission.Lib.K4ScalarActualSwitching
