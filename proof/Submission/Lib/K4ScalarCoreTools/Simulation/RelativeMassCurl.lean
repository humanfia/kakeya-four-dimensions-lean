/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/RelativeMassCurl.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Source: session x0212, branch x0212, commit179370d;
original owned file RelativeMassCurl.lean, with prior proof credit retained below.
-/

/-
From LOT session x0212, branch x0212, commit179370d,
Submission/Obl/k4_scalar_mesh_projection/RelativeMassCurl.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.HomogeneousCurl
import Submission.Lib.K4ScalarCoreTools.Simulation.FiniteReference

namespace Submission.Lib.K4ScalarCoreTools.Simulation

open Set MeasureTheory MvPolynomial
open Switching
open Submission.Lib.K4ScalarSwitching.Switching

/-- Relative original success and base ceilings give a mass-independent
coefficient curl estimate. The original finite reference and actual path
law are retained; their common total-mass factor cancels exactly. -/
theorem exists_original_relative_mass_curl_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ K L M p area ε : ℝ, 1 ≤ K → 1 ≤ L → 1 ≤ M →
        0 < p → p ≤ 1 → 0 ≤ area → 0 ≤ ε →
        ∀ (Θ : Type*) [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν] [NeZero ν]
          (μ : Measure (Θ × (Fin 4 → ℝ))) (S : Set (Θ × (Fin 4 → ℝ)))
          (x : Θ → Fin 2 → ℝ) (v : Θ → Fin 4 → ℝ) (X₀ : Θ → ℝ)
          (ι : Type*) (F : Finset ι) (E : Θ → ι → Set (Fin 2 → ℝ)) (c : Θ → ι → ℝ),
          Measurable x → MeasurableSet S →
          ν.map x ≤ ENNReal.ofReal (M * (ν univ).toReal) • volume →
          μ ≤ ENNReal.ofReal L • (ν.prod volume) →
          ENNReal.ofReal (p * (ν univ).toReal) ≤ μ S →
          (∀ z ∈ S, z.2 ∈ Icc (-1 : Fin 4 → ℝ) 1) →
          (∀ z ∈ S, x z.1 ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
            (∀ i, |v z.1 i| ≤ K) ∧ 1 / K ≤ |v z.1 1 - v z.1 0| ∧
              1 / K ≤ |v z.1 3 - v z.1 2|) →
          (∀ θ, ∀ i ∈ F, MeasurableSet (E θ i)) →
          (∀ θ, (∑ i ∈ F, volume (E θ i)) ≤ ENNReal.ofReal area) →
          (∀ z ∈ S, ∃ i ∈ F, switchedBaseEndpoint (x z.1) (v z.1) z.2 ∈ E z.1 i ∧
            |X₀ z.1 + eval z.2 (brokenHeight A B (x z.1) (v z.1)) - c z.1 i| ≤ ε) →
          ∀ e : Fin 2 →₀ ℕ, |(pderiv 0 B - pderiv 1 A).coeff e| ≤
            C * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε / p ^ (6 * D + 1) := by
  obtain ⟨C, hC, hcurl⟩ := exists_homogeneous_coefficient_curl_constant D
  refine ⟨C, hC, ?_⟩
  intro A B hA hB K L M p area ε hK hL hM hp hp1 harea hε
    Θ _ ν _ _ μ S x v X₀ ι F E c hx hS hbase hdom hmass hbox hdata hE hareaSum hcover e
  let m := (ν univ).toReal
  let ν₀ := (ν univ)⁻¹ • ν
  obtain ⟨hν₀, hm, hdom₀, hbase₀⟩ :=
    finite_reference_real_bounds ν volume μ x hx volume L (M * m)
      (by linarith : 0 ≤ L) hdom hbase
  letI : IsProbabilityMeasure ν₀ := hν₀
  have hm0 : m ≠ 0 := hm.ne'
  have hcancel : (M * m) / m = M := by field_simp [hm0]
  change ν₀.map x ≤ ENNReal.ofReal ((M * m) / m) • volume at hbase₀
  rw [hcancel] at hbase₀
  have h := hcurl A B hA hB K (L * m) M (p * m) area ε hK
    (mul_pos (by linarith : 0 < L) hm) hM (mul_pos hp hm)
    (mul_le_mul_of_nonneg_right (hp1.trans hL) hm.le) harea hε
    Θ ν₀ μ S x v X₀ ι F E c hx hS hbase₀ hdom₀ hmass hbox hdata hE hareaSum hcover e
  have hid : C * K ^ 4 * (L * m) ^ (6 * D + 1) * M ^ (2 * D) * area * ε /
      (p * m) ^ (6 * D + 1) =
      C * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * area * ε / p ^ (6 * D + 1) := by
    apply (div_eq_div_iff (pow_ne_zero _ (mul_ne_zero hp.ne' hm0))
      (pow_ne_zero _ hp.ne')).mpr
    rw [mul_pow, mul_pow]
    ring
  exact h.trans_eq hid

end Submission.Lib.K4ScalarCoreTools.Simulation
