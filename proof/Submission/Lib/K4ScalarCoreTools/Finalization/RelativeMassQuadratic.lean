/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/RelativeMassQuadratic.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: o062/x0511,03001f00, RelativeMassQuadratic.lean.
All matrix/jet recovery is imported. This wrapper keeps the original base-law mass in both the ceiling and floor.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.RobustQuadraticLines

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MvPolynomial MeasureTheory
open Submission.Lib.K4ScalarCoreTools.Simulation.Switching

/-- The absolute base ceiling may be arbitrarily small. Only the ratio
of the original success floor to that ceiling enters the Remez estimate. -/
theorem exists_homogeneous_mass_quadratic_restoration_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ K H E τ M p : ℝ, 1 ≤ K → 0 ≤ H → 0 ≤ E → 0 ≤ τ →
      0 < M → 0 < p → p ≤ M →
      (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ H) →
      ∀ (μ : Measure (Fin 2 → ℝ)) (S : Set (Fin 2 → ℝ)),
        μ ≤ ENNReal.ofReal M • volume → ENNReal.ofReal p ≤ μ S →
        S ⊆ Icc (-1 : Fin 2 → ℝ) 1 →
        (∀ z ∈ S, nearbyQuadraticLineFits P z K E τ) →
        ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
          (∀ e : Fin 2 →₀ ℕ, e.degree ≤ 2 → Q.coeff e = P.coeff e) ∧
          ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P - eval z Q| ≤
            C * K ^ 6 * (64 * ((D : ℝ) + 1) * M / p) ^ (2 * D) *
              (E + K ^ 3 * H * τ) := by
  obtain ⟨C, hC, hrestore⟩ := exists_quadratic_restoration_from_nearby_lines_constant D
  refine ⟨C, hC, ?_⟩
  intro P hP K H E τ M p hK hH hE hτ hM hp hpM hnorm μ S hdom hmass hS hlines
  have hη : 0 < p / M := div_pos hp hM
  have hη1 : p / M ≤ 1 := (div_le_one hM).mpr hpM
  have harea : ENNReal.ofReal (p / M) ≤ volume S := by
    rw [ENNReal.ofReal_div_of_pos hM]
    apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hM).ne' ENNReal.ofReal_ne_top).mpr
    calc
      ENNReal.ofReal p ≤ μ S := hmass
      _ ≤ (ENNReal.ofReal M • volume) S := hdom S
      _ = volume S * ENNReal.ofReal M := by
        rw [Measure.smul_apply, smul_eq_mul, mul_comm]
  obtain ⟨Q, hQ, hcoeff, herror⟩ := hrestore P hP K H E τ (p / M) hK hH hE hτ
    hη hη1 hnorm S hS harea hlines
  have hid : 64 * ((D : ℝ) + 1) / (p / M) = 64 * ((D : ℝ) + 1) * M / p := by
    field_simp [hp.ne', hM.ne']
  exact ⟨Q, hQ, hcoeff, fun z hz => by simpa only [hid] using herror z hz⟩

/-- Relative original mass cancels from the degree-restoration error.
The original base law and its successful subset are both unchanged. -/
theorem exists_relative_original_mass_quadratic_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ K H E τ M p : ℝ, 1 ≤ K → 0 ≤ H → 0 ≤ E → 0 ≤ τ →
      1 ≤ M → 0 < p → p ≤ 1 →
      (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ H) →
      ∀ (μ : Measure (Fin 2 → ℝ)) [IsFiniteMeasure μ] [NeZero μ] (S : Set (Fin 2 → ℝ)),
        μ ≤ ENNReal.ofReal (M * (μ univ).toReal) • volume →
        ENNReal.ofReal (p * (μ univ).toReal) ≤ μ S →
        S ⊆ Icc (-1 : Fin 2 → ℝ) 1 →
        (∀ z ∈ S, nearbyQuadraticLineFits P z K E τ) →
        ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
          (∀ e : Fin 2 →₀ ℕ, e.degree ≤ 2 → Q.coeff e = P.coeff e) ∧
          ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P - eval z Q| ≤
            C * K ^ 6 * (64 * ((D : ℝ) + 1) * M / p) ^ (2 * D) *
              (E + K ^ 3 * H * τ) := by
  obtain ⟨C, hC, hrestore⟩ := exists_homogeneous_mass_quadratic_restoration_constant D
  refine ⟨C, hC, ?_⟩
  intro P hP K H E τ M p hK hH hE hτ hM hp hp1 hnorm μ _ _ S hdom hmass hS hlines
  let m := (μ univ).toReal
  have hm : 0 < m := ENNReal.toReal_pos (NeZero.ne (μ univ)) (measure_ne_top _ _)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  obtain ⟨Q, hQ, hcoeff, herror⟩ := hrestore P hP K H E τ (M * m) (p * m)
    hK hH hE hτ (mul_pos hMpos hm) (mul_pos hp hm)
    (mul_le_mul_of_nonneg_right (hp1.trans hM) hm.le) hnorm μ S hdom hmass hS hlines
  have hid : 64 * ((D : ℝ) + 1) * (M * m) / (p * m) =
      64 * ((D : ℝ) + 1) * M / p := by
    field_simp [hp.ne', hm.ne']
  exact ⟨Q, hQ, hcoeff, fun z hz => by simpa only [hid] using herror z hz⟩

end Submission.Lib.K4ScalarCoreTools.Finalization
