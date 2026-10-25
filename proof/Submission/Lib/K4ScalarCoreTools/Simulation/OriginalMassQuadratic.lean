/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/OriginalMassQuadratic.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ffac21c,
Submission/Obl/k4_scalar_mesh_projection/OriginalMassQuadratic.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.RobustQuadraticLines

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Submission.Lib.K4ScalarSwitching.Switching
open Set MvPolynomial MeasureTheory

/-- Positive original base mass under a density ceiling supplies the area
needed for robust quadratic restoration. No successful law is normalized. -/
theorem exists_quadratic_restoration_from_original_mass_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ K H E τ M p : ℝ, 1 ≤ K → 0 ≤ H → 0 ≤ E → 0 ≤ τ →
      1 ≤ M → 0 < p → p ≤ 1 →
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
  intro P hP K H E τ M p hK hH hE hτ hM hp hp1 hnorm μ S hdom hmass hS hlines
  have hMp : 0 < M := by linarith
  have hη : 0 < p / M := div_pos hp hMp
  have hη1 : p / M ≤ 1 := (div_le_one hMp).mpr (hp1.trans hM)
  have harea : ENNReal.ofReal (p / M) ≤ volume S := by
    rw [ENNReal.ofReal_div_of_pos hMp]
    apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hMp)) ENNReal.ofReal_ne_top).mpr
    calc
      ENNReal.ofReal p ≤ μ S := hmass
      _ ≤ (ENNReal.ofReal M • volume) S := hdom S
      _ = volume S * ENNReal.ofReal M := by
        rw [Measure.smul_apply, smul_eq_mul, mul_comm]
  obtain ⟨Q, hQ, hcoeff, herror⟩ := hrestore P hP K H E τ (p / M) hK hH hE hτ
    hη hη1 hnorm S hS harea hlines
  refine ⟨Q, hQ, hcoeff, ?_⟩
  intro z hz
  have hid : 64 * ((D : ℝ) + 1) / (p / M) = 64 * ((D : ℝ) + 1) * M / p := by
    field_simp
  simpa only [hid] using herror z hz

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
