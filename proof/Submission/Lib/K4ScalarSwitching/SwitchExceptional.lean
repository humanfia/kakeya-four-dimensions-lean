/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit fe7a5f4,
Submission/Obl/k4_scalar_mesh_projection/SwitchExceptional.lean.
-/

import Submission.Lib.K4ScalarSwitching.SymmetricSublevel
import Submission.Lib.K4ScalarSwitching.SwitchScaling
import Submission.Lib.K4ScalarSwitching.SwitchEndpoint

namespace Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory MvPolynomial

/-- High curl selects one actual maximal minor whose small-value set in
any signed increment box has an explicit power-small relative volume. -/
theorem exists_small_cube_switching_sublevel_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (K q κ η : ℝ),
        1 ≤ K → 0 < q → 0 < κ → 0 < η → η ≤ 1 →
        (∀ i, |v i| ≤ K) → 1 / K ≤ |v 1 - v 0| → 1 / K ≤ |v 3 - v 2| →
        8 * K ^ 4 * κ < |eval x (pderiv 0 B - pderiv 1 A)| →
        ∃ last : Fin 2,
          volume {δ : Fin 4 → ℝ | δ ∈ Icc (fun _ => -q) (fun _ => q) ∧
            |eval δ (endpointMinor (brokenHeight A B x v) v (Fin.natAdd 2 last))| ≤
              (q * κ) * η ^ (4 * D) /
                (2 * C * (512 * ((D : ℝ) + 1)) ^ (4 * D))} <
                  ENNReal.ofReal (q ^ 4 * η) := by
  obtain ⟨C, hC, hsub⟩ := exists_symmetric_polynomial_sublevel_constant D
  refine ⟨C, hC, ?_⟩
  intro A B hA hB x v K q κ η hK hq hκ hη hη1 hv hI hJ hcurl
  obtain ⟨i, j, _, hj, hi⟩ := exists_large_minor_coefficient A B x v
    hK hκ.le hv hI hJ hcurl
  let last : Fin 2 := ⟨j.val - 2, by have := j.isLt; omega⟩
  have hlast : Fin.natAdd 2 last = j := by
    apply Fin.ext
    dsimp [last]
    omega
  refine ⟨last, ?_⟩
  rw [hlast]
  let P := endpointMinor (brokenHeight A B x v) v j
  have hP : P.totalDegree ≤ D :=
    (brokenHeight_minor_degree A B x v j).trans (max_le hA hB)
  have hlin : q * κ ≤ |(dilatePolynomial q P).coeff (Finsupp.single i 1)| := by
    rw [linear_coefficient_dilatePolynomial, abs_mul, abs_of_pos hq]
    exact mul_le_mul_of_nonneg_left hi.le hq.le
  exact scaled_sublevel_volume_lt hq P
    (hsub (dilatePolynomial q P) ((dilatePolynomial_degree q P).trans hP)
      i (q * κ) η (mul_pos hq hκ) hη hη1 hlin)

end Submission.Lib.K4ScalarSwitching.Switching
