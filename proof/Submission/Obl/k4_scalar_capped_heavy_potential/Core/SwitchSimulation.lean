/- Adapted (namespace renamed) from LOT tree oai_074 (this tree), obligation o062,
session x0511, branch x0511, commit f33e26edad,
Submission/Lib/K4ScalarCoreTools/Simulation/SwitchSimulation.lean (an unadmitted lib candidate).
Its own credits follow unchanged. -/

/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/SwitchSimulation.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 778c2ed,
Submission/Obl/k4_scalar_mesh_projection/SwitchSimulation.lean.
-/

import Submission.Obl.k4_scalar_capped_heavy_potential.Core.PolynomialVariation
import Submission.Obl.k4_scalar_capped_heavy_potential.Core.SwitchBaseError
import Submission.Lib.K4ScalarSwitching.SwitchPathError

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching

open Set MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching

/-- Sup norm control of the restored field justifies replacing its base
point and velocity by the simulated ones, with a uniform degree-only loss. -/
theorem exists_polynomial_row_perturbation_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ K : ℝ, 0 ≤ K →
        (∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z A| ≤ K ∧ |eval z B| ≤ K) →
        ∀ actual ∈ Icc (-1 : Fin 2 → ℝ) 1,
          ∀ simulated ∈ Icc (-1 : Fin 2 → ℝ) 1,
          ∀ r p w v derivative e : ℝ, 0 ≤ p →
            (∀ d, |simulated d - actual d| ≤ r) →
            |w| ≤ K → |w - v| ≤ p →
            |derivative - (eval actual A + w * eval actual B)| ≤ e →
            |derivative - (eval simulated A + v * eval simulated B)| ≤
              e + (1 + K) * (2 * C * K) * r + K * p := by
  obtain ⟨C, hC, hvar⟩ := exists_symmetric_square_variation_constant D
  refine ⟨C, hC, ?_⟩
  intro A B hA hB K hK hnorm actual ha simulated hs r p w v derivative e hp hdist hw hv hrow
  have hsum : |simulated 0 - actual 0| + |simulated 1 - actual 1| ≤ 2 * r := by
    linarith [hdist 0, hdist 1]
  have hfield (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ D)
      (hbound : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z P| ≤ K) :
      |eval actual P - eval simulated P| ≤ (2 * C * K) * r := by
    have h := hvar P hP K hK hbound actual ha simulated hs
    have h' : |eval simulated P - eval actual P| ≤ C * K * (2 * r) :=
      h.trans (mul_le_mul_of_nonneg_left hsum (mul_nonneg hC.le hK))
    rw [abs_sub_comm] at h'
    convert h' using 1
    ring
  exact scalar_field_row_perturbation derivative (eval actual A) (eval actual B)
    (eval simulated A) (eval simulated B) w v e (2 * C * K) r p K hK hp
    hrow (hfield A hA fun z hz => (hnorm z hz).1)
    (hfield B hB fun z hz => (hnorm z hz).2) hw hv (hnorm simulated hs).2

/-- The polynomial endpoint simulates all four actual line increments.
Base errors and velocity binning are charged before integrating the row
residual, and state-switch height discontinuities remain explicit. -/
theorem exists_switched_height_simulation_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ (x : Fin 2 → ℝ) (v w δ : Fin 4 → ℝ) (z : Fin 4 → Fin 2 → ℝ)
        (S : Fin 4 → Polynomial ℝ) (K q b p e r : ℝ),
        0 ≤ K → 0 ≤ b → 0 ≤ p → 0 ≤ e → 0 ≤ r →
        (∀ j, |δ j| ≤ q) → (∀ j, |w j| ≤ K) → (∀ j, |w j - v j| ≤ p) →
        (∀ u ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval u A| ≤ K ∧ |eval u B| ≤ K) →
        (∀ j, ∀ s ∈ uIcc (0 : ℝ) (δ j),
          (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s) ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
          (fun d => eval (Sum.elim δ (fun _ : Unit => s)) (legPoint x v j d)) ∈
            Icc (-1 : Fin 2 → ℝ) 1 ∧
          (∀ d, |eval (Sum.elim δ (fun _ : Unit => s)) (legPoint x v j d) -
            (z j d + ((![1, w j] : Fin 2 → ℝ) d) * s)| ≤ r) ∧
          |(S j).derivative.eval s -
            (eval (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s) A +
              w j * eval (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s) B)| ≤ e) →
        (∀ j : Fin 3, |(S j.succ).eval 0 - (S j.castSucc).eval (δ j.castSucc)| ≤ b) →
        |(S 3).eval (δ 3) - (S 0).eval 0 - eval δ (brokenHeight A B x v)| ≤
          4 * q * (e + (1 + K) * (2 * C * K) * r + K * p) + 3 * b := by
  obtain ⟨C, hC, hrow⟩ := exists_polynomial_row_perturbation_constant D
  refine ⟨C, hC, ?_⟩
  intro A B hA hB x v w δ z S K q b p e r hK hb hp he hr hδ hw hv hnorm hpath hswitch
  apply broken_height_error_with_switches A B x v δ S _ q b
    (by positivity) hδ _ hswitch
  intro j s hs
  obtain ⟨ha, hsim, hdist, hactual⟩ := hpath j s hs
  have h := hrow A B hA hB K hK hnorm _ ha _ hsim
    r p (w j) (v j) ((S j).derivative.eval s) e hp hdist (hw j) (hv j) hactual
  simpa only [legField, eval_substitution, map_add, map_mul, eval_C] using h

end Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching
