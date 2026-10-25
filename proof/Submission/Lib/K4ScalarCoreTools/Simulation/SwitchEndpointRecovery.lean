/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/SwitchEndpointRecovery.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511,
Submission/Obl/k4_scalar_mesh_projection/SwitchEndpointRecovery.lean.
-/

import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchSimulation
import Submission.Lib.K4ScalarCoreTools.Simulation.SwitchSupport

namespace Submission.Lib.K4ScalarCoreTools.Simulation.Switching

open Set MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching

theorem last_leg_endpoint_eq (x : Fin 2 → ℝ) (v δ : Fin 4 → ℝ) (d : Fin 2) :
    eval (Sum.elim δ (fun _ : Unit => δ 3)) (legPoint x v 3 d) =
      switchedBaseEndpoint x v δ d := by
  rw [eval_legPoint]
  dsimp only [switchedBaseEndpoint]
  norm_num [Fin.sum_univ_succ]
  ring

/-- Actual switched trajectories lying in one physical support cell have
their exact polynomial simulated endpoint in an explicitly enlarged cell.
The witnesses need only exist pointwise; no measurable selection is used. -/
theorem exists_actual_endpoint_cover_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : MvPolynomial (Fin 2) ℝ),
      A.totalDegree ≤ D → B.totalDegree ≤ D →
      ∀ (x center : Fin 2 → ℝ) (v w δ : Fin 4 → ℝ) (z : Fin 4 → Fin 2 → ℝ)
        (S : Fin 4 → Polynomial ℝ) (K b p e ξ a X₀ c : ℝ),
        0 ≤ K → 0 ≤ b → 0 ≤ p → 0 ≤ e →
        (∀ j, |δ j| ≤ 1) → (∀ j, |w j| ≤ K) → (∀ j, |w j - v j| ≤ p) →
        (∀ u ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval u A| ≤ K ∧ |eval u B| ≤ K) →
        (∀ d, |z 0 d - x d| ≤ b) →
        (∀ j : Fin 3, ∀ d : Fin 2,
          |z j.succ d - (z j.castSucc d + ((![1, w j.castSucc] : Fin 2 → ℝ) d) * δ j.castSucc)| ≤ b) →
        (∀ j, ∀ s ∈ uIcc (0 : ℝ) (δ j),
          (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s) ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
          (fun d => eval (Sum.elim δ (fun _ : Unit => s)) (legPoint x v j d)) ∈
            Icc (-1 : Fin 2 → ℝ) 1 ∧
          |(S j).derivative.eval s -
            (eval (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s) A +
              w j * eval (fun d => z j d + ((![1, w j] : Fin 2 → ℝ) d) * s) B)| ≤ e) →
        (∀ j : Fin 3, |(S j.succ).eval 0 - (S j.castSucc).eval (δ j.castSucc)| ≤ b) →
        |(S 0).eval 0 - X₀| ≤ b →
        (∀ d, |z 3 d + ((![1, w 3] : Fin 2 → ℝ) d) * δ 3 - center d| ≤ ξ) →
        |(S 3).eval (δ 3) - c| ≤ a →
        switchedBaseEndpoint x v δ ∈
          Icc (fun d => center d - (ξ + (4 * b + 4 * p)))
            (fun d => center d + (ξ + (4 * b + 4 * p))) ∧
          |X₀ + eval δ (brokenHeight A B x v) - c| ≤
            a + (4 * (e + (1 + K) * (2 * C * K) * (4 * b + 4 * p) + K * p) + 3 * b) + b := by
  obtain ⟨C, hC, hsim⟩ := exists_switched_height_simulation_constant D
  refine ⟨C, hC, ?_⟩
  intro A B hA hB x center v w δ z S K b p e ξ a X₀ c hK hb hp he hδ hw hv
    hnorm hstart hbase hpath hswitch hheightStart hphysical hheight
  let r := 4 * b + 4 * p
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hbaseError (j : Fin 4) (d : Fin 2) (s : ℝ) (hs : |s| ≤ 1) :
      |eval (Sum.elim δ (fun _ : Unit => s)) (legPoint x v j d) -
        (z j d + ((![1, w j] : Fin 2 → ℝ) d) * s)| ≤ r := by
    have h := switched_base_error x v w δ z b p 1 hb hp hδ hv hstart hbase j d s hs
    simpa only [abs_sub_comm, mul_one, one_mul] using h
  have hsimError := hsim A B hA hB x v w δ z S K 1 b p e r hK hb hp he hr
    hδ hw hv hnorm (fun j s hs => by
      obtain ⟨ha, hb, hrow⟩ := hpath j s hs
      have hsabs : |s| ≤ 1 := abs_le.mpr
        ⟨(le_min (by norm_num) (abs_le.mp (hδ j)).1).trans hs.1,
          hs.2.trans (max_le (by norm_num) (abs_le.mp (hδ j)).2)⟩
      exact ⟨ha, hb, fun d => hbaseError j d s hsabs, hrow⟩) hswitch
  let H := 4 * (e + (1 + K) * (2 * C * K) * r + K * p) + 3 * b
  have hH : |(S 3).eval (δ 3) - (S 0).eval 0 - eval δ (brokenHeight A B x v)| ≤ H := by
    simpa only [one_mul, mul_one] using hsimError
  have hpredict : |X₀ + eval δ (brokenHeight A B x v) - (S 3).eval (δ 3)| ≤ H + b := by
    have h := abs_add_le (X₀ - (S 0).eval 0)
      (-((S 3).eval (δ 3) - (S 0).eval 0 - eval δ (brokenHeight A B x v)))
    have hid : X₀ - (S 0).eval 0 +
        (-((S 3).eval (δ 3) - (S 0).eval 0 - eval δ (brokenHeight A B x v))) =
          X₀ + eval δ (brokenHeight A B x v) - (S 3).eval (δ 3) := by ring
    rw [hid, abs_neg, abs_sub_comm X₀] at h
    linarith
  have h := simulated_endpoint_mem_enlarged_cell
    (fun d => z 3 d + ((![1, w 3] : Fin 2 → ℝ) d) * δ 3)
    (switchedBaseEndpoint x v δ) center ((S 3).eval (δ 3))
    (X₀ + eval δ (brokenHeight A B x v)) c ξ r a (H + b) hphysical
    (fun d => by simpa only [last_leg_endpoint_eq] using hbaseError 3 d (δ 3) (hδ 3))
    hheight hpredict
  refine ⟨h.1, h.2.trans_eq ?_⟩
  dsimp only [r, H]
  ring

end Submission.Lib.K4ScalarCoreTools.Simulation.Switching
