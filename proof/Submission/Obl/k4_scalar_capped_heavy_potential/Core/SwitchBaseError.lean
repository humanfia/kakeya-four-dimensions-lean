/- Adapted (namespace renamed) from LOT tree oai_074 (this tree), obligation o062,
session x0511, branch x0511, commit f33e26edad,
Submission/Lib/K4ScalarCoreTools/Simulation/SwitchBaseError.lean (an unadmitted lib candidate).
Its own credits follow unchanged. -/

/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/SwitchBaseError.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 778c2ed,
Submission/Obl/k4_scalar_mesh_projection/SwitchBaseError.lean.
-/

import Submission.Lib.K4ScalarSwitching.SwitchPath

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching

open Set MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching

/-- Binning the velocities and switching between nearby physical states
changes every simulated base point by a controlled error. Both orientations
of each increment are permitted. -/
theorem switched_base_error (x : Fin 2 → ℝ) (v w δ : Fin 4 → ℝ)
    (z : Fin 4 → Fin 2 → ℝ) (b p q : ℝ) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hδ : ∀ j, |δ j| ≤ q) (hvw : ∀ j, |w j - v j| ≤ p)
    (hstart : ∀ d, |z 0 d - x d| ≤ b)
    (hswitch : ∀ j : Fin 3, ∀ d : Fin 2,
      |z j.succ d - (z j.castSucc d + ((![1, w j.castSucc] : Fin 2 → ℝ) d) * δ j.castSucc)| ≤ b)
    (j : Fin 4) (d : Fin 2) (s : ℝ) (hs : |s| ≤ q) :
    |z j d + ((![1, w j] : Fin 2 → ℝ) d) * s -
      eval (Sum.elim δ (fun _ : Unit => s)) (legPoint x v j d)| ≤ 4 * b + 4 * q * p := by
  let gap : Fin 3 → ℝ := fun k =>
    z k.succ d - (z k.castSucc d + ((![1, w k.castSucc] : Fin 2 → ℝ) d) * δ k.castSucc)
  let diff : Fin 4 → ℝ := fun k =>
    ((![1, w k] : Fin 2 → ℝ) d) - ((![1, v k] : Fin 2 → ℝ) d)
  let g : ℝ := ∑ k : Fin 3, if k.val < j.val then gap k else 0
  let r : ℝ := ∑ k : Fin 3, if k.val < j.val then diff k.castSucc * δ k.castSucc else 0
  have hd (k : Fin 4) : |diff k| ≤ p := by
    dsimp only [diff]
    fin_cases d
    · simpa using hp
    · simpa using hvw k
  have hq : 0 ≤ q := (abs_nonneg (δ 0)).trans (hδ 0)
  have hprod (k : Fin 4) : |diff k * δ k| ≤ q * p := by
    rw [abs_mul]
    exact (mul_le_mul (hd k) (hδ k) (abs_nonneg _) hp).trans_eq (mul_comm _ _)
  have hg : |g| ≤ 3 * b := by
    calc
      _ ≤ ∑ k : Fin 3, |if k.val < j.val then gap k else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 3, b := Finset.sum_le_sum fun k _ => by
        split_ifs
        · exact hswitch k d
        · simpa using hb
      _ = 3 * b := by simp
  have hr : |r| ≤ 3 * (q * p) := by
    calc
      _ ≤ ∑ k : Fin 3, |if k.val < j.val then diff k.castSucc * δ k.castSucc else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 3, q * p := Finset.sum_le_sum fun k _ => by
        split_ifs
        · exact hprod k.castSucc
        · simpa using mul_nonneg hq hp
      _ = 3 * (q * p) := by simp
  have hlast : |diff j * s| ≤ q * p := by
    rw [abs_mul]
    exact (mul_le_mul (hd j) hs (abs_nonneg _) hp).trans_eq (mul_comm _ _)
  have hid : z j d + ((![1, w j] : Fin 2 → ℝ) d) * s -
      eval (Sum.elim δ (fun _ : Unit => s)) (legPoint x v j d) =
        (z 0 d - x d) + g + r + diff j * s := by
    rw [eval_legPoint]
    dsimp only [g, r, gap, diff]
    fin_cases j <;> norm_num [Fin.sum_univ_succ] <;> ring
  rw [hid]
  have h₁ := abs_add_le ((z 0 d - x d) + g + r) (diff j * s)
  have h₂ := abs_add_le ((z 0 d - x d) + g) r
  have h₃ := abs_add_le (z 0 d - x d) g
  linarith [hstart d]

/-- Moving a controlled row residual to a nearby base point and a binned
velocity adds only the field variation and velocity-bin errors. -/
theorem scalar_field_row_perturbation (derivative A₀ B₀ A₁ B₁ w v E L r p K : ℝ)
    (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hrow : |derivative - (A₀ + w * B₀)| ≤ E)
    (hA : |A₀ - A₁| ≤ L * r) (hB : |B₀ - B₁| ≤ L * r)
    (hw : |w| ≤ K) (hv : |w - v| ≤ p) (hB₁ : |B₁| ≤ K) :
    |derivative - (A₁ + v * B₁)| ≤ E + (1 + K) * L * r + K * p := by
  have hid : derivative - (A₁ + v * B₁) =
      (derivative - (A₀ + w * B₀)) + (A₀ - A₁) +
        w * (B₀ - B₁) + (w - v) * B₁ := by ring
  rw [hid]
  have h₁ := abs_add_le
    ((derivative - (A₀ + w * B₀)) + (A₀ - A₁) + w * (B₀ - B₁)) ((w - v) * B₁)
  have h₂ := abs_add_le ((derivative - (A₀ + w * B₀)) + (A₀ - A₁)) (w * (B₀ - B₁))
  have h₃ := abs_add_le (derivative - (A₀ + w * B₀)) (A₀ - A₁)
  have h₄ : |w * (B₀ - B₁)| ≤ K * (L * r) := by
    rw [abs_mul]
    exact mul_le_mul hw hB (abs_nonneg _) hK
  have h₅ : |(w - v) * B₁| ≤ p * K := by
    rw [abs_mul]
    exact mul_le_mul hv hB₁ (abs_nonneg _) hp
  nlinarith

end Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching
