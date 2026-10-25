import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.NativeMesh
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.CountMesh

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_critical_derivative_evaluation_lists

namespace NativeModel

variable {α : Type} [MeasurableSpace α] (cfg : NativeModel α)

/-- The same fixed physical mesh used for original affine comparison resolves
the whole contact box used by the child count. -/
theorem original_count_mesh_resolves {k : ℕ} {s p v m : ℝ}
    (a : cfg.AssignmentLevel k s) (hN : 2 ≤ cfg.N k) (hK : 1 ≤ cfg.K k)
    (hℓ : cfg.ℓ = cfg.κ) (hκ : 0 ≤ cfg.κ) (hκ1 : 2 * cfg.κ ≤ 1) (hs : 0 ≤ s)
    (hlarge : 69120 * cfg.K k ^ 8 ≤ cfg.N k)
    (hp : |p| ≤ 3 * cfg.K k) (hv : |v| ≤ cfg.K k ^ 2) (hm : |m| ≤ 1) :
    cfg.N k ^ (-(s + 2)) ≤ cfg.timeLength k s / 2 ∧
    (|v| + 1) * cfg.N k ^ (-(s + 2)) ≤ 8 * cfg.K k ^ 2 * cfg.timeLength k s ∧
    (|-p - m * v| + |m| + 1) * cfg.N k ^ (-(s + 2)) ≤
      32 * cfg.K k ^ 4 * cfg.timeLength k s ^ 2 ∧
    24 * cfg.K k ^ 4 * cfg.N k ^ (-(s + 2)) ≤ cfg.N k ^ (-s) := by
  have hNp : 0 < cfg.N k := by linarith
  have hN1 : 1 ≤ cfg.N k := by linarith
  have hKp : 0 < cfg.K k := zero_lt_one.trans_le hK
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hη : 0 < cfg.N k ^ (-(s + 2)) := Real.rpow_pos_of_pos hNp _
  obtain ⟨hH, hmesh, _, hfit, _⟩ :=
    cfg.original_affine_mesh_resolves a hN hK hℓ hκ hκ1 hs hlarge
  have hH₂ : (2 : ℝ) ≤ ⌈cfg.N k⌉₊ := hN.trans (Nat.le_ceil _)
  have hmesh₀ : cfg.N k ^ (-(s + 2)) ≤ cfg.timeLength k s / 2 :=
    hmesh.trans (div_le_div_of_nonneg_left hq.le (by norm_num) hH₂)
  have hK₈ : cfg.K k ≤ cfg.K k ^ 8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show (1 : ℕ) ≤ 8 by norm_num)
  have hKN : cfg.K k ≤ cfg.N k := by
    have hk8 : 1 ≤ cfg.K k ^ 8 := one_le_pow₀ hK
    linarith
  have hsquare : cfg.N k ^ (-s) ≤ cfg.K k ^ 2 * cfg.timeLength k s ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hq)).mp (cfg.hidden_time_ratios a hN1 hKp hκ hκ1 hs).2
  have hmesh₂ : cfg.N k ^ (-(s + 2)) ≤ cfg.timeLength k s ^ 2 := by
    rw [original_affine_mesh_identity hNp]
    apply (div_le_iff₀ (sq_pos_of_pos hNp)).mpr
    calc
      _ ≤ cfg.K k ^ 2 * cfg.timeLength k s ^ 2 := hsquare
      _ ≤ cfg.N k ^ 2 * cfg.timeLength k s ^ 2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hKp.le hKN 2) (sq_nonneg _)
      _ = _ := mul_comm _ _
  have hb := count_mesh_of_square_floor hK hq.le hη.le hmesh₀ hmesh₂ hp hv hm
  exact ⟨hmesh₀, hb.1, hb.2, hfit⟩

end NativeModel

end Submission.Obl.k4_horizontal_strict_parameter_step
