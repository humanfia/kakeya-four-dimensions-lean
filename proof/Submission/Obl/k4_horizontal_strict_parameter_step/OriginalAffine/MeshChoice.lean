/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/MeshChoice.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
/- Adapted from this LOT tree, obligation o202, session x0698, commit
   af82e6f9c71df56ed963f4a992dea84d0d6d83b5, file
   Submission/Obl/k4_horizontal_subcritical_rate_candidates/NativeMeshChoice.lean.
   The eighth slack power matches the unrestricted q^4/K^3 witness floor. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! A fixed fine mesh resolves the original true box and affine band. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

lemma native_fine_mesh_choice {N K a q g : ℝ} {H : ℕ}
    (hN : 2 ≤ N) (hK : 1 ≤ K) (ha : 0 < a) (hq : 0 < q)
    (hH : 0 < H) (hHlo : N ≤ (H : ℝ)) (hHhi : (H : ℝ) ≤ 2 * N)
    (hlarge : 69120 * K ^ 8 ≤ N) (hbase : a ≤ K * q) (hvolume : a ≤ K * q * g) :
    a / N ^ 2 ≤ q / H ∧
    (2 * K + 1) * (a / N ^ 2) ≤ 2 * K * q * g / H ∧
    24 * K ^ 4 * (a / N ^ 2) ≤ a ∧ 69120 * K ^ 8 ≤ (H : ℝ) := by
  have hN0 : 0 < N := by linarith
  have hH0 : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have hK0 : 0 ≤ K := by linarith
  have hK8 : K ≤ K ^ 8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show (1 : ℕ) ≤ 8 by norm_num)
  have hK48 : K ^ 4 ≤ K ^ 8 := pow_le_pow_right₀ hK (by norm_num)
  have hK81 : 1 ≤ K ^ 8 := one_le_pow₀ hK
  have hbaseN : 2 * K ≤ N := by linarith
  have hangleN : 2 * K + 1 ≤ N := by linarith
  have hfitN : 24 * K ^ 4 ≤ N ^ 2 := by
    have : 24 * K ^ 4 ≤ N := by linarith
    nlinarith
  have hprod : a / N ^ 2 * (H : ℝ) ≤ 2 * a / N := by
    calc
      _ = (a * H) / N ^ 2 := by ring
      _ ≤ (a * (2 * N)) / N ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hHhi ha.le) (sq_nonneg N)
      _ = _ := by field_simp
  have hmesh : a / N ^ 2 ≤ q / H := by
    apply (le_div_iff₀ hH0).mpr
    apply hprod.trans
    apply (div_le_iff₀ hN0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hbaseN hq.le]
  have hmesh' : (2 * K + 1) * (a / N ^ 2) ≤ 2 * K * q * g / H := by
    apply (le_div_iff₀ hH0).mpr
    calc
      _ = (2 * K + 1) * (a / N ^ 2 * H) := by ring
      _ ≤ (2 * K + 1) * (2 * a / N) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = ((2 * K + 1) * (2 * a)) / N := by ring
      _ ≤ 2 * a := (div_le_iff₀ hN0).mpr (by
        nlinarith [mul_le_mul_of_nonneg_left hangleN (by positivity : 0 ≤ 2 * a)])
      _ ≤ _ := by linarith
  have hfit : 24 * K ^ 4 * (a / N ^ 2) ≤ a := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hN0)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hfitN ha.le]
  exact ⟨hmesh, hmesh', hfit, hlarge.trans hHlo⟩

end Submission.Obl.k4_horizontal_strict_parameter_step
