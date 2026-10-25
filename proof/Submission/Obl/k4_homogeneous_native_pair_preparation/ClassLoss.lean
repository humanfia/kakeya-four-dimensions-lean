-- Adapted from this LOT tree, o114, session x0680, commit 8cc890dd,
-- Submission/Obl/k4_terminal_representative_atlas/Preparation/ClassLoss.lean.
import Submission.Lib.K4Homogenization.DensitySelection

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

/-- Polynomially many logarithmic scale classes cost an arbitrarily small
power, uniformly once the sample resolution exceeds a real threshold. This
uses the accepted simultaneous density-class count. -/
theorem logarithmic_class_loss_subpower (k : ℕ) {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (2 * a * Real.logb 2 N + 2) ^ k ≤ N ^ ε := by
  obtain ⟨N₀, hN₀, hbound⟩ :=
    Submission.Lib.K4Homogenization.dyadic_density_loss_subpower k
      (by linarith : 0 < a + 1) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := hN₀.trans hN
  have hN0 : 0 < N := by linarith
  have hlog : 1 ≤ Real.logb 2 N := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (0 : ℝ) < 2) hN2
  have hid : Real.logb 2 (N ^ (a + 1) / N ^ (-(a + 1))) =
      2 * (a + 1) * Real.logb 2 N := by
    rw [Real.logb_div (Real.rpow_pos_of_pos hN0 _).ne'
      (Real.rpow_pos_of_pos hN0 _).ne',
      Real.logb_rpow_eq_mul_logb_of_pos hN0,
      Real.logb_rpow_eq_mul_logb_of_pos hN0]
    ring
  have hcompare : 2 * a * Real.logb 2 N + 2 ≤
      ((WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyExp
        (N ^ (a + 1)) (N ^ (-(a + 1))) + 1 : ℕ) : ℝ) := by
    unfold WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyExp
    push_cast
    rw [hid]
    have hf := Nat.lt_floor_add_one (2 * (a + 1) * Real.logb 2 N)
    linarith
  calc
    _ ≤ (((WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale.dyExp
        (N ^ (a + 1)) (N ^ (-(a + 1))) + 1) ^ k : ℕ) : ℝ) := by
      push_cast
      simpa only [Nat.cast_add, Nat.cast_one] using
        pow_le_pow_left₀ (by positivity) hcompare k
    _ ≤ N ^ ε := hbound N hN

end Submission.Obl.k4_homogeneous_native_pair_preparation
