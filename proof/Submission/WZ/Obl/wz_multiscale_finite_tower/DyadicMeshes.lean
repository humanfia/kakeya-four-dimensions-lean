-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.DyadicMeshes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.NestedGrid

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

/-- Round arbitrary tower radii to commensurate grid widths. The error is only a
fixed factor, and every larger mesh is an integer multiple of every smaller one. -/
theorem dyadic_meshes {ι : Type*} {d : ℝ} (hd : 0 < d) (r : ι → ℝ)
    (hr : ∀ i, d ≤ r i) :
    ∃ a : ι → ℝ, (∀ i, 0 < a i ∧ r i / 8 ≤ a i ∧ a i ≤ r i / 4) ∧
      ∀ i j, r j ≤ r i → ∃ k : ℕ, 0 < k ∧ a i = (k : ℝ) * a j := by
  have hex (i : ι) := exists_nat_pow_near
    ((one_le_div hd).mpr (hr i)) (by norm_num : (1 : ℝ) < 2)
  choose m hm using hex
  let a : ι → ℝ := fun i => d / 4 * (2 : ℝ) ^ m i
  refine ⟨a, ?_, ?_⟩
  · intro i
    have hlo := (le_div_iff₀ hd).mp (hm i).1
    have hhi := (div_lt_iff₀ hd).mp (hm i).2
    rw [pow_succ] at hhi
    refine ⟨by dsimp [a]; positivity, ?_, ?_⟩ <;> dsimp [a] <;> nlinarith
  · intro i j hji
    have hp : (2 : ℝ) ^ m j < 2 ^ (m i + 1) :=
      ((hm j).1.trans (div_le_div_of_nonneg_right hji hd.le)).trans_lt (hm i).2
    have hmji : m j ≤ m i := by
      have hh := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hp
      omega
    refine ⟨2 ^ (m i - m j), pow_pos (by norm_num) _, ?_⟩
    have he : (2 : ℝ) ^ m i = (2 : ℝ) ^ (m i - m j) * 2 ^ m j := by
      rw [← pow_add, Nat.sub_add_cancel hmji]
    dsimp [a]
    rw [Nat.cast_pow, Nat.cast_ofNat, he]
    ring

end WangZahlLot.Obl.wz_multiscale_finite_tower
