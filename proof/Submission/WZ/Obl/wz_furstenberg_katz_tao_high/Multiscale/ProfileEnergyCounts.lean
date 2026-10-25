-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.ProfileEnergyCounts.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

open scoped BigOperators

/-- Convert incidence, class/cell, and cap-energy counts into the stronger
profile-energy witness.  Here `I` is total incidence, `H` counts occupied
class/cell pairs, and `U` is the sum of squared class/cell degrees. -/
theorem profile_energy_witness_of_counts {ι : Type*}
    (S : Finset ι) (q : ι → ℝ) {B e Ga Fa Gh Fh I H U : ℝ}
    (hS : S.Nonempty) (hB : 1 < B) (hU0 : 0 ≤ U)
    (hcard : (S.card : ℝ) ≤ B ^ e)
    (hI : B ^ (Ga + Fa - e) ≤ I)
    (hCS : I ^ 2 ≤ H * U)
    (hH : H ≤ B ^ (2 * Fa + Gh - Fh + e))
    (hU : U ≤ B ^ (2 * Ga + Fa + e) * ∑ y ∈ S, B ^ (-q y)) :
    ∃ y ∈ S, q y ≤ Fa + Gh - Fh + 5 * e := by
  classical
  have hB0 : 0 < B := zero_lt_one.trans hB
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image S q hS
  have hsum : ∑ z ∈ S, B ^ (-q z) ≤ B ^ (e - q y) := by
    calc
      ∑ z ∈ S, B ^ (-q z) ≤ ∑ _z ∈ S, B ^ (-q y) := by
        apply Finset.sum_le_sum
        intro z hz
        exact Real.rpow_le_rpow_of_exponent_le hB.le (neg_le_neg (hmin z hz))
      _ = (S.card : ℝ) * B ^ (-q y) := by simp
      _ ≤ B ^ e * B ^ (-q y) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hB0.le _)
      _ = B ^ (e - q y) := by
        simpa only [sub_eq_add_neg] using (Real.rpow_add hB0 e (-q y)).symm
  have hU' : U ≤ B ^ (2 * Ga + Fa + e) * B ^ (e - q y) :=
    hU.trans (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hB0.le _))
  have hpow : (B ^ (Ga + Fa - e)) ^ (2 : ℕ) ≤
      B ^ ((2 * Fa + Gh - Fh + e) + (2 * Ga + Fa + e) + (e - q y)) := by
    calc
      (B ^ (Ga + Fa - e)) ^ (2 : ℕ) ≤ I ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hB0.le _) hI 2
      _ ≤ H * U := hCS
      _ ≤ B ^ (2 * Fa + Gh - Fh + e) *
          (B ^ (2 * Ga + Fa + e) * B ^ (e - q y)) :=
        mul_le_mul hH hU' hU0 (Real.rpow_nonneg hB0.le _)
      _ = B ^ ((2 * Fa + Gh - Fh + e) + (2 * Ga + Fa + e) + (e - q y)) := by
        rw [← Real.rpow_add hB0, ← Real.rpow_add hB0]
        congr 1
        ring
  rw [← Real.rpow_mul_natCast hB0.le (Ga + Fa - e) 2] at hpow
  have hexp := (Real.rpow_le_rpow_left_iff hB).mp hpow
  refine ⟨y, hy, ?_⟩
  norm_num only [Nat.cast_ofNat] at hexp
  linarith

/-- The cutoff-free tube-pruning inequality also yields the strong energy
premise. `Ga` may be the mass exponent of the original fine pins. -/
theorem profile_energy_witness_of_cubic_errors {ι : Type*}
    (S : Finset ι) (q : ι → ℝ) {B e eU Ga Fa Gh Fh I W E J U : ℝ}
    (hS : S.Nonempty) (hB : 1 < B)
    (hW0 : 0 ≤ W) (hE0 : 0 ≤ E) (hJ0 : 0 ≤ J) (hU0 : 0 ≤ U)
    (hcard : (S.card : ℝ) ≤ B ^ e) (h8 : 8 ≤ B ^ e)
    (hI : B ^ (Ga + Fa - e) ≤ I)
    (hcubic : I ^ 3 ≤ 8 * W * E * J * U)
    (hW : W ≤ B ^ (Ga - Gh + Fa - Fh + e))
    (hE : E ≤ B ^ (2 * Gh + e))
    (hJ : J ≤ B ^ (2 * Fa + e))
    (hU : U ≤ B ^ (2 * Ga + Fa + eU) * ∑ y ∈ S, B ^ (-q y)) :
    ∃ y ∈ S, q y ≤ Fa + Gh - Fh + 8 * e + eU := by
  classical
  have hB0 : 0 < B := zero_lt_one.trans hB
  obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image S q hS
  have hsum : ∑ z ∈ S, B ^ (-q z) ≤ B ^ (e - q y) := by
    calc
      ∑ z ∈ S, B ^ (-q z) ≤ ∑ _z ∈ S, B ^ (-q y) := by
        apply Finset.sum_le_sum
        intro z hz
        exact Real.rpow_le_rpow_of_exponent_le hB.le (neg_le_neg (hmin z hz))
      _ = (S.card : ℝ) * B ^ (-q y) := by simp
      _ ≤ B ^ e * B ^ (-q y) :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hB0.le _)
      _ = B ^ (e - q y) := by
        simpa only [sub_eq_add_neg] using (Real.rpow_add hB0 e (-q y)).symm
  have hU' : U ≤ B ^ (2 * Ga + Fa + eU) * B ^ (e - q y) :=
    hU.trans (mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hB0.le _))
  have hpow : (B ^ (Ga + Fa - e)) ^ (3 : ℕ) ≤
      B ^ (3 * Ga + 4 * Fa + Gh - Fh + 5 * e + eU - q y) := by
    calc
      (B ^ (Ga + Fa - e)) ^ (3 : ℕ) ≤ I ^ 3 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hB0.le _) hI 3
      _ ≤ 8 * W * E * J * U := hcubic
      _ ≤ B ^ e * B ^ (Ga - Gh + Fa - Fh + e) * B ^ (2 * Gh + e) *
          B ^ (2 * Fa + e) * (B ^ (2 * Ga + Fa + eU) * B ^ (e - q y)) := by
        gcongr
      _ = B ^ (3 * Ga + 4 * Fa + Gh - Fh + 5 * e + eU - q y) := by
        repeat rw [← Real.rpow_add hB0]
        congr 1
        ring
  rw [← Real.rpow_mul_natCast hB0.le (Ga + Fa - e) 3] at hpow
  have hexp := (Real.rpow_le_rpow_left_iff hB).mp hpow
  refine ⟨y, hy, ?_⟩
  norm_num only [Nat.cast_ofNat] at hexp
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
