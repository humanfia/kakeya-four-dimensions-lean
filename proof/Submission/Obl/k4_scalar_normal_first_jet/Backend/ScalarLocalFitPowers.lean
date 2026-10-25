/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarLocalFitPowers.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarLocalFitPowers.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarLocalFitConstants
import Mathlib.Tactic.GCongr

/-! Polynomial losses in the local affine-fitting length and collision count. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable def scalarLocalFitErrorCount (K : ℝ) : ℕ := ⌈13 * K ^ 2⌉₊

theorem scalarLocalFitErrorCount_bounds {K : ℝ} (hK : 1 ≤ K) :
    2 + 8 * K + 2 * K ^ 2 ≤ (scalarLocalFitErrorCount K : ℝ) ∧
      (scalarLocalFitErrorCount K : ℝ) ≤ 14 * K ^ 2 := by
  have hlo := Nat.le_ceil (13 * K ^ 2)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 13 * K ^ 2 by positivity)
  have hKK : K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  constructor <;> dsimp only [scalarLocalFitErrorCount] <;> nlinarith

theorem scalar_local_fit_support_budget {K s : ℝ} (hK : 1 ≤ K) (hs : s ≤ 1) :
    (2 * (scalarLocalFitErrorCount K : ℝ) + 3) * K *
      (1 + 2 * (scalarLocalFitErrorCount K : ℝ)) ^ s ≤ 899 * K ^ 5 := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKK : 1 ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
  have hn := (scalarLocalFitErrorCount_bounds hK).2
  have h₁ : 2 * (scalarLocalFitErrorCount K : ℝ) + 3 ≤ 31 * K ^ 2 := by linarith
  have h₂ : 1 + 2 * (scalarLocalFitErrorCount K : ℝ) ≤ 29 * K ^ 2 := by linarith
  have hpow : (1 + 2 * (scalarLocalFitErrorCount K : ℝ)) ^ s ≤ 29 * K ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ 1 + 2 * (scalarLocalFitErrorCount K : ℝ) by
        have hn0 : (0 : ℝ) ≤ (scalarLocalFitErrorCount K : ℝ) := Nat.cast_nonneg _
        linarith) hs
    rw [Real.rpow_one] at h
    exact h.trans h₂
  calc
    _ ≤ (31 * K ^ 2) * K * (29 * K ^ 2) := by gcongr
    _ = _ := by ring

theorem scalar_pair_ceiling_power_bound {p K d : ℝ}
    (hp : 0 < p) (hK : 1 ≤ K) (hd : d ≤ 1) :
    scalarCollisionPairCeiling p K d K (1 + 2 * K) ≤ 529 * K ^ 6 * p ^ (2 + 2 * d) := by
  let A := 3 + 16 * K + 4 * K ^ 2
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg K]
  have hAupper : A ≤ 23 * K ^ 2 := by
    have hKK : K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
    dsimp [A]
    nlinarith
  have hApow : A ^ (1 + d) ≤ (23 * K ^ 2) ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hA1 (show 1 + d ≤ 2 by linarith)
    rw [Real.rpow_two] at h
    exact h.trans (pow_le_pow_left₀ hA0 hAupper 2)
  have heq : scalarCollisionPairCeiling p K d K (1 + 2 * K) =
      K ^ 2 * A ^ (1 + d) * p ^ (2 + 2 * d) := by
    have hbase : 2 * ((1 + 2 * K) + 6 * K + 2 * K ^ 2) + 1 = A := by dsimp [A]; ring
    have hpow : p ^ (2 + 2 * d) = p ^ (1 + d) * p ^ (1 + d) := by
      rw [← Real.rpow_add hp]
      congr 1
      ring
    unfold scalarCollisionPairCeiling
    rw [hbase, Real.mul_rpow hA0 hp.le, hpow]
    ring
  rw [heq]
  calc
    _ ≤ K ^ 2 * (23 * K ^ 2) ^ 2 * p ^ (2 + 2 * d) := by gcongr
    _ = _ := by ring

theorem scalar_normalized_collision_mass_lower {p K d : ℝ}
    (hp : 0 < p) (hK : 1 ≤ K) (hd : d ≤ 1) :
    p ^ (2 * d) / (36 * K ^ 6) ≤ scalarNormalizedCollisionMass p K d K⁻¹ := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hpd : p ^ d ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  have hKd : (2 * K) ^ d ≠ 0 := (Real.rpow_pos_of_pos (by positivity : 0 < 2 * K) _).ne'
  have hp2d : p ^ (2 * d) = (p ^ d) ^ 2 := by
    rw [show 2 * d = d * 2 by ring, Real.rpow_mul hp.le, Real.rpow_two]
  have hK2d : (2 * K) ^ (2 * d) = ((2 * K) ^ d) ^ 2 := by
    rw [show 2 * d = d * 2 by ring, Real.rpow_mul (by positivity : 0 ≤ 2 * K), Real.rpow_two]
  have heq : scalarNormalizedCollisionMass p K d K⁻¹ =
      p ^ (2 * d) / (9 * K ^ 4 * (2 * K) ^ (2 * d)) := by
    unfold scalarNormalizedCollisionMass
    rw [Real.div_rpow (by positivity : 0 ≤ 2 * K) hp.le, hp2d, hK2d]
    field_simp [hKpos.ne', hpd, hKd] <;> ring
  have hpow : (2 * K) ^ (2 * d) ≤ (2 * K) ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 2 * K by linarith)
      (show 2 * d ≤ 2 by linarith)
    simpa only [Real.rpow_two] using h
  have hden : 9 * K ^ 4 * (2 * K) ^ (2 * d) ≤ 36 * K ^ 6 := by
    calc
      _ ≤ 9 * K ^ 4 * (2 * K) ^ 2 := by gcongr
      _ = _ := by ring
  rw [heq]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hp.le _) (by positivity) hden

theorem scalar_normalized_active_length_lower {p K d : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 1 ≤ K) (hd : d ≤ 1) :
    p / (11426400 * K ^ 14) ≤ scalarNormalizedActiveLength p K d K K⁻¹ := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have he : 0 ≤ 1 + 2 * K := by linarith
  have hcapPos := scalarCollisionPairCeiling_pos (d := d) hp hK hKpos he
  have hcap := scalar_pair_ceiling_power_bound hp hK hd
  have hJ : 2 * K / p + 3 ≤ 5 * K / p := by
    have h := (one_le_div hp).mpr (hp1.trans hK)
    calc
      _ ≤ 2 * K / p + 3 * (K / p) := by linarith
      _ = _ := by ring
  have hT : 2 / p + 4 ≤ 6 / p := by
    have h := (one_le_div hp).mpr hp1
    calc
      _ ≤ 2 / p + 4 * (1 / p) := by linarith
      _ = _ := by ring
  have hQ : (2 * K / p + 3) ^ 2 * scalarCollisionPairCeiling p K d K (1 + 2 * K) ≤
      13225 * K ^ 8 * p ^ (2 * d) := by
    calc
      _ ≤ (5 * K / p) ^ 2 * (529 * K ^ 6 * p ^ (2 + 2 * d)) := by gcongr
      _ = _ := by
        rw [Real.rpow_add hp, Real.rpow_two]
        field_simp [hp.ne'] <;> ring
  have hden : 4 * ((2 * K / p + 3) ^ 2 * scalarCollisionPairCeiling p K d K (1 + 2 * K)) *
      (2 / p + 4) ≤ 317400 * K ^ 8 * p ^ (2 * d) / p := by
    calc
      _ ≤ 4 * (13225 * K ^ 8 * p ^ (2 * d)) * (6 / p) := by gcongr
      _ = _ := by ring
  have hM : 0 ≤ scalarNormalizedCollisionMass p K d K⁻¹ := by
    unfold scalarNormalizedCollisionMass
    positivity
  have hp2d : p ^ (2 * d) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
  unfold scalarNormalizedActiveLength
  calc
    _ = (p ^ (2 * d) / (36 * K ^ 6)) / (317400 * K ^ 8 * p ^ (2 * d) / p) := by
      field_simp [hp.ne', hKpos.ne', hp2d] <;> ring
    _ ≤ scalarNormalizedCollisionMass p K d K⁻¹ / (317400 * K ^ 8 * p ^ (2 * d) / p) :=
      div_le_div_of_nonneg_right (scalar_normalized_collision_mass_lower hp hK hd) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hM (by positivity) hden

theorem scalar_local_fit_density_budget {p K d η : ℝ}
    (hp : 0 < p) (hK : 1 ≤ K) (hd : d ≤ 1)
    (hsmall : 11000000000 * K ^ 15 * p ^ η ≤ 1) :
    4 * ((51 * K) ^ 3 * p ^ (η - 3)) *
      (scalarCollisionPairCeiling p K d K (1 + 2 * K) * p) ≤
        scalarNormalizedCollisionMass p K d K⁻¹ := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hcap := scalar_pair_ceiling_power_bound hp hK hd
  have hpow : p ^ (η - 3) * p ^ (2 + 2 * d) * p = p ^ (η + 2 * d) := by
    calc
      _ = (p ^ (η - 3) * p ^ (2 + 2 * d)) * p ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = p ^ (η - 3 + (2 + 2 * d) + 1) := by rw [← Real.rpow_add hp, ← Real.rpow_add hp]
      _ = _ := by congr 1; ring
  have hcoef : 36 * 280689516 * K ^ 15 * p ^ η ≤ 1 := by
    calc
      _ ≤ 11000000000 * K ^ 15 * p ^ η := by gcongr <;> norm_num
      _ ≤ 1 := hsmall
  calc
    _ ≤ 4 * ((51 * K) ^ 3 * p ^ (η - 3)) * (529 * K ^ 6 * p ^ (2 + 2 * d) * p) := by gcongr
    _ = 280689516 * K ^ 9 * p ^ (η + 2 * d) := by
      calc
        _ = 280689516 * K ^ 9 * (p ^ (η - 3) * p ^ (2 + 2 * d) * p) := by ring
        _ = _ := by rw [hpow]
    _ ≤ p ^ (2 * d) / (36 * K ^ 6) := by
      apply (le_div_iff₀ (by positivity : 0 < 36 * K ^ 6)).mpr
      calc
        _ = (36 * 280689516 * K ^ 15 * p ^ η) * p ^ (2 * d) := by
          rw [Real.rpow_add hp]
          ring
        _ ≤ 1 * p ^ (2 * d) := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hp.le _)
        _ = _ := one_mul _
    _ ≤ _ := scalar_normalized_collision_mass_lower hp hK hd

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
