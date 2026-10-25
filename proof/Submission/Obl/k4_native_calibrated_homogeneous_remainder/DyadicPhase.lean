import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CompHomog
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.RawDensities
import Submission.Obl.k4_crop_angular_finite_tail.Grid

/-! The encoding's intrinsic hidden phase refines the required dyadic bins
by at most a factor of two. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion

theorem intrinsic_phase_factor {N ρ s : ℝ} (hN : 1 ≤ N) (hρ : 0 ≤ ρ) (hs : 0 ≤ s) :
    ∃ d : ℕ, d ≤ 1 ∧ δ N s = (2 : ℝ) ^ d * Comp.theta N ρ s := by
  obtain ⟨d, hd, -, hprod⟩ :=
    Submission.Obl.k4_crop_angular_finite_tail.width_product hN hρ hs
  refine ⟨d, hd, ?_⟩
  change Comp.dl N s = (2 : ℝ) ^ d * Comp.theta N ρ s
  change Comp.dl N ρ * Comp.dl N s = (2 : ℝ) ^ d * Comp.dl N (ρ + s) at hprod
  unfold Comp.theta
  rw [← mul_div_assoc]
  exact (eq_div_iff (Comp.dl_pos N ρ).ne').mpr (by simpa only [mul_comm] using hprod)

theorem floor_scale_nat {a : ℝ} (ha : a ≠ 0) (n : ℕ) (x : ℝ) :
    ⌊x / ((n : ℝ) * a)⌋ = ⌊x / a⌋ / (n : ℤ) := by
  rw [show x / ((n : ℝ) * a) = (x / a) / n by ring]
  exact Int.floor_div_natCast _ _

theorem pure_obs_coarsening {N ρ s : ℝ} {d : ℕ}
    (hd : δ N s = (2 : ℝ) ^ d * Comp.theta N ρ s) (B : ℝ) (z : Incidence) :
    obs B (δ N s) z =
      ((obs B (Comp.theta N ρ s) z).1,
        (obs B (Comp.theta N ρ s) z).2 / (2 : ℤ) ^ d) := by
  apply Prod.ext
  · rfl
  change ⌊B * x z.1 z.2 3 / δ N s⌋ =
    ⌊B * x z.1 z.2 3 / Comp.theta N ρ s⌋ / (2 : ℤ) ^ d
  rw [hd]
  have hf := floor_scale_nat (Comp.theta_pos N ρ s).ne' (2 ^ d) (B * x z.1 z.2 3)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hf

/-- A coarsening by a factor of one or two has at most two children. -/
theorem count_int_div_two_pow_le {d : ℕ} (hd : d ≤ 1) (c : ℤ) :
    Measure.count {b : ℤ | b / (2 : ℤ) ^ d = c} ≤ (2 : ENNReal) := by
  classical
  let L : Finset ℤ := Finset.Ico ((2 : ℤ)^d * c) ((2 : ℤ)^d * (c + 1))
  have heq : {b : ℤ | b / (2 : ℤ)^d = c} = (L : Set ℤ) := by
    ext b
    simp only [L, Finset.mem_coe, Finset.mem_Ico, mem_setOf_eq]
    have hpow : 0 < (2 : ℤ)^d := by positivity
    constructor
    · intro hb
      constructor
      · have := (Int.le_ediv_iff_mul_le hpow).mp hb.ge
        simpa only [mul_comm] using this
      · have := (Int.ediv_lt_iff_lt_mul hpow).mp (show b / (2 : ℤ)^d < c + 1 by omega)
        simpa only [mul_comm] using this
    · intro hb
      have hle := (Int.le_ediv_iff_mul_le hpow).mpr (by simpa only [mul_comm] using hb.1)
      have hlt := (Int.ediv_lt_iff_lt_mul hpow).mpr (by simpa only [mul_comm] using hb.2)
      omega
  rw [heq, Measure.count_apply_finset]
  have hc : L.card = 2 ^ d := by
    simp only [L, Int.card_Ico]
    rw [show (2 : ℤ)^d * (c + 1) - (2 : ℤ)^d * c = (2 : ℤ)^d by ring]
    norm_cast
  rw [hc]
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> norm_num

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
