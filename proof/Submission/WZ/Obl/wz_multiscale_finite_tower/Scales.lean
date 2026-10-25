-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Scales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

/-- A fixed multiplicative loss can be absorbed by an additional positive scale power. -/
theorem exists_scale_cutoff (c h D : ℝ) (hc : 0 < c) (hh : 0 < h) (hD : 0 < D) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ D ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ → d ^ h ≤ c := by
  refine ⟨min D (c ^ h⁻¹), lt_min hD (Real.rpow_pos_of_pos hc _), min_le_left _ _, ?_⟩
  intro d hd hdd
  calc
    d ^ h ≤ (c ^ h⁻¹) ^ h := Real.rpow_le_rpow hd.le (hdd.trans (min_le_right _ _)) hh.le
    _ = c := Real.rpow_inv_rpow hc.le hh.ne'

/-- The geometric mesh in the paper implies the frozen mesh once the scale is small enough. -/
theorem exists_mesh_cutoff {ω D : ℝ} (hω : ω ≤ 1) (hD : 0 < D) (q : ℕ) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ D ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      d ^ (2 * (1 - ω / 100) ^ q) ≤ (2 : ℝ) ^ (-(q : ℝ)) * d ^ ((1 - ω / 100) ^ q) := by
  have ha : 0 < (1 - ω / 100 : ℝ) := by linarith
  have hc : 0 < (2 : ℝ) ^ (-(q : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨d₀, hd₀, hd₀D, hsmall⟩ := exists_scale_cutoff _ _ D hc (pow_pos ha q) hD
  refine ⟨d₀, hd₀, hd₀D, ?_⟩
  intro d hd hdd
  have hpow := hsmall d hd hdd
  calc
    d ^ (2 * (1 - ω / 100) ^ q) = d ^ ((1 - ω / 100) ^ q) * d ^ ((1 - ω / 100) ^ q) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (-(q : ℝ)) * d ^ ((1 - ω / 100) ^ q) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hd.le _)

/-- One insertion reduces each logarithmic gap by the one-scale exponent. -/
theorem inserted_gap {d a t r s c : ℝ} {q : ℕ}
    (hd : 0 < d) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hold : c * d ^ (a ^ q) ≤ s / r)
    (hupper : (s / r) ^ a ≤ t / r)
    (hlower : (s / r) ^ a / 2 ≤ s / t) :
    c ^ a * d ^ (a ^ (q + 1)) ≤ t / r ∧
    c ^ a / 2 * d ^ (a ^ (q + 1)) ≤ s / t := by
  have hp : c ^ a * d ^ (a ^ (q + 1)) ≤ (s / r) ^ a := by
    calc
      _ = (c * d ^ (a ^ q)) ^ a := by
        rw [Real.mul_rpow hc (Real.rpow_nonneg hd.le _), ← Real.rpow_mul hd.le, pow_succ]
      _ ≤ (s / r) ^ a := Real.rpow_le_rpow (by positivity) hold ha
  constructor
  · exact hp.trans hupper
  · calc
      c ^ a / 2 * d ^ (a ^ (q + 1)) = (c ^ a * d ^ (a ^ (q + 1))) / 2 := by ring
      _ ≤ (s / r) ^ a / 2 := div_le_div_of_nonneg_right hp (by norm_num)
      _ ≤ s / t := hlower

/-- A dyadic loss remains sufficient through the sublinear exponent recurrence. -/
theorem dyadic_factor_succ {a : ℝ} (ha : a ≤ 1) (q : ℕ) :
    (2 : ℝ) ^ (-((q + 1 : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ (-(q : ℝ))) ^ a / 2 := by
  have hc : 0 < (2 : ℝ) ^ (-(q : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hc1 : (2 : ℝ) ^ (-(q : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (Nat.cast_nonneg q))
  have hca : (2 : ℝ) ^ (-(q : ℝ)) ≤ ((2 : ℝ) ^ (-(q : ℝ))) ^ a := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hc hc1 ha
  have heq : (2 : ℝ) ^ (-((q + 1 : ℕ) : ℝ)) = (2 : ℝ) ^ (-(q : ℝ)) / 2 := by
    rw [Nat.cast_add, Nat.cast_one, neg_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_neg_one]
    ring
  rw [heq]
  exact div_le_div_of_nonneg_right hca (by norm_num)

/-- The quantitative mesh recurrence used for a fixed finite number of insertions. -/
theorem dyadic_inserted_gap {d a t r s : ℝ} {q : ℕ}
    (hd : 0 < d) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hold : (2 : ℝ) ^ (-(q : ℝ)) * d ^ (a ^ q) ≤ s / r)
    (hupper : (s / r) ^ a ≤ t / r)
    (hlower : (s / r) ^ a / 2 ≤ s / t) :
    (2 : ℝ) ^ (-((q + 1 : ℕ) : ℝ)) * d ^ (a ^ (q + 1)) ≤ t / r ∧
    (2 : ℝ) ^ (-((q + 1 : ℕ) : ℝ)) * d ^ (a ^ (q + 1)) ≤ s / t := by
  have hc : 0 ≤ (2 : ℝ) ^ (-(q : ℝ)) := Real.rpow_nonneg (by norm_num) _
  obtain ⟨hu, hl⟩ := inserted_gap hd ha hc hold hupper hlower
  have hnext := dyadic_factor_succ ha1 q
  constructor
  · apply le_trans _ hu
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
    exact hnext.trans (by nlinarith [Real.rpow_nonneg hc a])
  · exact (mul_le_mul_of_nonneg_right hnext (Real.rpow_nonneg hd.le _)).trans hl

end WangZahlLot.Obl.wz_multiscale_finite_tower
