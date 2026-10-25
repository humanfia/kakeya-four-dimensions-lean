import Submission.Obl.k4_homogeneous_native_pair_preparation.ClassLoss
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open Filter

/-- The output slack and the one-time mass retained after class selection. -/
noncomputable def preparedSlack (κ₀ n K : ℝ) : ℝ := 64 * (κ₀ * n) ^ 2 * K

noncomputable def retainedMass (κ₀ n : ℝ) : ℝ := (κ₀ * n)⁻¹

/-- All sample budgets reduce to five inequalities involving only real powers.
The old chart slack, class count and native bound may be any subpower quantities. -/
theorem preparation_numeric_bounds {N κ₀ n K τ ε a e c : ℝ}
    (hN : 1 ≤ N) (hκ₀ : 1 ≤ κ₀) (hn : 1 ≤ n) (hK : 1 ≤ K)
    (hκpow : κ₀ ≤ N ^ τ) (hnpow : n ≤ N ^ τ) (hKpow : K ≤ N ^ τ)
    (hslack : 64 * N ^ (5 * τ) ≤ N ^ ε)
    (hgeom : 192 * N ^ (τ + 2 * e) ≤ N ^ a)
    (hgood : 8 * N ^ (-c) ≤ N ^ (-4 * τ))
    (hder : 32 * N ^ (τ - a) ≤ N ^ (-4 * τ))
    (hfloor : 2 * N ^ (τ - a) ≤ 1) :
    1 ≤ preparedSlack κ₀ n K ∧ κ₀ ≤ preparedSlack κ₀ n K ∧
      K ≤ preparedSlack κ₀ n K ∧ preparedSlack κ₀ n K ≤ N ^ ε ∧
      0 < retainedMass κ₀ n ∧
      N ^ (-a) ≤ (1 / κ₀) / 2 ∧
      (∀ g : ℝ, 0 ≤ g → g ≤ 2 * N ^ e → 48 * κ₀ * g ^ 2 ≤ N ^ a) ∧
      2 * N ^ (-c) + 8 * κ₀ * N ^ (-a) ≤ (retainedMass κ₀ n) ^ 2 / 2 ∧
      16 ≤ preparedSlack κ₀ n K * (retainedMass κ₀ n) ^ 2 := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hκpos : 0 < κ₀ := zero_lt_one.trans_le hκ₀
  have hnpos : 0 < n := zero_lt_one.trans_le hn
  have hPpos : 0 < κ₀ * n := mul_pos hκpos hnpos
  have hPκ : κ₀ ≤ κ₀ * n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn hκpos.le
  have hPone : 1 ≤ κ₀ * n := hκ₀.trans hPκ
  have hPsq : κ₀ * n ≤ (κ₀ * n) ^ 2 := by
    simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hPone hPpos.le
  have hsqone : 1 ≤ (κ₀ * n) ^ 2 := hPone.trans hPsq
  have hsqs : (κ₀ * n) ^ 2 ≤ preparedSlack κ₀ n K := by
    dsimp [preparedSlack]
    have hm : 1 ≤ 64 * K := by linarith only [hK]
    simpa only [one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_right hm (sq_nonneg (κ₀ * n))
  have hKs : K ≤ preparedSlack κ₀ n K := by
    dsimp [preparedSlack]
    have hm : 1 ≤ 64 * (κ₀ * n) ^ 2 := by linarith only [hsqone]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (zero_le_one.trans hK)
  have hspow : preparedSlack κ₀ n K ≤ N ^ ε := by
    apply le_trans ?_ hslack
    calc
      preparedSlack κ₀ n K ≤ 64 * (N ^ τ * N ^ τ) ^ 2 * N ^ τ := by
        dsimp [preparedSlack]
        gcongr
      _ = 64 * N ^ (5 * τ) := by
        have heq : (N ^ τ * N ^ τ) ^ 2 * N ^ τ = N ^ (5 * τ) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
            ← Real.rpow_add hN0]
          congr 1
          ring
        calc
          _ = 64 * ((N ^ τ * N ^ τ) ^ 2 * N ^ τ) := by ring
          _ = _ := by rw [heq]
  have hPpow : κ₀ * n ≤ N ^ (2 * τ) := by
    calc
      κ₀ * n ≤ N ^ τ * N ^ τ := mul_le_mul hκpow hnpow hnpos.le (by positivity)
      _ = N ^ (2 * τ) := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hmasslo : N ^ (-4 * τ) ≤ (retainedMass κ₀ n) ^ 2 := by
    have hi : (N ^ (2 * τ))⁻¹ ≤ (κ₀ * n)⁻¹ :=
      (inv_le_inv₀ (by positivity) hPpos).mpr hPpow
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (N ^ (2 * τ))⁻¹) hi 2
    have heq : ((N ^ (2 * τ))⁻¹) ^ 2 = N ^ (-4 * τ) := by
      rw [← Real.rpow_neg hN0.le, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      ring
    simpa only [heq, retainedMass] using hs
  have hd : κ₀ * N ^ (-a) ≤ N ^ (τ - a) := by
    calc
      κ₀ * N ^ (-a) ≤ N ^ τ * N ^ (-a) :=
        mul_le_mul_of_nonneg_right hκpow (by positivity)
      _ = N ^ (τ - a) := by rw [← Real.rpow_add hN0, sub_eq_add_neg]
  refine ⟨hsqone.trans hsqs, hPκ.trans (hPsq.trans hsqs), hKs, hspow,
    inv_pos.mpr hPpos, ?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (le_div_iff₀ hκpos).mpr
    nlinarith only [hd, hfloor]
  · intro g hg hgu
    calc
      48 * κ₀ * g ^ 2 ≤ 48 * N ^ τ * (2 * N ^ e) ^ 2 := by gcongr
      _ = 192 * N ^ (τ + 2 * e) := by
        have hp : (N ^ e) ^ 2 = N ^ (2 * e) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          congr 1
          ring
        calc
          _ = 192 * (N ^ τ * (N ^ e) ^ 2) := by ring
          _ = _ := by rw [hp, ← Real.rpow_add hN0]
      _ ≤ _ := hgeom
  · nlinarith only [hgood, hder, hd, hmasslo]
  · have heq : preparedSlack κ₀ n K * (retainedMass κ₀ n) ^ 2 = 64 * K := by
      dsimp [preparedSlack, retainedMass]
      field_simp
    rw [heq]
    linarith only [hK]

/-- Choose the old slack so every fixed loss can be absorbed eventually.
The native loss is the universal constant eight. -/
theorem eventual_preparation_numerics (N : ℕ → ℝ)
    (hNt : Tendsto N atTop atTop) (M : ℕ)
    {ε e c gap : ℝ} (hε : 0 < ε) (he : 0 < e) (hc : 0 < c) (hgap : 0 < gap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ ε ∧ τ ≤ gap ∧
      ∀ᶠ k in atTop,
        (2 * (3 * (M : ℝ) + 1) * Real.logb 2 (N k) + 2) ^ 2 ≤ N k ^ τ ∧
        64 * N k ^ (5 * τ) ≤ N k ^ ε ∧
        192 * N k ^ (τ + 2 * e) ≤ N k ^ (8 * e) ∧
        8 * N k ^ (-c) ≤ N k ^ (-4 * τ) ∧
        32 * N k ^ (τ - 8 * e) ≤ N k ^ (-4 * τ) ∧
        2 * N k ^ (τ - 8 * e) ≤ 1 := by
  let τ := min (min ε e) (min c gap) / 16
  have hmin : 0 < min (min ε e) (min c gap) := lt_min (lt_min hε he) (lt_min hc hgap)
  have hτ : 0 < τ := div_pos hmin (by norm_num)
  have hτε : 16 * τ ≤ ε := by
    have := (min_le_left (min ε e) (min c gap)).trans (min_le_left ε e)
    dsimp [τ]
    linarith
  have hτe : 16 * τ ≤ e := by
    have := (min_le_left (min ε e) (min c gap)).trans (min_le_right ε e)
    dsimp [τ]
    linarith
  have hτc : 16 * τ ≤ c := by
    have := (min_le_right (min ε e) (min c gap)).trans (min_le_left c gap)
    dsimp [τ]
    linarith
  have hτg : 16 * τ ≤ gap := by
    have := (min_le_right (min ε e) (min c gap)).trans (min_le_right c gap)
    dsimp [τ]
    linarith
  obtain ⟨N₀, _, hclass⟩ := logarithmic_class_loss_subpower 2 (by positivity : 0 ≤ 3 * (M : ℝ) + 1) hτ
  have hclass' := (hNt.eventually_ge_atTop N₀).mono (fun k hk => hclass (N k) hk)
  have hs := hNt.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
    64 (by linarith : 5 * τ < ε))
  have hg := hNt.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
    192 (by linarith : τ + 2 * e < 8 * e))
  have hq := hNt.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
    8 (by linarith : -c < -4 * τ))
  have hd := hNt.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
    32 (by linarith : τ - 8 * e < -4 * τ))
  have hf := hNt.eventually (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
    2 (by linarith : τ - 8 * e < 0))
  refine ⟨τ, hτ, by linarith, by linarith, ?_⟩
  filter_upwards [hclass', hs, hg, hq, hd, hf] with k hk hs hg hq hd hf
  exact ⟨hk, hs, hg, hq, hd, by simpa only [Real.rpow_zero] using hf⟩

end Submission.Obl.k4_homogeneous_native_pair_preparation
