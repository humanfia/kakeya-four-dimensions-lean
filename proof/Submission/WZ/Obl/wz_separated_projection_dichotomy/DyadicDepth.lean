-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.DyadicDepth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Basic

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Filter
open scoped Topology

noncomputable def dyadicRadius (n : ℕ) : ℝ := 32 * (1 / 2 : ℝ) ^ n

theorem dyadicRadius_pos (n : ℕ) : 0 < dyadicRadius n := by unfold dyadicRadius; positivity

theorem dyadicRadius_antitone : Antitone dyadicRadius := by
  intro n m hnm
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hnm) (by norm_num)

theorem exists_dyadic_depth_budget {p : ℝ} (hp : 0 < p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ n : ℕ, δ ≤ dyadicRadius n ∧ dyadicRadius (n + 1) < δ ∧
        ((n + 1 : ℕ) : ℝ) * δ ^ p ≤ 1 := by
  have hpow : Tendsto (fun δ : ℝ => δ ^ p) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hp.ne'] using
      (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).continuousWithinAt.tendsto
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero hp
  have hlimit : Tendsto (fun δ : ℝ => ((Real.log 32 - Real.log δ) / Real.log 2 + 1) * δ ^ p)
      (𝓝[>] 0) (𝓝 0) := by
    convert (hpow.const_mul (Real.log 32 / Real.log 2 + 1)).sub (hlog.div_const (Real.log 2)) using 1
    · funext δ
      ring
    · simp
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ((Real.log 32 - Real.log δ) / Real.log 2 + 1) * δ ^ p < 1 :=
    (tendsto_order.1 hlimit).2 1 zero_lt_one
  obtain ⟨δ₁, hδ₁, hbudget⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hevent
  refine ⟨min δ₁ 1, lt_min hδ₁ zero_lt_one, min_le_right _ _, ?_⟩
  intro δ hδ hsmall
  have hδ1 : δ ≤ 1 := hsmall.trans (min_le_right _ _)
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one
    (by positivity : 0 < δ / 32) (by linarith : δ / 32 ≤ 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hleft : δ ≤ dyadicRadius n := by dsimp [dyadicRadius]; linarith
  have hright : dyadicRadius (n + 1) < δ := by dsimp [dyadicRadius]; linarith
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  have hlogs := Real.log_le_log hδ hleft
  rw [dyadicRadius, Real.log_mul (by norm_num) (by positivity), Real.log_pow, hloghalf] at hlogs
  have hn_bound : (n : ℝ) ≤ (Real.log 32 - Real.log δ) / Real.log 2 := by
    apply (le_div_iff₀ hlogtwo).mpr
    nlinarith
  refine ⟨n, hleft, hright, ?_⟩
  have hbud := hbudget ⟨hδ, hsmall.trans (min_le_left _ _)⟩
  calc ((n + 1 : ℕ) : ℝ) * δ ^ p ≤
        ((Real.log 32 - Real.log δ) / Real.log 2 + 1) * δ ^ p := by
        gcongr
        push_cast
        linarith
    _ ≤ 1 := hbud.le

/-- The finite dyadic family down to `δ` resolves every radius between
`δ` and the fixed upper scale. -/
theorem dyadicRadius_cover {δ r : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hlast : dyadicRadius (n + 1) < δ) (hδr : δ ≤ r) (hr : r ≤ 32) :
    ∃ k ∈ Finset.range (n + 1), r ≤ dyadicRadius k ∧ dyadicRadius k < 2 * r := by
  have hrpos := hδ.trans_le hδr
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near_of_lt_one
    (by positivity : 0 < r / 32) (by linarith : r / 32 ≤ 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hkr : r ≤ dyadicRadius k := by dsimp [dyadicRadius]; linarith
  have hk2 : dyadicRadius k < 2 * r := by
    rw [pow_succ] at hk
    dsimp [dyadicRadius]
    linarith
  have hkn : k < n + 1 := by
    by_contra h
    have hh := dyadicRadius_antitone (le_of_not_gt h)
    linarith
  exact ⟨k, Finset.mem_range.mpr hkn, hkr, hk2⟩

end WangZahlLot.Obl.wz_separated_projection_dichotomy
