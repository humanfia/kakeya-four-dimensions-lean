-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.TransferGrid, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/TransferGrid.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 40b071c3e1be70138434c7f18ff663f9c27a6dfa,
Submission/Obl/k4_staged_weak_breadth_discovery/TransferGrid.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/TransferGrid.lean.
-- Existing source attributions are preserved below.

import Mathlib

/-!
# Uniform grids with reserve for transferring an anisotropic candidate

This file supplies only scale choices. It does not supply the geometric
candidate or a bound on compatible finer packet capacities.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

/-- The positive uniform grid ending at one. -/
noncomputable def transferScale (m i : ℕ) : ℝ := ((i : ℝ) + 1) / m

theorem transferScale_last {m : ℕ} (hm : 0 < m) :
    transferScale m (m - 1) = 1 := by
  unfold transferScale
  rw [Nat.cast_sub (by omega : 1 ≤ m)]
  simp only [Nat.cast_one, sub_add_cancel]
  exact div_self (by positivity)

theorem transferScale_valid {m : ℕ} (hm : 0 < m) :
    0 < m ∧ 0 < transferScale m 0 ∧
      (∀ i, i + 1 < m → transferScale m i < transferScale m (i + 1)) ∧
      transferScale m (m - 1) = 1 := by
  refine ⟨hm, by unfold transferScale; positivity, ?_, transferScale_last hm⟩
  intro i _
  unfold transferScale
  apply (div_lt_div_iff_of_pos_right (by positivity : 0 < (m : ℝ))).mpr
  push_cast
  linarith

theorem transferScale_le_iff {m i j : ℕ} (hm : 0 < m) :
    transferScale m i ≤ transferScale m j ↔ i ≤ j := by
  unfold transferScale
  rw [div_le_div_iff_of_pos_right (by positivity : 0 < (m : ℝ)),
    add_le_add_iff_right]
  exact Nat.cast_le

/-- Round a target up to a grid point, with an error smaller than one mesh. -/
theorem exists_transferScale_above {m : ℕ} (hm : 0 < m) {target : ℝ}
    (hlo : transferScale m 0 ≤ target) (hhi : target ≤ 1) :
    ∃ j < m, target ≤ transferScale m j ∧
      transferScale m j < target + 1 / (m : ℝ) := by
  classical
  have hex : ∃ j, j < m ∧ target ≤ transferScale m j :=
    ⟨m - 1, by omega, by rw [transferScale_last hm]; exact hhi⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  change j < m ∧ target ≤ transferScale m j at hj
  refine ⟨j, hj.1, hj.2, ?_⟩
  by_cases hj0 : j = 0
  · have hmesh : 0 < 1 / (m : ℝ) := by positivity
    simpa only [hj0] using (lt_add_of_le_of_pos hlo hmesh)
  · have hjpred : transferScale m (j - 1) < target := by
      by_contra h
      have hp : j - 1 < m ∧ target ≤ transferScale m (j - 1) :=
        ⟨by omega, le_of_not_gt h⟩
      have hmin : j ≤ j - 1 := Nat.find_min' hex hp
      omega
    have hstep : transferScale m j = transferScale m (j - 1) + 1 / (m : ℝ) := by
      unfold transferScale
      rw [Nat.cast_sub (by omega : 1 ≤ j)]
      push_cast
      ring
    rw [hstep]
    linarith

/-- A requested nonnegative shift fits a later grid point with one mesh of
overshoot. -/
theorem exists_transferScale_shift {m i : ℕ} (hm : 0 < m)
    {shift : ℝ} (hshift : 0 ≤ shift) (hroom : transferScale m i + shift ≤ 1) :
    ∃ j < m, i ≤ j ∧ shift ≤ transferScale m j - transferScale m i ∧
      transferScale m j - transferScale m i < shift + 1 / (m : ℝ) := by
  have hzero : transferScale m 0 ≤ transferScale m i :=
    (transferScale_le_iff hm).mpr (Nat.zero_le i)
  obtain ⟨j, hj, hlow, hhigh⟩ := exists_transferScale_above hm
    (show transferScale m 0 ≤ transferScale m i + shift by linarith) hroom
  refine ⟨j, hj, (transferScale_le_iff hm).mp (by linarith), ?_, ?_⟩ <;> linarith

/-- An even-sized grid can be chosen before the source problem. It has a central
point exactly at one half and any prescribed positive mesh upper bound. -/
theorem exists_central_transfer_grid {mesh : ℝ} (hmesh : 0 < mesh) :
    ∃ m i : ℕ, 0 < m ∧ i < m ∧ transferScale m i = 1 / 2 ∧
      1 / (m : ℝ) ≤ mesh := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hmesh
  refine ⟨2 * (n + 1), n, by omega, by omega, ?_, ?_⟩
  · unfold transferScale
    push_cast
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    field_simp
  · have hnpos : (0 : ℝ) < n + 1 := by positivity
    have hden : (n : ℝ) + 1 ≤ (2 * (n + 1) : ℕ) := by
      push_cast
      linarith
    exact (one_div_le_one_div_of_le hnpos hden).trans hn.le

/-- Moving past a strip exponent of at most four gains leaves a positive
candidate gain, even after both path-depth errors. All depths here are divided
by the length of the source problem. -/
theorem transfer_gain_reserve {e κ gain δ si sj ri rj u : ℝ}
    (he : 0 < e) (heupper : e ≤ 1 / 8) (hκ : 0 < κ) (hκupper : κ ≤ 1)
    (hgain : e * κ ^ 2 = 64 * gain)
    (hδ : 0 ≤ δ) (hδupper : δ ≤ gain)
    (hsi : 1 / 4 ≤ si) (hsiupper : si ≤ 1 / 2) (hu : 0 ≤ u)
    (hshiftlower : u + 2 * δ ≤ κ * (sj - si))
    (hshiftupper : κ * (sj - si) ≤ 7 * gain)
    (hri : |ri - si| ≤ δ) (hrj : |rj - sj| ≤ δ) :
    0 ≤ rj - ri ∧ κ * (rj - ri) ≤ 9 * gain ∧
      gain ≤ e * κ * si - (rj - ri) ∧
      e * κ * si - (rj - ri) ≤ 1 / 8 ∧
      rj + 2 * (e * κ * si - (rj - ri)) ≤ 1 := by
  have hgainpos : 0 < gain := by
    have := mul_pos he (sq_pos_of_pos hκ)
    nlinarith
  have hκδ : κ * δ ≤ δ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hκupper) hδ]
  have hri' := abs_le.mp hri
  have hrj' := abs_le.mp hrj
  have hdifflo : si - sj - 2 * δ ≤ ri - rj := by linarith
  have hdiffhi : ri - rj ≤ si - sj + 2 * δ := by linarith
  have hdiff : 0 ≤ rj - ri := by
    have := mul_le_mul_of_nonneg_left hdiffhi hκ.le
    nlinarith
  have hdiffupper : κ * (rj - ri) ≤ 9 * gain := by
    have := mul_le_mul_of_nonneg_left hdifflo hκ.le
    nlinarith
  have hleft : 16 * gain ≤ e * κ ^ 2 * si := by
    have := mul_nonneg (mul_pos he (sq_pos_of_pos hκ)).le
      (sub_nonneg.mpr hsi)
    nlinarith
  have hκgain : κ * gain ≤ gain :=
    (mul_le_mul_of_nonneg_right hκupper hgainpos.le).trans_eq (one_mul _)
  have hremaining : gain ≤ e * κ * si - (rj - ri) := by
    have : κ * gain ≤ κ * (e * κ * si - (rj - ri)) := by nlinarith
    exact (mul_le_mul_iff_right₀ hκ).mp (by simpa [mul_comm] using this)
  have hκsi : 0 ≤ κ * si ∧ κ * si ≤ 1 / 2 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg (sub_nonneg.mpr hκupper) (show 0 ≤ si by linarith)]
  have hold : e * κ * si ≤ 1 / 16 := by
    have := mul_le_mul heupper hκsi.2 hκsi.1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith
  have hκsq : κ ^ 2 ≤ 1 := by nlinarith
  have hgainupper : gain ≤ 1 / 8 := by
    have := mul_le_mul heupper hκsq (sq_nonneg κ) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith
  exact ⟨hdiff, hdiffupper, hremaining, by linarith, by linarith⟩

/-- A time improvement `h^e` uses the ACTUAL dyadic time exponent. Its error of
at most `e*delta` can be kept along with both path-depth errors; it need not be
replaced by the nominal grid exponent. -/
theorem transfer_gain_reserve_with_time_error {e κ gain δ si sj ri rj u a : ℝ}
    (he : 0 < e) (heupper : e ≤ 1 / 8) (hκ : 0 < κ) (hκupper : κ ≤ 1)
    (hgain : e * κ ^ 2 = 64 * gain)
    (hδ : 0 ≤ δ) (hδupper : δ ≤ gain)
    (hsi : 1 / 4 ≤ si) (hsiupper : si ≤ 1 / 2) (hu : 0 ≤ u)
    (hshiftlower : u + 2 * δ ≤ κ * (sj - si))
    (hshiftupper : κ * (sj - si) ≤ 7 * gain)
    (hri : |ri - si| ≤ δ) (hrj : |rj - sj| ≤ δ)
    (ha : |a - e * κ * si| ≤ e * δ) :
    0 ≤ rj - ri ∧ gain ≤ a - (rj - ri) ∧ a - (rj - ri) ≤ 1 / 8 ∧
      rj + 2 * (a - (rj - ri)) ≤ 1 := by
  have hbase := transfer_gain_reserve he heupper hκ hκupper hgain hδ hδupper
    hsi hsiupper hu hshiftlower hshiftupper hri hrj
  have hgainpos : 0 < gain := by
    have := mul_pos he (sq_pos_of_pos hκ)
    nlinarith
  have hκsq : κ ^ 2 ≤ 1 := by nlinarith
  have hgainupper : gain ≤ 1 / 8 := by
    have := mul_le_mul heupper hκsq (sq_nonneg κ) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith
  have heκ : e * κ ≤ 1 := by
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hκupper)]
  have heκδ : e * κ * δ ≤ gain := by
    have := mul_le_mul_of_nonneg_right heκ hδ
    nlinarith
  have hleft : 16 * gain ≤ e * κ ^ 2 * si := by
    have := mul_nonneg (mul_pos he (sq_pos_of_pos hκ)).le (sub_nonneg.mpr hsi)
    nlinarith
  have hκgain : κ * gain ≤ gain := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hκupper) hgainpos.le]
  have ha' := abs_le.mp ha
  have hlow := mul_le_mul_of_nonneg_left ha'.1 hκ.le
  have hremaining : gain ≤ a - (rj - ri) := by
    have : κ * gain ≤ κ * (a - (rj - ri)) := by nlinarith [hbase.2.1]
    exact (mul_le_mul_iff_right₀ hκ).mp (by simpa [mul_comm] using this)
  have hκsi : 0 ≤ κ * si ∧ κ * si ≤ 1 / 2 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg (sub_nonneg.mpr hκupper) (show 0 ≤ si by linarith)]
  have hnominal : e * κ * si ≤ 1 / 16 := by
    have := mul_le_mul heupper hκsi.2 hκsi.1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith
  have htimeError : e * δ ≤ 1 / 64 := by
    have := mul_le_mul heupper (hδupper.trans hgainupper) hδ
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith
  have hri' := abs_le.mp hri
  exact ⟨hbase.1, hremaining, by linarith [hbase.1], by linarith [hbase.1]⟩

/-- The scale shift needed to absorb a strip fits the chosen uniform grid.
The constants are independent of every source problem, path, and format. -/
theorem exists_strip_transfer_node {m i : ℕ} (hm : 0 < m)
    {e κ gain δ u : ℝ}
    (he : 0 < e) (heupper : e ≤ 1 / 8) (hκ : 0 < κ) (hκupper : κ ≤ 1)
    (hgain : e * κ ^ 2 = 64 * gain)
    (hδ : 0 ≤ δ) (hδupper : δ ≤ gain)
    (hu : 0 ≤ u) (huupper : u ≤ 4 * gain)
    (hmesh : 1 / (m : ℝ) ≤ gain / κ)
    (hsi : transferScale m i ≤ 1 / 2) :
    ∃ j < m, i ≤ j ∧ u + 2 * δ ≤ κ * (transferScale m j - transferScale m i) ∧
      κ * (transferScale m j - transferScale m i) ≤ 7 * gain := by
  have hgainpos : 0 < gain := by
    have := mul_pos he (sq_pos_of_pos hκ)
    nlinarith
  have heκ : e * κ ≤ 1 / 8 := by
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hκupper)]
  have hgκ : 64 * gain ≤ κ := by
    have := mul_le_mul_of_nonneg_right heκ hκ.le
    nlinarith
  have hshift : 0 ≤ (u + 2 * δ) / κ := div_nonneg (by linarith) hκ.le
  have hroom : transferScale m i + (u + 2 * δ) / κ ≤ 1 := by
    have hdiv : (u + 2 * δ) / κ ≤ 1 - transferScale m i := by
      apply (div_le_iff₀ hκ).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsi hκ.le]
    linarith
  obtain ⟨j, hj, hij, hlo, hhi⟩ := exists_transferScale_shift hm hshift hroom
  refine ⟨j, hj, hij, ?_, ?_⟩
  · simpa only [mul_comm] using (div_le_iff₀ hκ).mp hlo
  · have hmeshκ : κ * (1 / (m : ℝ)) ≤ gain := by
      simpa only [mul_comm] using (le_div_iff₀ hκ).mp hmesh
    have hmul := mul_le_mul_of_nonneg_left hhi.le hκ.le
    rw [mul_add, mul_div_cancel₀ _ hκ.ne'] at hmul
    nlinarith

/-- The dyadic time bounds in the frozen path turn the guarded scale shift
into actual time contraction by the strip exponent. -/
theorem dyadic_time_contraction {N L κ δ si sj u : ℝ} {Ti Tj : ℕ}
    (hN : 1 ≤ N) (hL : 0 ≤ L)
    (hi : (2 : ℝ) ^ Ti ≤ N ^ ((κ * si + δ) * L))
    (hj : N ^ ((κ * sj - δ) * L) ≤ (2 : ℝ) ^ Tj)
    (hshift : u + 2 * δ ≤ κ * (sj - si)) :
    (2 : ℝ) ^ Ti * N ^ (u * L) ≤ (2 : ℝ) ^ Tj := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    (2 : ℝ) ^ Ti * N ^ (u * L) ≤ N ^ ((κ * si + δ) * L) * N ^ (u * L) :=
      mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg hNpos.le _)
    _ = N ^ (((κ * si + δ) + u) * L) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    _ ≤ N ^ ((κ * sj - δ) * L) :=
      Real.rpow_le_rpow_of_exponent_le hN
        (mul_le_mul_of_nonneg_right (by nlinarith) hL)
    _ ≤ _ := hj

/-- The same guarded time comparison in block-length units. -/
theorem dyadic_length_contraction {N L κ δ si sj u : ℝ} {Ti Tj : ℕ}
    (hN : 1 ≤ N) (hL : 0 ≤ L)
    (hi : (2 : ℝ) ^ Ti ≤ N ^ ((κ * si + δ) * L))
    (hj : N ^ ((κ * sj - δ) * L) ≤ (2 : ℝ) ^ Tj)
    (hshift : u + 2 * δ ≤ κ * (sj - si)) :
    N ^ (u * L) * ((2 : ℝ) ^ Tj)⁻¹ ≤ ((2 : ℝ) ^ Ti)⁻¹ := by
  have h := dyadic_time_contraction hN hL hi hj hshift
  have hiPos : (0 : ℝ) < 2 ^ Ti := by positivity
  have hjPos : (0 : ℝ) < 2 ^ Tj := by positivity
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hjPos hiPos]
  simpa only [one_mul, mul_comm] using h

/-- Read the actual normalized gain of `h^e` directly from the two frozen
dyadic time inequalities. This preserves its true mass exponent. -/
theorem normalized_time_gain_error {N L κ si δ e : ℝ} {T : ℕ}
    (hN : 1 < N) (hL : 0 < L) (he : 0 ≤ e)
    (hlo : N ^ ((κ * si - δ) * L) ≤ (2 : ℝ) ^ T)
    (hhi : (2 : ℝ) ^ T ≤ N ^ ((κ * si + δ) * L)) :
    |e * (Real.logb N ((2 : ℝ) ^ T) / L) - e * κ * si| ≤ e * δ := by
  have hNpos : 0 < N := lt_trans zero_lt_one hN
  have hloglo := Real.logb_le_logb_of_le hN (Real.rpow_pos_of_pos hNpos _) hlo
  have hloghi := Real.logb_le_logb_of_le hN (by positivity) hhi
  rw [Real.logb_rpow hNpos (ne_of_gt hN)] at hloglo hloghi
  have hlo' : κ * si - δ ≤ Real.logb N ((2 : ℝ) ^ T) / L :=
    (le_div_iff₀ hL).mpr hloglo
  have hhi' : Real.logb N ((2 : ℝ) ^ T) / L ≤ κ * si + δ :=
    (div_le_iff₀ hL).mpr hloghi
  have hfit : |Real.logb N ((2 : ℝ) ^ T) / L - κ * si| ≤ δ := by
    rw [abs_le]
    constructor <;> linarith
  calc
    _ = |e| * |Real.logb N ((2 : ℝ) ^ T) / L - κ * si| := by
      rw [← abs_mul]
      congr 1
      ring
    _ = e * |Real.logb N ((2 : ℝ) ^ T) / L - κ * si| := by rw [abs_of_nonneg he]
    _ ≤ e * δ := mul_le_mul_of_nonneg_left hfit he

/-- The grid, fixed gain and tolerance can all be chosen uniformly before the
problem and its format. Every strip exponent at most four gains has a finer
node that both absorbs the strip and preserves an admissible candidate gain. -/
theorem exists_uniform_transfer_grid {e κ ρ : ℝ}
    (he : 0 < e) (heupper : e ≤ 1 / 8) (hκ : 0 < κ) (hκupper : κ ≤ 1)
    (hρ : 0 < ρ) :
    ∃ (m i : ℕ) (gain δ : ℝ),
      (0 < m ∧ 0 < transferScale m 0 ∧
        (∀ n, n + 1 < m → transferScale m n < transferScale m (n + 1)) ∧
        transferScale m (m - 1) = 1) ∧
      0 < gain ∧ gain ≤ 1 / 8 ∧ 0 < δ ∧ δ ≤ ρ * gain ∧ δ ≤ gain ∧
      i < m ∧ transferScale m i = 1 / 2 ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 4 * gain →
        ∃ j < m, i ≤ j ∧
          u + 2 * δ ≤ κ * (transferScale m j - transferScale m i) ∧
          ∀ ri rj : ℝ, |ri - transferScale m i| ≤ δ →
            |rj - transferScale m j| ≤ δ →
            0 ≤ rj - ri ∧
              gain ≤ e * κ * transferScale m i - (rj - ri) ∧
              e * κ * transferScale m i - (rj - ri) ≤ 1 / 8 ∧
              rj + 2 * (e * κ * transferScale m i - (rj - ri)) ≤ 1 := by
  let gain := e * κ ^ 2 / 64
  have hgain : e * κ ^ 2 = 64 * gain := by dsimp [gain]; ring
  have hgpos : 0 < gain := by dsimp [gain]; positivity
  have hκsq : κ ^ 2 ≤ 1 := by nlinarith
  have hgupper : gain ≤ 1 / 8 := by
    have := mul_le_mul heupper hκsq (sq_nonneg κ) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith
  let δ := min gain (ρ * gain) / 2
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδgain : δ ≤ gain := by
    have := min_le_left gain (ρ * gain)
    dsimp [δ]
    linarith
  have hδrho : δ ≤ ρ * gain := by
    have := min_le_right gain (ρ * gain)
    have := mul_pos hρ hgpos
    dsimp [δ]
    linarith
  obtain ⟨m, i, hm, hi, hcenter, hmesh⟩ :=
    exists_central_transfer_grid (div_pos hgpos hκ)
  refine ⟨m, i, gain, δ, transferScale_valid hm, hgpos, hgupper,
    hδpos, hδrho, hδgain, hi, hcenter, ?_⟩
  intro u hu huupper
  obtain ⟨j, hj, hij, hshiftlo, hshifthi⟩ := exists_strip_transfer_node hm
    he heupper hκ hκupper hgain hδpos.le hδgain hu huupper hmesh (by rw [hcenter])
  refine ⟨j, hj, hij, hshiftlo, ?_⟩
  intro ri rj hri hrj
  have hres := transfer_gain_reserve he heupper hκ hκupper hgain
    hδpos.le hδgain (by rw [hcenter]; norm_num) (by rw [hcenter])
    hu hshiftlo hshifthi hri hrj
  exact ⟨hres.1, hres.2.2⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
