-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.ScaleDyadic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale

/-- The dyadic exponent of a dimension `a ∈ (0, M]`. -/
def dyExp (M a : ℝ) : ℕ := ⌊Real.logb 2 (M / a)⌋₊

/-- The dyadic round-up `M / 2 ^ dyExp M a` of `a`. -/
def dyUp (M a : ℝ) : ℝ := M / 2 ^ dyExp M a

theorem le_dyUp {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) : a ≤ dyUp M a := by
  have hM : 0 < M := ha.trans_le haM
  have h1 : (1 : ℝ) ≤ M / a := by rw [le_div_iff₀ ha]; linarith
  have hlog : 0 ≤ Real.logb 2 (M / a) := Real.logb_nonneg (by norm_num) h1
  have h2 : (2 : ℝ) ^ dyExp M a ≤ M / a := by
    have := Nat.floor_le hlog
    calc (2 : ℝ) ^ dyExp M a = (2 : ℝ) ^ ((dyExp M a : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ Real.logb 2 (M / a) := Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = M / a := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  unfold dyUp
  rw [le_div_iff₀ (by positivity)]
  rw [le_div_iff₀ ha] at h2
  linarith

theorem dyUp_lt {M a : ℝ} (ha : 0 < a) (hM : 0 < M) : dyUp M a < 2 * a := by
  have h2 : M / a < (2 : ℝ) ^ (dyExp M a + 1) := by
    have := Nat.lt_floor_add_one (Real.logb 2 (M / a))
    calc M / a = (2 : ℝ) ^ Real.logb 2 (M / a) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ < (2 : ℝ) ^ ((dyExp M a : ℝ) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by simpa [dyExp] using this)
      _ = (2 : ℝ) ^ (dyExp M a + 1) := by rw [← Real.rpow_natCast]; push_cast; rfl
  unfold dyUp
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ ha, pow_succ] at h2
  linarith

theorem dyExp_le {M a ρ : ℝ} (hM : 0 < M) (hρ : 0 < ρ) (hρa : ρ ≤ a) :
    dyExp M a ≤ dyExp M ρ := by
  unfold dyExp
  apply Nat.floor_le_floor
  apply Real.logb_le_logb_of_le (by norm_num) (div_pos hM (hρ.trans_le hρa))
  exact div_le_div_of_nonneg_left hM.le hρ hρa

theorem dyUp_le {M a : ℝ} (hM : 0 ≤ M) : dyUp M a ≤ M := by
  unfold dyUp
  exact div_le_self hM (one_le_pow₀ (by norm_num))

theorem dyUp_le_dyUp {M a b : ℝ} (hM : 0 ≤ M) (h : dyExp M b ≤ dyExp M a) :
    dyUp M a ≤ dyUp M b := by
  unfold dyUp
  exact div_le_div_of_nonneg_left hM (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-- Dyadic annuli with lower endpoints at most one cover every positive
angle at most two, using only logarithmically many endpoints. -/
theorem dyadic_annulus {s₀ s : ℝ} (hs₀ : 0 < s₀) (hs₀s : s₀ ≤ s) (hs2 : s ≤ 2) :
    ∃ j : Fin (dyExp 1 (s₀ / 2) + 1),
      s₀ / 2 ≤ 1 / (2 : ℝ) ^ (j : ℕ) ∧ 1 / (2 : ℝ) ^ (j : ℕ) ≤ 1 ∧
      1 / (2 : ℝ) ^ (j : ℕ) ≤ s ∧ s ≤ 2 * (1 / (2 : ℝ) ^ (j : ℕ)) := by
  have hs : 0 < s := hs₀.trans_le hs₀s
  let j : Fin (dyExp 1 (s₀ / 2) + 1) := ⟨dyExp 1 (s / 2),
    Nat.lt_succ_of_le (dyExp_le (by norm_num) (by positivity) (by linarith))⟩
  have hlow := le_dyUp (by positivity : 0 < s / 2) (by linarith : s / 2 ≤ 1)
  have hhigh := dyUp_lt (by positivity : 0 < s / 2) (by norm_num : (0 : ℝ) < 1)
  have hone := dyUp_le (a := s / 2) (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨j, ?_, ?_, ?_, ?_⟩ <;> change _ ≤ _
  · change s₀ / 2 ≤ dyUp 1 (s / 2)
    linarith
  · exact hone
  · change dyUp 1 (s / 2) ≤ s
    linarith
  · change s ≤ 2 * dyUp 1 (s / 2)
    linarith


end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Scale
