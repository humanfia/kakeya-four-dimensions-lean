-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormDegree.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormFamily

/-!
# Degree bounds for the conflict relations

A used tube (resp. cover) of radius `ρ` conflicts with fewer than `normColors lam` others, for
zoomed radius `R ≤ 25 lam ρ` and `3 · 10 ^ 8 lam ρ ≤ 1`.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory Finset
open scoped ENNReal

/-- The number of colours. -/
noncomputable def normColors (lam : ℝ) : ℕ := ⌊(10 : ℝ) ^ 50 * lam ^ 4⌋₊ + 1

theorem normColors_pos (lam : ℝ) : 0 < normColors lam := Nat.succ_pos _

theorem normColors_le {lam : ℝ} (hlam : 1 ≤ lam) :
    (normColors lam : ℝ) ≤ 2 * 10 ^ 50 * lam ^ 4 := by
  unfold normColors
  push_cast
  have h1 : (⌊(10 : ℝ) ^ 50 * lam ^ 4⌋₊ : ℝ) ≤ 10 ^ 50 * lam ^ 4 :=
    Nat.floor_le (by positivity)
  have h2 : (1 : ℝ) ≤ 10 ^ 50 * lam ^ 4 := by
    have : (1 : ℝ) ≤ lam ^ 4 := one_le_pow₀ hlam
    nlinarith
  linarith

open scoped Classical in
theorem conflict_degree_lt {k : ℕ} {c : Space} {lam ρ R : ℝ} (hlam : 1 ≤ lam) (hρ : 0 < ρ)
    (hR0 : 0 ≤ R) (hRρ : R ≤ 25 * lam * ρ) (z w : Fin k → Space) (hw : ∀ j, ‖w j‖ = 1)
    (hsep : ∀ j j', j ≠ j' → volume (tube ρ (z j) (w j) ∩ tube ρ (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (tube ρ (z j) (w j)))
    (U : Fin k → Prop) (hU : ∀ j, U j → ‖c - z j‖ ≤ 3) (hsmall : 3 * 10 ^ 8 * lam * ρ ≤ 1)
    (j : Fin k) : (univ.filter (conflict c lam R z w U j)).card < normColors lam := by
  classical
  have hlam0 : 0 < lam := by linarith
  by_cases hUj : U j
  swap
  · have : univ.filter (conflict c lam R z w U j) = ∅ := by
      apply Finset.filter_false_of_mem
      intro j' _ h
      exact hUj h.1
    rw [this, Finset.card_empty]; exact normColors_pos lam
  set r := (2 + 8 * lam) * (10000 * R / lam) + ρ with hr
  have hr1 : r ≤ 2500001 * lam * ρ := by
    have h1 : (2 + 8 * lam) * (10000 * R / lam) ≤ (10 * lam) * (10000 * (25 * lam * ρ) / lam) := by
      apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
      apply div_le_div_of_nonneg_right _ hlam0.le
      linarith
    have h2 : (10 * lam) * (10000 * (25 * lam * ρ) / lam) = 2500000 * lam * ρ := by
      field_simp; ring
    have h3 : ρ ≤ lam * ρ := by nlinarith
    rw [hr]; linarith
  have hsmall' : r ≤ 1 / 4 := by nlinarith
  set R₅ := 117 * r + ρ with hR₅
  have hR₅b : R₅ ≤ 3 * 10 ^ 8 * lam * ρ := by
    have h3 : ρ ≤ lam * ρ := by nlinarith
    rw [hR₅]; nlinarith
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hR₅pos : 0 < R₅ := by rw [hR₅]; linarith
  have hsub : ∀ j' ∈ univ.filter (conflict c lam R z w U j),
      tube ρ (z j') (w j') ⊆ LC (foot c (z j) (w j)) (w j) 61 R₅ := by
    intro j' hj'
    have hc := (mem_filter.mp hj').2
    exact subset_LC_of_conflict hlam hρ hR0 hw hU hsmall' hc
  have hcount := card_le_of_subset_LC hρ hR₅pos (hR₅b.trans hsmall) z w hw hsep (hw j)
    (univ.filter (conflict c lam R z w U j)) hsub
  have hbound : ((univ.filter (conflict c lam R z w U j)).card : ℝ) ≤
      10 ^ 6 * 46848 ^ 2 * (3 * 10 ^ 8) ^ 4 * lam ^ 4 := by
    have hρ4 : 0 < ρ ^ 4 := by positivity
    have h1 : (46848 * R₅ ^ 2) ^ 2 ≤ (46848 * (3 * 10 ^ 8 * lam * ρ) ^ 2) ^ 2 := by
      have : 0 ≤ R₅ := hR₅pos.le
      gcongr
    have h2 : 10 ^ 6 * (46848 * (3 * 10 ^ 8 * lam * ρ) ^ 2) ^ 2 =
        10 ^ 6 * 46848 ^ 2 * (3 * 10 ^ 8) ^ 4 * lam ^ 4 * ρ ^ 4 := by ring
    have h3 := hcount.trans (le_trans (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2.le)
    exact le_of_mul_le_mul_right (by linarith) hρ4
  have hfloor : (10 : ℝ) ^ 6 * 46848 ^ 2 * (3 * 10 ^ 8) ^ 4 * lam ^ 4 <
      (normColors lam : ℝ) := by
    unfold normColors
    push_cast
    have h1 := Nat.lt_floor_add_one ((10 : ℝ) ^ 50 * lam ^ 4)
    have h2 : (10 : ℝ) ^ 6 * 46848 ^ 2 * (3 * 10 ^ 8) ^ 4 * lam ^ 4 ≤ 10 ^ 50 * lam ^ 4 := by
      have : (0 : ℝ) ≤ lam ^ 4 := by positivity
      nlinarith
    linarith
  exact_mod_cast hbound.trans_lt hfloor

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
