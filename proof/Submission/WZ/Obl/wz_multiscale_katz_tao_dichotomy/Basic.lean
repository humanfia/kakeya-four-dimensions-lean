-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_endpoint_bootstrap

namespace WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

abbrev Tube := wz_endpoint_bootstrap.tube
abbrev KatzTao := @wz_endpoint_bootstrap.Katz
abbrev Frostman := @wz_endpoint_bootstrap.Frostman
abbrev Dense := @wz_endpoint_bootstrap.Dense

/-- The admissibility predicate in the frozen statement. -/
def Admissible (δ η M L : ℝ) {n : ℕ} (x v : Fin n → Space)
    (Y : Fin n → Set Space) : Prop :=
  0 < n ∧
  (∀ i, ‖v i‖ = 1 ∧ Tube δ (x i) (v i) ⊆ ball 0 1 ∧
    MeasurableSet (Y i) ∧ Y i ⊆ Tube δ (x i) (v i)) ∧
  (∀ i j, i ≠ j → volume (Tube δ (x i) (v i) ∩ Tube δ (x j) (v j)) ≤
    (1 / 2 : ℝ≥0∞) * volume (Tube δ (x i) (v i))) ∧
  Dense δ η Y ∧ KatzTao δ M x v ∧ Frostman δ L x v

theorem Admissible.mono {δ η η' M M' L L' : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible δ η M L x v Y) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : η ≤ η') (hM : M ≤ M') (hL : L ≤ L') :
    Admissible δ η' M' L' x v Y := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.mono hδ hδ1 hη,
    h.2.2.2.2.1.mono hM, h.2.2.2.2.2.mono hL⟩

theorem Admissible.mono_eta {δ η η' : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible δ η (δ ^ (-η)) (δ ^ (-η)) x v Y)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η') :
    Admissible δ η' (δ ^ (-η')) (δ ^ (-η')) x v Y := by
  have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)
  exact h.mono hδ hδ1 hη hp hp

theorem Admissible.measurable_union {δ η M L : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible δ η M L x v Y) : MeasurableSet (⋃ i, Y i) :=
  MeasurableSet.iUnion fun i => (h.2.1 i).2.2.1

theorem Admissible.union_subset_ball {δ η M L : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible δ η M L x v Y) : (⋃ i, Y i) ⊆ ball 0 1 := by
  refine iUnion_subset fun i => ?_
  exact (h.2.1 i).2.2.2.trans (h.2.1 i).2.1

theorem Admissible.volume_ne_top {δ η M L : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible δ η M L x v Y) (i : Fin n) : volume (Y i) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_ball_ne_top
    (measure_mono ((h.2.1 i).2.2.2.trans (h.2.1 i).2.1))

theorem Admissible.total_volume_ne_top {δ η M L : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible δ η M L x v Y) : (∑ i, volume (Y i)) ≠ ⊤ := by
  exact ENNReal.sum_ne_top.mpr fun i _ => h.volume_ne_top i

theorem Admissible.total_volume_pos {δ η M L : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible δ η M L x v Y) (hδ : 0 < δ) : 0 < ∑ i, volume (Y i) := by
  apply lt_of_lt_of_le _ h.2.2.2.1
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hδ _) (Nat.cast_pos.mpr h.1))
    (sq_pos_of_pos hδ)

theorem total_volume_le_card_mul_union {n : ℕ} (Y : Fin n → Set Space) :
    ∑ i, volume (Y i) ≤ (n : ℝ≥0∞) * volume (⋃ i, Y i) := by
  calc
    ∑ i, volume (Y i) ≤ ∑ _ : Fin n, volume (⋃ i, Y i) :=
      Finset.sum_le_sum fun i _ => measure_mono (subset_iUnion Y i)
    _ = _ := by simp

/-- The average shading gives a lower bound without any transversality assumptions. -/
theorem Admissible.union_volume_lower {δ η M L : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Admissible δ η M L x v Y) (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ volume (⋃ i, Y i) := by
  have h₁ := h.2.2.2.1.trans (total_volume_le_card_mul_union Y)
  have heq : ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) =
      (n : ℝ≥0∞) * ENNReal.ofReal (δ ^ η * δ ^ 2) := by
    rw [show δ ^ η * (n : ℝ) * δ ^ 2 = (n : ℝ) * (δ ^ η * δ ^ 2) by ring,
      ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  rw [heq] at h₁
  exact (ENNReal.mul_le_mul_iff_right (a := (n : ℝ≥0∞))
    (by exact_mod_cast h.1.ne') (by simp)).mp h₁

/-- Refining a shading can be budgeted directly by the total retained measure. -/
theorem Dense.of_retained_mass {δ η ζ : ℝ} {n m : ℕ}
    {Y : Fin n → Set Space} {Z : Fin m → Set Space}
    (hδ : 0 < δ) (hm : m ≤ n) (hY : Dense δ η Y)
    (hZ : ENNReal.ofReal (δ ^ ζ) * ∑ i, volume (Y i) ≤ ∑ j, volume (Z j)) :
    Dense δ (η + ζ) Z := by
  apply le_trans _ hZ
  calc
    ENNReal.ofReal (δ ^ (η + ζ) * (m : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal (δ ^ (η + ζ) * (n : ℝ) * δ ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      gcongr
    _ = ENNReal.ofReal (δ ^ ζ) * ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _), Real.rpow_add hδ]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (δ ^ ζ) * ∑ i, volume (Y i) := mul_le_mul_right hY _

end WangZahlLot.Obl.wz_multiscale_katz_tao_dichotomy
