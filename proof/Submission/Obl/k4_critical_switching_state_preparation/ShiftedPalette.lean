import Mathlib
import Submission.Obl.k4_scalar_normalized_exact_refinement.ChartObs

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory
open scoped ENNReal

noncomputable section

/-- Two raw velocity bins cover each bin after a real velocity translation. -/
theorem raw_floor_of_shifted {h c w : ℝ} {j : ℤ}
    (hj : ⌊(w - c) / h⌋ = j) :
    ⌊w / h⌋ = j + ⌊c / h⌋ ∨ ⌊w / h⌋ = j + ⌊c / h⌋ + 1 := by
  have hh := Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis.floor_add_cases
    ((w - c) / h) (c / h)
  rwa [show (w - c) / h + c / h = w / h by ring, hj] at hh

/-- A raw palette bin is assigned to both of its possible translated bins. -/
def shiftPaletteAtom (h c : ℝ) (n : ℤ) (w : ℝ) : ℝ :=
  h * ((⌊w / h⌋ - ⌊c / h⌋ - n : ℤ) : ℝ)

def shiftedPalette (π : Measure ℝ) (h c : ℝ) : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • π.map (shiftPaletteAtom h c 0) +
    (1 / 2 : ℝ≥0∞) • π.map (shiftPaletteAtom h c 1)

theorem measurable_shiftPaletteAtom (h c : ℝ) (n : ℤ) :
    Measurable (shiftPaletteAtom h c n) := by
  unfold shiftPaletteAtom
  fun_prop

theorem shiftedPalette_probability (π : Measure ℝ) [IsProbabilityMeasure π] (h c : ℝ) :
    IsProbabilityMeasure (shiftedPalette π h c) := by
  constructor
  simp [shiftedPalette, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_shiftPaletteAtom h c _) MeasurableSet.univ,
    ENNReal.inv_two_add_inv_two]

theorem shiftPaletteAtom_tag {h : ℝ} (hh : 0 < h) (c : ℝ) (n : ℤ) (w : ℝ) :
    ⌊shiftPaletteAtom h c n w / h⌋ = ⌊w / h⌋ - ⌊c / h⌋ - n := by
  simp [shiftPaletteAtom, hh.ne']

theorem map_shiftPaletteAtom_bin (π : Measure ℝ) {h : ℝ} (hh : 0 < h)
    (c : ℝ) (n j : ℤ) :
    (π.map (shiftPaletteAtom h c n)) {w | ⌊w / h⌋ = j} =
      π {w | ⌊w / h⌋ = j + ⌊c / h⌋ + n} := by
  rw [Measure.map_apply (measurable_shiftPaletteAtom h c n)
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  congr 1
  ext w
  change ⌊shiftPaletteAtom h c n w / h⌋ = j ↔ ⌊w / h⌋ = j + ⌊c / h⌋ + n
  rw [shiftPaletteAtom_tag hh]
  omega

/-- The translated palette gives half of each adjacent raw-bin mass. -/
theorem shiftedPalette_bin (π : Measure ℝ) {h : ℝ} (hh : 0 < h) (c : ℝ) (j : ℤ) :
    shiftedPalette π h c {w | ⌊w / h⌋ = j} =
      (1 / 2 : ℝ≥0∞) * π {w | ⌊w / h⌋ = j + ⌊c / h⌋} +
        (1 / 2 : ℝ≥0∞) * π {w | ⌊w / h⌋ = j + ⌊c / h⌋ + 1} := by
  simp only [shiftedPalette, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    map_shiftPaletteAtom_bin π hh, add_zero]

theorem twice_shiftedPalette_bin (π : Measure ℝ) {h : ℝ} (hh : 0 < h)
    (c : ℝ) (j : ℤ) :
    2 * shiftedPalette π h c {w | ⌊w / h⌋ = j} =
      π {w | ⌊w / h⌋ = j + ⌊c / h⌋} +
        π {w | ⌊w / h⌋ = j + ⌊c / h⌋ + 1} := by
  rw [shiftedPalette_bin π hh]
  simp only [one_div, mul_add, ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp), one_mul]

/-- A translation changes the original joint velocity ceiling by only a factor two. -/
theorem shifted_palette_cap {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (state : Ω → Q) (vel : Ω → ℝ) (π : Measure ℝ)
    {h : ℝ} (hh : 0 < h) (c : ℝ) (C : Q → ℝ≥0∞)
    (hcap : ∀ q j, μ {p | state p = q ∧ ⌊vel p / h⌋ = j} ≤
      C q * π {w | ⌊w / h⌋ = j}) :
    ∀ q j, μ {p | state p = q ∧ ⌊(vel p - c) / h⌋ = j} ≤
      (2 * C q) * shiftedPalette π h c {w | ⌊w / h⌋ = j} := by
  intro q j
  have hsub : {p | state p = q ∧ ⌊(vel p - c) / h⌋ = j} ⊆
      {p | state p = q ∧ ⌊vel p / h⌋ = j + ⌊c / h⌋} ∪
      {p | state p = q ∧ ⌊vel p / h⌋ = j + ⌊c / h⌋ + 1} := by
    intro p hp
    rcases raw_floor_of_shifted hp.2 with h | h
    · exact Or.inl ⟨hp.1, h⟩
    · exact Or.inr ⟨hp.1, h⟩
  calc
    _ ≤ μ {p | state p = q ∧ ⌊vel p / h⌋ = j + ⌊c / h⌋} +
        μ {p | state p = q ∧ ⌊vel p / h⌋ = j + ⌊c / h⌋ + 1} :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ C q * π {w | ⌊w / h⌋ = j + ⌊c / h⌋} +
        C q * π {w | ⌊w / h⌋ = j + ⌊c / h⌋ + 1} :=
      add_le_add (hcap q _) (hcap q _)
    _ = _ := by rw [← mul_add, ← twice_shiftedPalette_bin π hh]; ring

theorem shiftPaletteAtom_error {h : ℝ} (hh : 0 < h) (c w : ℝ) {n : ℤ}
    (hn0 : 0 ≤ n) (hn1 : n ≤ 1) :
    |shiftPaletteAtom h c n w - (w - c)| ≤ 2 * h := by
  have hw0 := (le_div_iff₀ hh).mp (Int.floor_le (w / h))
  have hw1 := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (w / h))
  have hc0 := (le_div_iff₀ hh).mp (Int.floor_le (c / h))
  have hc1 := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (c / h))
  have hn0' : (0 : ℝ) ≤ n := by exact_mod_cast hn0
  have hn1' : (n : ℝ) ≤ 1 := by exact_mod_cast hn1
  dsimp [shiftPaletteAtom]
  push_cast
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Rounding and shifting the palette costs only two fine mesh widths in
an interval bound, uniformly in the real translation. -/
theorem shiftedPalette_interval_le (π : Measure ℝ) {h : ℝ} (hh : 0 < h)
    (c z r : ℝ) :
    shiftedPalette π h c (Icc (z - r) (z + r)) ≤
      π (Icc (z + c - (r + 2 * h)) (z + c + (r + 2 * h))) := by
  have hm (n : ℤ) (hn0 : 0 ≤ n) (hn1 : n ≤ 1) :
      (π.map (shiftPaletteAtom h c n)) (Icc (z - r) (z + r)) ≤
        π (Icc (z + c - (r + 2 * h)) (z + c + (r + 2 * h))) := by
    rw [Measure.map_apply (measurable_shiftPaletteAtom h c n) measurableSet_Icc]
    apply measure_mono
    intro w hw
    have hb := abs_le.mp (shiftPaletteAtom_error hh c w hn0 hn1)
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  calc
    _ ≤ (1 / 2 : ℝ≥0∞) * π (Icc (z + c - (r + 2 * h)) (z + c + (r + 2 * h))) +
        (1 / 2 : ℝ≥0∞) * π (Icc (z + c - (r + 2 * h)) (z + c + (r + 2 * h))) := by
      exact add_le_add (mul_le_mul' le_rfl (hm 0 (by norm_num) (by norm_num)))
        (mul_le_mul' le_rfl (hm 1 (by norm_num) (by norm_num)))
    _ = _ := by rw [← add_mul, one_div, ENNReal.inv_two_add_inv_two, one_mul]

end

end Submission.Obl.k4_critical_switching_state_preparation
