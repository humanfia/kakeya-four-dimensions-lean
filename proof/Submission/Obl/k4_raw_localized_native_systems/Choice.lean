import Mathlib

/-!
# The global numerical choices of the raw localization

For the extremal setup `(ds, kr, S, η)` the following exponents are fixed
before the accuracy `χ`, the thinness `w` and the neighborhood tolerance:

* `angU = min η 1 / 2`, the angular depth of the later bad-pair bound;
* `laterDepth = min (1/2) (S * angU / (8 * (1 + 2 * kr)))`, the target depth of
  the later system, so that `(1 + 2 kr) * laterDepth ≤ S * angU / 8`;
* `sExp = laterDepth / 2`, the frozen scalar depth `s`, and
  `mExp = sExp + 4`, `UExp = 1`.

For an accuracy `χ` and a thinness `w`:

* `nuOf = min (sExp / 8) (min (χ / 100) (η / 100))`;
* the earlier target depth is `sExp - 2 * nuOf`, the later one `laterDepth`;
* depth tolerance `nuOf / 2`, width error, width band and profile tolerance
  `nuOf / 10`;
* relative narrowness `wOf = 2 * (w + 20 + 2 * kr + 3 * angU) / sExp`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems

noncomputable section

/-- The angular depth of the later bad-pair bound. -/
def angU (η : ℝ) : ℝ := min η 1 / 2

/-- The target depth of the later system. -/
def laterDepth (kr S η : ℝ) : ℝ := min (1 / 2) (S * angU η / (8 * (1 + 2 * kr)))

/-- The frozen scalar depth `s`. -/
def sExp (kr S η : ℝ) : ℝ := laterDepth kr S η / 2

/-- The frozen window exponent `m`. -/
def mExp (kr S η : ℝ) : ℝ := sExp kr S η + 4

/-- The frozen exponent `U`. -/
def UExp : ℝ := 1

/-- The accuracy-dependent depth unit. -/
def nuOf (kr S η χ : ℝ) : ℝ := min (sExp kr S η / 8) (min (χ / 100) (η / 100))

/-- The two target depths: the earlier one strictly below `s`. -/
def sdOf (kr S η χ : ℝ) : ℕ → ℝ :=
  fun i => if i = 0 then sExp kr S η - 2 * nuOf kr S η χ else laterDepth kr S η

/-- The depth tolerance. -/
def epsOf (kr S η χ : ℝ) : ℝ := nuOf kr S η χ / 2

/-- The width error, the width band and the profile tolerance. -/
def tolOf (kr S η χ : ℝ) : ℝ := nuOf kr S η χ / 10

/-- The relative narrowness. -/
def wOf (kr S η w : ℝ) : ℝ := 2 * (w + 20 + 2 * kr + 3 * angU η) / sExp kr S η

section Bounds

variable {kr S η χ w : ℝ}

theorem angU_pos (hη : 0 < η) : 0 < angU η := by
  unfold angU; have := lt_min hη one_pos; positivity

theorem angU_le_half : angU η ≤ 1 / 2 := by
  unfold angU; have := min_le_right η 1; linarith

theorem angU_le (hη : 0 < η) : angU η ≤ η := by
  unfold angU; have := min_le_left η 1; linarith

theorem laterDepth_pos (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) :
    0 < laterDepth kr S η := by
  unfold laterDepth
  have := angU_pos hη
  exact lt_min (by norm_num) (by positivity)

theorem laterDepth_le_half : laterDepth kr S η ≤ 1 / 2 := min_le_left _ _

theorem laterDepth_bad (hkr : 0 ≤ kr) :
    (1 + 2 * kr) * laterDepth kr S η ≤ S * angU η / 8 := by
  unfold laterDepth
  have hpos : 0 < 8 * (1 + 2 * kr) := by positivity
  have h := min_le_right (1 / 2 : ℝ) (S * angU η / (8 * (1 + 2 * kr)))
  calc (1 + 2 * kr) * min (1 / 2) (S * angU η / (8 * (1 + 2 * kr)))
      ≤ (1 + 2 * kr) * (S * angU η / (8 * (1 + 2 * kr))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = S * angU η / 8 := by field_simp

theorem sExp_pos (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) : 0 < sExp kr S η := by
  unfold sExp; have := laterDepth_pos hkr hS hη; positivity

theorem sExp_lt_laterDepth (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) :
    sExp kr S η < laterDepth kr S η := by
  unfold sExp; have := laterDepth_pos hkr hS hη; linarith

theorem sExp_lt_one : sExp kr S η < 1 := by
  unfold sExp; have := (laterDepth_le_half : laterDepth kr S η ≤ 1 / 2); linarith

theorem sExp_lt_mExp : sExp kr S η < mExp kr S η := by unfold mExp; linarith

theorem UExp_pos : 0 < UExp := by unfold UExp; norm_num

theorem UExp_lt_mExp (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) : UExp < mExp kr S η := by
  unfold UExp mExp; have := sExp_pos hkr hS hη; linarith

theorem nuOf_pos (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) (hχ : 0 < χ) :
    0 < nuOf kr S η χ := by
  unfold nuOf; have := sExp_pos hkr hS hη
  exact lt_min (by positivity) (lt_min (by positivity) (by positivity))

theorem nuOf_le_s : nuOf kr S η χ ≤ sExp kr S η / 8 := min_le_left _ _

theorem nuOf_le_chi : nuOf kr S η χ ≤ χ / 100 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem nuOf_le_eta : nuOf kr S η χ ≤ η / 100 :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem sdOf_zero : sdOf kr S η χ 0 = sExp kr S η - 2 * nuOf kr S η χ := by
  simp [sdOf]

theorem sdOf_one : sdOf kr S η χ 1 = laterDepth kr S η := by simp [sdOf]

theorem sdOf_zero_pos (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) :
    0 < sdOf kr S η χ 0 := by
  rw [sdOf_zero]
  have h1 := sExp_pos hkr hS hη
  have h2 := (nuOf_le_s : nuOf kr S η χ ≤ sExp kr S η / 8)
  linarith

theorem sdOf_zero_lt_one (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) (hχ : 0 < χ) :
    sdOf kr S η χ 0 < sdOf kr S η χ 1 := by
  rw [sdOf_zero, sdOf_one]
  have h1 := sExp_lt_laterDepth hkr hS hη
  have h2 := nuOf_pos hkr hS hη hχ
  linarith

theorem sdOf_one_le : sdOf kr S η χ 1 ≤ 1 := by
  rw [sdOf_one]; have := (laterDepth_le_half : laterDepth kr S η ≤ 1 / 2); linarith

theorem epsOf_pos (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) (hχ : 0 < χ) :
    0 < epsOf kr S η χ := by
  unfold epsOf; have := nuOf_pos hkr hS hη hχ; positivity

theorem epsOf_le_one : epsOf kr S η χ ≤ 1 := by
  unfold epsOf
  have h1 := (nuOf_le_s : nuOf kr S η χ ≤ sExp kr S η / 8)
  have h2 := (sExp_lt_one : sExp kr S η < 1)
  linarith

theorem tolOf_pos (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) (hχ : 0 < χ) :
    0 < tolOf kr S η χ := by
  unfold tolOf; have := nuOf_pos hkr hS hη hχ; positivity

theorem wOf_nonneg (hkr : 0 ≤ kr) (hS : 0 < S) (hη : 0 < η) (hw : 0 ≤ w) :
    0 ≤ wOf kr S η w := by
  unfold wOf
  have := sExp_pos hkr hS hη
  have := angU_pos hη
  positivity

end Bounds

end
end Submission.Obl.k4_raw_localized_native_systems
