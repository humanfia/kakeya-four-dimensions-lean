/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/CommonDomains.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Lib.K4VelocityStrips.StripBins

/-!
# Literal common domains for true and projected labels

A domain records time, the two major coefficient bins, transverse velocity, and the
transverse position at the left endpoint of the recorded time cell. Its normalized
three-dimensional base retains the original major coordinate. All its incidences lie
in the ball of radius `1/8`, leaving the margins required by comparison and jitter.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

open Set MeasureTheory

noncomputable section

abbrev Code := Fin 5 → ℤ

def timeCenter (q : ℝ) (c : Code) : ℝ := (c 0 : ℝ) * q

/-- Time, major velocity, major intercept, transverse velocity, transverse position. -/
def code (q χ g m : ℝ) (b : Fin 6 → ℝ) (t : ℝ) : Code :=
  ![⌊t / q⌋, ⌊b 3 / χ⌋, ⌊b 0 / χ⌋, ⌊b 4 / g⌋,
    ⌊(b 1 + ((⌊t / q⌋ : ℤ) : ℝ) * q * b 4) / m⌋]

def majorCenter (χ : ℝ) (c : Code) (t : ℝ) : ℝ :=
  (c 2 : ℝ) * χ + t * ((c 1 : ℝ) * χ)

def minorCenter (q g m : ℝ) (c : Code) (t : ℝ) : ℝ :=
  (c 4 : ℝ) * m + (t - timeCenter q c) * ((c 3 : ℝ) * g)

/-- The comparison coordinates of the physical base `(t,Z,Y)`. -/
def coords (q χ g m : ℝ) (c : Code) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(z 0 - timeCenter q c) / (100 * q),
    (z 1 - majorCenter χ c (z 0)) / (100 * χ),
    (z 2 - minorCenter q g m c (z 0)) / (100 * m)]

def point (b : Fin 6 → ℝ) (t : ℝ) : Fin 3 → ℝ := ![t, b 0 + t * b 3, b 1 + t * b 4]

theorem measurable_code {α : Type*} [MeasurableSpace α] (b : α → Fin 6 → ℝ)
    (hb : Measurable b) (q χ g m : ℝ) :
    Measurable (fun p : α × ℝ => code q χ g m (b p.1) p.2) := by
  unfold code
  fun_prop

theorem time_error {q χ g m : ℝ} (hq : 0 < q) (b : Fin 6 → ℝ) (t : ℝ) :
    |t - timeCenter q (code q χ g m b t)| ≤ q := by
  simpa only [timeCenter, code, Matrix.cons_val_zero] using
    Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hq t

theorem timeCenter_mem_unit {q χ g m : ℝ} (hq : 0 < q) (b : Fin 6 → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    timeCenter q (code q χ g m b t) ∈ Icc (0 : ℝ) 1 := by
  have hf : (0 : ℤ) ≤ ⌊t / q⌋ := Int.floor_nonneg.mpr (div_nonneg ht.1 hq.le)
  have hf' : (0 : ℝ) ≤ (⌊t / q⌋ : ℝ) := by exact_mod_cast hf
  have hlo := (le_div_iff₀ hq).mp (Int.floor_le (t / q))
  constructor
  · simpa [timeCenter, code] using mul_nonneg hf' hq.le
  · simpa [timeCenter, code] using hlo.trans ht.2

theorem major_error {q χ g m : ℝ} (hχ : 0 < χ) (b : Fin 6 → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |(point b t) 1 - majorCenter χ (code q χ g m b t) t| ≤ 2 * χ := by
  have h₀ := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hχ (b 0)
  have h₃ := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hχ (b 3)
  have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hid : (point b t) 1 - majorCenter χ (code q χ g m b t) t =
      (b 0 - (⌊b 0 / χ⌋ : ℝ) * χ) + t * (b 3 - (⌊b 3 / χ⌋ : ℝ) * χ) := by
    simp [point, majorCenter, code]
    ring
  rw [hid]
  calc
    _ ≤ |b 0 - (⌊b 0 / χ⌋ : ℝ) * χ| + |t * (b 3 - (⌊b 3 / χ⌋ : ℝ) * χ)| := abs_add_le _ _
    _ ≤ χ + 1 * χ := by
      rw [abs_mul]
      exact add_le_add h₀ (mul_le_mul ht' h₃ (abs_nonneg _) zero_le_one)
    _ = _ := by ring

theorem minor_error {q χ g m : ℝ} (hq : 0 < q) (hg : 0 < g) (hm : 0 < m)
    (hqg : q * g ≤ m) (b : Fin 6 → ℝ) (t : ℝ) :
    |(point b t) 2 - minorCenter q g m (code q χ g m b t) t| ≤ 2 * m := by
  set c := code q χ g m b t
  have htime : |t - timeCenter q c| ≤ q := time_error hq b t
  have hslope := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hg (b 4)
  have hposition := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hm
    (b 1 + timeCenter q c * b 4)
  have hpos : |b 1 + timeCenter q c * b 4 - (c 4 : ℝ) * m| ≤ m := by
    simpa [c, code, timeCenter, mul_assoc] using hposition
  have hslo : |b 4 - (c 3 : ℝ) * g| ≤ g := by simpa [c, code] using hslope
  have hid : (point b t) 2 - minorCenter q g m c t =
      (b 1 + timeCenter q c * b 4 - (c 4 : ℝ) * m) +
      (t - timeCenter q c) * (b 4 - (c 3 : ℝ) * g) := by
    simp [point, minorCenter]
    ring
  change |(point b t) 2 - minorCenter q g m c t| ≤ _
  rw [hid]
  calc
    _ ≤ |b 1 + timeCenter q c * b 4 - (c 4 : ℝ) * m| +
        |(t - timeCenter q c) * (b 4 - (c 3 : ℝ) * g)| := abs_add_le _ _
    _ ≤ m + q * g := by rw [abs_mul]; gcongr
    _ ≤ 2 * m := by linarith

/-- Every actual occurrence has the strict stable margin required before jittering. -/
theorem coords_norm_le {q χ g m : ℝ} (hq : 0 < q) (hχ : 0 < χ) (hg : 0 < g)
    (hm : 0 < m) (hqg : q * g ≤ m) (b : Fin 6 → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖WithLp.toLp 2 (coords q χ g m (code q χ g m b t) (point b t))‖ ≤ (1 : ℝ) / 8 := by
  let z := coords q χ g m (code q χ g m b t) (point b t)
  have hz : ∀ i : Fin 3, |z i| ≤ 2 / 100 := by
    intro i
    fin_cases i
    · have h := time_error (χ := χ) (g := g) (m := m) hq b t
      dsimp [z, coords, point]
      rw [abs_div, abs_of_pos (by positivity : 0 < 100 * q)]
      exact (div_le_iff₀ (by positivity)).mpr (by linarith)
    · have h := major_error (q := q) (g := g) (m := m) hχ b ht
      change |(point b t) 1 - majorCenter χ (code q χ g m b t) t| ≤ _ at h
      change |((point b t) 1 - majorCenter χ (code q χ g m b t) t) / (100 * χ)| ≤ _
      rw [abs_div, abs_of_pos (by positivity : 0 < 100 * χ)]
      exact (div_le_iff₀ (by positivity)).mpr (by linarith)
    · have h := minor_error (χ := χ) hq hg hm hqg b t
      change |((point b t) 2 - minorCenter q g m (code q χ g m b t) t) / (100 * m)| ≤ _
      rw [abs_div, abs_of_pos (by positivity : 0 < 100 * m)]
      exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hs : ∀ i : Fin 3, z i ^ 2 ≤ (2 / 100 : ℝ) ^ 2 := by
    intro i
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (z i)) (hz i) 2
  have hn := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z)
  simp only [Fin.sum_univ_three] at hn
  change ‖WithLp.toLp 2 z‖ ≤ _
  nlinarith [hs 0, hs 1, hs 2, norm_nonneg (WithLp.toLp 2 z)]

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
