import Mathlib
import ChallengeDeps

open MeasureTheory Set Filter
open scoped ENNReal

/-!
# Native observations

These definitions abbreviate the maps in the frozen statement. The dyadic width is between
`N^(-r)` and `2 * N^(-r)`; the selected incidence measure has mass at most one.
-/

namespace Submission.Obl.k4_profile_density_bounds

abbrev Line := ℕ × (Fin 6 → ℝ)
abbrev State := Line × ℝ
abbrev Base := EuclideanSpace ℝ (Fin 3)
abbrev Velocity := EuclideanSpace ℝ (Fin 2)
abbrev Observation := (Base × ℤ) × (Fin 2 → ℤ)

def physical (p : State) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3,
    p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]

def base (p : State) : Base :=
  WithLp.toLp 2 ![p.2, p.1.2 0 + p.2 * p.1.2 3,
    p.1.2 1 + p.2 * p.1.2 4]

def velocity (l : Line) : Velocity := WithLp.toLp 2 ![l.2 3, l.2 4]

def hidden (p : State) : ℝ := p.1.2 2 + p.2 * p.1.2 5

noncomputable def width (N r : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(⌊r * Real.log N / Real.log 2⌋ : ℤ))

noncomputable def observe (N r u : ℝ) (p : State) : Observation :=
  ((base p, ⌊hidden p / width N r⌋), fun j => ⌊velocity p.1 j / width N u⌋)

noncomputable def reference : Measure Observation :=
  (volume.prod Measure.count).prod Measure.count

noncomputable def selected (ν : Measure Line) (E : Set State) : Measure State :=
  (ν.prod volume).restrict E

lemma measurable_physical : Measurable physical := by
  unfold physical
  fun_prop

lemma measurable_base : Measurable base := by
  unfold base
  fun_prop

lemma measurable_velocity : Measurable velocity := by
  unfold velocity
  fun_prop

lemma measurable_hidden : Measurable hidden := by
  unfold hidden
  fun_prop

lemma measurable_observe (N r u : ℝ) : Measurable (observe N r u) := by
  unfold observe base hidden velocity
  fun_prop

lemma width_pos (N r : ℝ) : 0 < width N r := by
  unfold width
  positivity

lemma width_zero (N : ℝ) : width N 0 = 1 := by
  simp [width]

lemma width_bounds {N : ℝ} (hN : 0 < N) (r : ℝ) :
    N ^ (-r) ≤ width N r ∧ width N r ≤ 2 * N ^ (-r) := by
  have h2 : (1 : ℝ) ≤ 2 := by norm_num
  have hl2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  let x := r * Real.log N / Real.log 2
  have hid : (2 : ℝ) ^ (-x) = N ^ (-r) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hN]
    congr 1
    dsimp [x]
    field_simp
  have hw : width N r = (2 : ℝ) ^ (-(⌊x⌋ : ℝ)) := by
    change (2 : ℝ) ^ (-(⌊x⌋ : ℤ)) = (2 : ℝ) ^ (-(⌊x⌋ : ℝ))
    rw [← Real.rpow_intCast]
    simp only [Int.cast_neg]
  rw [hw, ← hid]
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le h2 (neg_le_neg (Int.floor_le x))
  · calc
      (2 : ℝ) ^ (-(⌊x⌋ : ℝ)) ≤ (2 : ℝ) ^ (1 + -x) :=
        Real.rpow_le_rpow_of_exponent_le h2 (by linarith [Int.lt_floor_add_one x])
      _ = 2 * (2 : ℝ) ^ (-x) := by rw [Real.rpow_add (by norm_num)]; simp

lemma selected_le (ν : Measure Line) (E : Set State) :
    selected ν E ≤ ν.prod volume := Measure.restrict_le_self

lemma selected_mass_le_one (ν : Measure Line) [IsProbabilityMeasure ν]
    (E : Set State) (hE : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    selected ν E univ ≤ 1 := by
  rw [selected, Measure.restrict_apply_univ]
  calc
    (ν.prod volume) E ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hE
    _ = 1 := by simp [Measure.prod_prod]

end Submission.Obl.k4_profile_density_bounds
