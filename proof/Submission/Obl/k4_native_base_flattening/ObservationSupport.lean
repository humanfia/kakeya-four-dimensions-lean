import Submission.Lib.K4PolynomialGeometry.Frame
import Submission.Obl.k4_scalar_lift_plank.Cells
import Submission.Obl.k4_matching_homogeneous_records.Offsets
import Submission.Obl.k4_profile_density_bounds.Common
import Submission.Obl.k4_native_base_flattening.Powers

namespace Submission.Obl.k4_native_base_flattening

open MeasureTheory Set
open Submission.Obl.k4_profile_density_bounds
open Submission.Lib.K4PolynomialGeometry
open scoped ENNReal

/-- A finite interval containing the integer bin of every point in `[-T,T]`. -/
noncomputable def cubeBins (T a : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈T / a + 1⌉) ⌈T / a + 1⌉

lemma mem_cubeBins {T a x : ℝ} (ha : 0 < a) (hx : |x| ≤ T) :
    ⌊x / a⌋ ∈ cubeBins T a := by
  have hf : |(⌊x / a⌋ : ℝ)| ≤ |x / a| + 1 := by
    simpa using Submission.Obl.k4_matching_homogeneous_records.floor_sub_bound (x / a) 0
  have hdiv : |x / a| ≤ T / a := by
    rw [abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right hx ha.le
  have hi : |(⌊x / a⌋ : ℤ)| ≤ ⌈T / a + 1⌉ := by
    exact_mod_cast (hf.trans (by linarith) |>.trans (Int.le_ceil (T / a + 1)))
  exact Finset.mem_Icc.mpr (abs_le.mp hi)

lemma card_cubeBins_le {T a : ℝ} (hT : 0 ≤ T) (ha : 0 < a) :
    ((cubeBins T a).card : ℝ) ≤ 2 * T / a + 5 := by
  have hh := Submission.Obl.k4_scalar_lift_plank.card_ceil_interval_le
    (show 0 ≤ T / a + 1 by positivity)
  change ((Finset.Icc (-⌈T / a + 1⌉) ⌈T / a + 1⌉).card : ℝ) ≤ _
  convert hh using 1 <;> ring

noncomputable def cubeVelocityBins (T b : ℝ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun _ => cubeBins T b

lemma card_cubeVelocityBins_le {T b : ℝ} (hT : 0 ≤ T) (hb : 0 < b) :
    ((cubeVelocityBins T b).card : ℝ) ≤ (2 * T / b + 5) ^ 2 := by
  have heq : (cubeVelocityBins T b).card = (cubeBins T b).card ^ 2 := by
    simp [cubeVelocityBins, Fintype.card_piFinset]
  rw [heq, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (card_cubeBins_le hT hb) _

/-- A finite-reference-volume set containing the observation of a bounded chart cube. -/
noncomputable def cubeObservationSupport (T a b : ℝ) : Set Observation :=
  ((coordinateCube T) ×ˢ (cubeBins T a : Set ℤ)) ×ˢ
    (cubeVelocityBins T b : Set (Fin 2 → ℤ))

lemma measurableSet_cubeObservationSupport (T a b : ℝ) :
    MeasurableSet (cubeObservationSupport T a b) := by
  have hbase : MeasurableSet (coordinateCube (n := 3) T) :=
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc).preimage (by fun_prop)
  exact (hbase.prod (cubeBins T a).measurableSet).prod (cubeVelocityBins T b).measurableSet

/-- Observation in the chart coordinates `(t,y1,y2,w,s1,s2,s3)`. -/
noncomputable def chartObservation (a b : ℝ) (x : Fin 7 → ℝ) : Observation :=
  ((WithLp.toLp 2 ![x 0, x 1, x 2], ⌊x 3 / a⌋), ![⌊x 4 / b⌋, ⌊x 5 / b⌋])

lemma mem_cubeObservationSupport {T a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x : Fin 7 → ℝ) (hx : ∀ i, |x i| ≤ T) :
    chartObservation a b x ∈ cubeObservationSupport T a b := by
  refine ⟨⟨?_, mem_cubeBins ha (hx 3)⟩, ?_⟩
  · change ∀ i ∈ (univ : Set (Fin 3)), -T ≤ ![x 0, x 1, x 2] i ∧
      ![x 0, x 1, x 2] i ≤ T
    intro i _
    fin_cases i
    · exact abs_le.mp (hx 0)
    · exact abs_le.mp (hx 1)
    · exact abs_le.mp (hx 2)
  · change ![⌊x 4 / b⌋, ⌊x 5 / b⌋] ∈ Fintype.piFinset (fun _ : Fin 2 => cubeBins T b)
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i
    · exact mem_cubeBins hb (hx 4)
    · exact mem_cubeBins hb (hx 5)

lemma reference_cubeObservationSupport_le {T a b : ℝ}
    (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 < b) :
    reference (cubeObservationSupport T a b) ≤
      ENNReal.ofReal ((2 * T) ^ 3 * (2 * T / a + 5) * (2 * T / b + 5) ^ 2) := by
  have hca : ((cubeBins T a).card : ENNReal) ≤ ENNReal.ofReal (2 * T / a + 5) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_cubeBins_le hT ha)
  have hcb : ((cubeVelocityBins T b).card : ENNReal) ≤
      ENNReal.ofReal ((2 * T / b + 5) ^ 2) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (card_cubeVelocityBins_le hT hb)
  unfold reference cubeObservationSupport
  rw [Measure.prod_prod, Measure.prod_prod, volume_coordinateCube hT]
  simp only [Measure.count_apply_finset]
  calc
    _ ≤ ENNReal.ofReal ((2 * T) ^ 3) * ENNReal.ofReal (2 * T / a + 5) *
        ENNReal.ofReal ((2 * T / b + 5) ^ 2) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]

/-- The reference support of all observations in a bounded depth rectangle has one
polynomial volume bound. The natural numbers `d,e` are any upper bounds for the depths. -/
lemma reference_cubeObservationSupport_power_le (B d e : ℕ) {n r u : ℝ}
    (hn : 2 ≤ n) (hr : 0 ≤ r) (hrd : r ≤ (d : ℝ))
    (hu : 0 ≤ u) (hue : u ≤ (e : ℝ)) :
    reference (cubeObservationSupport (n ^ B) (width n r) (width n u)) ≤
      ENNReal.ofReal (n ^ (6 * B + d + 2 * e + 12)) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hdiv (s : ℝ) (j : ℕ) (hs : s ≤ (j : ℝ)) :
      n ^ B / width n s ≤ n ^ (B + j) := by
    have hmin : (n ^ j)⁻¹ ≤ width n s := by
      have hp : n ^ (-(j : ℝ)) ≤ width n s :=
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)).trans (width_bounds hn0 s).1
      simpa only [Real.rpow_neg hn0.le, Real.rpow_natCast] using hp
    have hinv : (width n s)⁻¹ ≤ n ^ j := by
      apply (inv_le_iff_one_le_mul₀ (width_pos n s)).2
      simpa only [mul_comm] using
        (inv_le_iff_one_le_mul₀ (pow_pos hn0 j)).1 hmin
    calc
      _ = n ^ B * (width n s)⁻¹ := div_eq_mul_inv _ _
      _ ≤ n ^ B * n ^ j := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := (pow_add _ _ _).symm
  have hbin (s : ℝ) (j : ℕ) (hs : s ≤ (j : ℝ)) :
      2 * n ^ B / width n s + 5 ≤ 7 * n ^ (B + j) := by
    have hh := hdiv s j hs
    have hp : 1 ≤ n ^ (B + j) := one_le_pow₀ hn1
    rw [mul_div_assoc]
    linarith
  refine (reference_cubeObservationSupport_le (by positivity) (width_pos n r)
    (width_pos n u)).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ (2 * n ^ B) ^ 3 * (7 * n ^ (B + d)) * (7 * n ^ (B + e)) ^ 2 := by
      gcongr
      · exact hbin r d hrd
      · exact add_nonneg (div_nonneg (by positivity) (width_pos n u).le) (by norm_num)
      · exact hbin u e hue
    _ = 2744 * n ^ (6 * B + d + 2 * e) := by
      simp only [show 6 * B = B * 6 by omega, show 2 * e = e * 2 by omega,
        pow_add, pow_mul]
      ring
    _ ≤ _ := Submission.Obl.k4_real_conic_restoration.absorb_constant hn (by norm_num)

end Submission.Obl.k4_native_base_flattening
