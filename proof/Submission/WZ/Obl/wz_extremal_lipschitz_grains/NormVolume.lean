-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NormVolume.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormCovering
import Submission.WZ.Obl.wz_grains_nonsingular_slices.ShearFubini

/-!
# Volume from covered twisted slices

If every twisted slice of a measurable subset of the unit ball is covered at resolution `d`
with exponent `α ≤ 1` and constant `C`, the set has volume at most `32 C d ^ (1 - α)`, for any
continuous slope. The grain fibres have length at most `2 / max 1 |f z|`, which compensates the
length `2 (1 + |f z|)` of the interval containing the slice.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_grains_nonsingular_slices (grainFib ofTwist ofTwist_zero ofTwist_one
  ofTwist_two volume_eq_lintegral_grainFib)

/-- A covered subset of an interval of length `R` has measure at most `2 d C (R / d) ^ α`. -/
theorem volume_le_of_covering {d α C R a : ℝ} {B : Set ℝ} (h : Covering d α C B) (hd : 0 < d)
    (hdR : d ≤ R) (hB : B ⊆ Icc a (a + R)) :
    volume B ≤ ENNReal.ofReal (2 * d * (C * (R / d) ^ α)) := by
  obtain ⟨m, c, hc, hm⟩ := h d R a le_rfl hdR
  have hsub : B ⊆ ⋃ j, closedBall (c j) d := fun u hu => hc ⟨hu, hB hu⟩
  calc volume B ≤ volume (⋃ j, closedBall (c j) d) := measure_mono hsub
    _ ≤ ∑ j, volume (closedBall (c j) d) := measure_iUnion_fintype_le _ _
    _ = ∑ _j : Fin m, ENNReal.ofReal (2 * d) := by simp [Real.volume_closedBall]
    _ = ENNReal.ofReal ((m : ℝ) * (2 * d)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * d * (C * (R / d) ^ α)) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith

theorem grainFib_subset_Ioo {f : ℝ → ℝ} {A : Set Space} (hA : A ⊆ ball 0 1) (u z : ℝ) :
    grainFib f A u z ⊆ Ioo (-1) 1 := by
  intro y hy
  have h := coord_mem_Icc_of_mem_ball (hA hy) 1
  have hb : ‖ofTwist f u y z‖ < 1 := by simpa using hA hy
  have hc : |(ofTwist f u y z) 1| ≤ ‖ofTwist f u y z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (ofTwist f u y z) 1
  rw [ofTwist_one] at hc
  exact abs_lt.mp (hc.trans_lt hb)

theorem volume_grainFib_le {f : ℝ → ℝ} {A : Set Space} (hA : A ⊆ ball 0 1) (u z : ℝ) :
    volume (grainFib f A u z) ≤ ENNReal.ofReal (2 / max 1 |f z|) := by
  rcases le_total |f z| 1 with hf | hf
  · rw [max_eq_left hf]
    calc volume (grainFib f A u z) ≤ volume (Ioo (-1 : ℝ) 1) :=
          measure_mono (grainFib_subset_Ioo hA u z)
      _ = ENNReal.ofReal (2 / 1) := by rw [Real.volume_Ioo]; norm_num
  · rw [max_eq_right hf]
    have hpos : 0 < |f z| := by linarith
    have hsub : grainFib f A u z ⊆ (fun y => f z * y) ⁻¹' Ioo (u - 1) (u + 1) := by
      intro y hy
      have hb : ‖ofTwist f u y z‖ < 1 := by simpa using hA hy
      have hc : |(ofTwist f u y z) 0| ≤ ‖ofTwist f u y z‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (ofTwist f u y z) 0
      rw [ofTwist_zero] at hc
      obtain ⟨h1, h2⟩ := abs_lt.mp (hc.trans_lt hb)
      simp only [mem_preimage, mem_Ioo]
      constructor <;> linarith
    calc volume (grainFib f A u z) ≤ volume ((fun y => f z * y) ⁻¹' Ioo (u - 1) (u + 1)) :=
          measure_mono hsub
      _ = ENNReal.ofReal (|f z|⁻¹) * volume (Ioo (u - 1) (u + 1)) := by
          rw [Real.volume_preimage_mul_left (abs_pos.mp hpos), abs_inv]
      _ = ENNReal.ofReal (2 / |f z|) := by
          rw [Real.volume_Ioo, ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
          congr 1
          field_simp
          ring

theorem projectedSlice_subset_Icc {f : ℝ → ℝ} {A : Set Space} (hA : A ⊆ ball 0 1) (z : ℝ) :
    projectedSlice f A z ⊆ Icc (-(1 + |f z|)) (-(1 + |f z|) + 2 * (1 + |f z|)) := by
  rintro u ⟨p, hp, he⟩
  simp only [Prod.mk.injEq] at he
  obtain ⟨hu, hz⟩ := he
  have h0 := coord_mem_Icc_of_mem_ball (hA hp) 0
  have h1 := coord_mem_Icc_of_mem_ball (hA hp) 1
  have hfz : |f (p 2) * p 1| ≤ |f z| := by
    rw [hz, abs_mul]
    have : |p 1| ≤ 1 := abs_le.mpr h1
    nlinarith [abs_nonneg (f z)]
  rw [← hu]
  obtain ⟨h3, h4⟩ := abs_le.mp hfz
  constructor <;> linarith [h0.1, h0.2]

theorem slice_bound {d α C t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hC : 0 ≤ C) (ht : 0 ≤ t) :
    2 / max 1 t * (2 * d * (C * (2 * (1 + t) / d) ^ α)) ≤ 16 * C * d ^ (1 - α) := by
  set M := max 1 t with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMt : t ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hR : 2 * (1 + t) / d ≤ 4 * M / d := by
    apply div_le_div_of_nonneg_right _ hd.le; linarith
  have hpow : (2 * (1 + t) / d) ^ α ≤ 4 * M / d ^ α := by
    calc (2 * (1 + t) / d) ^ α ≤ (4 * M / d) ^ α :=
          Real.rpow_le_rpow (by positivity) hR hα0
      _ = (4 * M) ^ α / d ^ α := Real.div_rpow (by positivity) hd.le _
      _ ≤ (4 * M) ^ (1 : ℝ) / d ^ α := by
          apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) hα1
      _ = 4 * M / d ^ α := by rw [Real.rpow_one]
  have hdα : d / d ^ α = d ^ (1 - α) := by
    rw [Real.rpow_sub hd, Real.rpow_one]
  have hdαpos : 0 < d ^ α := Real.rpow_pos_of_pos hd _
  calc 2 / M * (2 * d * (C * (2 * (1 + t) / d) ^ α)) ≤
        2 / M * (2 * d * (C * (4 * M / d ^ α))) := by
        gcongr
    _ = 16 * C * (d / d ^ α) := by field_simp; ring
    _ = 16 * C * d ^ (1 - α) := by rw [hdα]

/-- Covered twisted slices bound the volume. -/
theorem volume_le_of_slices {f : ℝ → ℝ} (hf : Continuous f) {A : Set Space}
    (hAm : MeasurableSet A) (hA : A ⊆ ball 0 1) {d α C : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hcov : ∀ z : ℝ, z ∈ Icc (-1) 1 → Covering d α C (projectedSlice f A z)) :
    volume A ≤ ENNReal.ofReal (32 * C * d ^ (1 - α)) := by
  rw [volume_eq_lintegral_grainFib hf hAm]
  have hz : ∀ z : ℝ, ∫⁻ u, volume (grainFib f A u z) ≤
      (Icc (-1 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (16 * C * d ^ (1 - α))) z := by
    intro z
    by_cases hzI : z ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hzI]
      have hpt : ∀ u, volume (grainFib f A u z) ≤
          (projectedSlice f A z).indicator (fun _ => ENNReal.ofReal (2 / max 1 |f z|)) u := by
        intro u
        by_cases hu : u ∈ projectedSlice f A z
        · rw [indicator_of_mem hu]; exact volume_grainFib_le hA u z
        · rw [indicator_of_notMem hu]
          have h0 : grainFib f A u z = ∅ := by
            ext y
            simp only [mem_empty_iff_false, iff_false]
            intro hy
            apply hu
            refine ⟨ofTwist f u y z, hy, ?_⟩
            simp [ofTwist_zero, ofTwist_one, ofTwist_two]
          rw [h0, measure_empty]
      calc ∫⁻ u, volume (grainFib f A u z) ≤
            ∫⁻ u, (projectedSlice f A z).indicator
              (fun _ => ENNReal.ofReal (2 / max 1 |f z|)) u := lintegral_mono hpt
        _ ≤ ENNReal.ofReal (2 / max 1 |f z|) * volume (projectedSlice f A z) :=
            lintegral_indicator_const_le _ _
        _ ≤ ENNReal.ofReal (2 / max 1 |f z|) *
              ENNReal.ofReal (2 * d * (C * (2 * (1 + |f z|) / d) ^ α)) := by
            gcongr
            exact volume_le_of_covering (hcov z hzI) hd
              (by nlinarith [abs_nonneg (f z)]) (projectedSlice_subset_Icc hA z)
        _ = ENNReal.ofReal (2 / max 1 |f z| *
              (2 * d * (C * (2 * (1 + |f z|) / d) ^ α))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (16 * C * d ^ (1 - α)) :=
            ENNReal.ofReal_le_ofReal (slice_bound hd hd1 hα0 hα1 hC (abs_nonneg _))
    · rw [indicator_of_notMem hzI]
      have h0 : ∀ u, grainFib f A u z = ∅ := by
        intro u
        ext y
        simp only [mem_empty_iff_false, iff_false]
        intro hy
        apply hzI
        have := coord_mem_Icc_of_mem_ball (hA hy) 2
        rwa [ofTwist_two] at this
      simp [h0]
  calc ∫⁻ z, ∫⁻ u, volume (grainFib f A u z) ≤
        ∫⁻ z, (Icc (-1 : ℝ) 1).indicator
          (fun _ => ENNReal.ofReal (16 * C * d ^ (1 - α))) z := lintegral_mono hz
    _ = ENNReal.ofReal (16 * C * d ^ (1 - α)) * volume (Icc (-1 : ℝ) 1) :=
        lintegral_indicator_const measurableSet_Icc _
    _ = ENNReal.ofReal (32 * C * d ^ (1 - α)) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
