-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.TransLemmas.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Saturate

/-!
# Horizontal translates and the trivial projection bound

* A horizontal translation `p ↦ p + s` (`s 2 = 0`) moves the projection `P_f` by the
  measure-preserving map `(u, z) ↦ (u + s 0 + f(z) s 1, z)`, so it does not increase the area of
  projections (`volume_proj_translate_le`).
* A measurable subset of a transverse `ρ`-tube has volume at most `6 ρ` times the area of its
  projection (`volume_le_proj`), since the fibres of `P_f` cross the tube within `6 ρ`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube proj fib measurable_fib
  volume_eq_lintegral_fib fib_eq_zero_of_notMem norm_sub_lt_of_same_height coord_abs_le)
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib ofTwist_zero ofTwist_one
  ofTwist_two grainFib_mono)

/-- The planar shear induced by a horizontal translation. -/
def pshift (f : ℝ → ℝ) (s : Space) (q : ℝ × ℝ) : ℝ × ℝ := (q.1 + s 0 + f q.2 * s 1, q.2)

theorem continuous_pshift {f : ℝ → ℝ} (hf : Continuous f) (s : Space) :
    Continuous (pshift f s) := by
  unfold pshift
  fun_prop

/-- The planar shear preserves area of measurable sets. -/
theorem volume_pshift_preimage {f : ℝ → ℝ} (hf : Continuous f) (s : Space) {G : Set (ℝ × ℝ)}
    (hG : MeasurableSet G) : volume (pshift f s ⁻¹' G) = volume G := by
  have hm : MeasurableSet (pshift f s ⁻¹' G) := hG.preimage (continuous_pshift hf s).measurable
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hm, Measure.prod_apply_symm hG]
  refine lintegral_congr fun z => ?_
  have he : (fun u => (u, z)) ⁻¹' (pshift f s ⁻¹' G) =
      (fun u => u + (s 0 + f z * s 1)) ⁻¹' ((fun u => (u, z)) ⁻¹' G) := by
    ext u; simp [pshift, add_assoc]
  rw [he, measure_preimage_add_right]

/-- The planar shear does not increase outer area. -/
theorem volume_pshift_preimage_le {f : ℝ → ℝ} (hf : Continuous f) (s : Space) (G : Set (ℝ × ℝ)) :
    volume (pshift f s ⁻¹' G) ≤ volume G := by
  calc volume (pshift f s ⁻¹' G) ≤ volume (pshift f s ⁻¹' toMeasurable volume G) :=
        measure_mono (preimage_mono (subset_toMeasurable _ _))
    _ = volume (toMeasurable volume G) := volume_pshift_preimage hf s (measurableSet_toMeasurable _ _)
    _ = volume G := measure_toMeasurable _

/-- The projection of a horizontal translate. -/
theorem proj_translate_subset (f : ℝ → ℝ) {s : Space} (hs : s 2 = 0) (E : Set Space) :
    proj f ((fun p => p - s) ⁻¹' E) ⊆ pshift f (-s) ⁻¹' proj f E := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨p - s, hp, ?_⟩
  simp only [pshift, PiLp.sub_apply, PiLp.neg_apply, hs, sub_zero]
  ext <;> simp <;> ring

/-- **Translates do not increase projected areas.** -/
theorem volume_proj_translate_le {f : ℝ → ℝ} (hf : Continuous f) {s : Space} (hs : s 2 = 0)
    (E : Set Space) : volume (proj f ((fun p => p - s) ⁻¹' E)) ≤ volume (proj f E) :=
  (measure_mono (proj_translate_subset f hs E)).trans (volume_pshift_preimage_le hf _ _)

/-- Translates of tubes. -/
theorem tube_translate (ρ : ℝ) (x v s : Space) :
    tube ρ (x + s) v = (fun p => p - s) ⁻¹' tube ρ x v := by
  ext p
  simp only [mem_preimage]
  rw [WangZahlLot.Obl.wz_compact_offset_normalization.mem_tube_iff,
    WangZahlLot.Obl.wz_compact_offset_normalization.mem_tube_iff]
  constructor
  · rintro ⟨t, ht, hd⟩
    refine ⟨t, ht, ?_⟩
    rwa [dist_eq_norm, show p - s - (x + t • v) = p - (x + s + t • v) by abel, ← dist_eq_norm]
  · rintro ⟨t, ht, hd⟩
    refine ⟨t, ht, ?_⟩
    rwa [dist_eq_norm, show p - (x + s + t • v) = p - s - (x + t • v) by abel, ← dist_eq_norm]

/-- Fibres of a subset of a transverse tube have length at most `6 ρ`, for every slope. -/
theorem volume_grainFib_le_six {ρ : ℝ} {x v : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) (f : ℝ → ℝ) {A : Set Space} (hA : A ⊆ tube ρ x v) (u z : ℝ) :
    volume (grainFib f A u z) ≤ ENNReal.ofReal (6 * ρ) := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun y hy y' hy' => ?_)
  have h := norm_sub_lt_of_same_height hv hv2 (hA hy) (hA hy') (by simp only [ofTwist_two])
  have h1 := coord_abs_le (ofTwist f u y z - ofTwist f u y' z) 1
  rw [PiLp.sub_apply, ofTwist_one, ofTwist_one] at h1
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The trivial projection bound.** -/
theorem volume_le_proj {ρ : ℝ} {x v : Space} (hv : ‖v‖ = 1) (hv2 : (1 / 2 : ℝ) ≤ |v 2|)
    {f : ℝ → ℝ} (hf : Continuous f) {A : Set Space} (hAm : MeasurableSet A)
    (hA : A ⊆ tube ρ x v) :
    volume A ≤ ENNReal.ofReal (6 * ρ) * volume (proj f A) := by
  set G := toMeasurable volume (proj f A) with hGdef
  have hGm : MeasurableSet G := measurableSet_toMeasurable _ _
  rw [volume_eq_lintegral_fib hf hAm, ← measure_toMeasurable (proj f A), ← hGdef,
    ← lintegral_indicator_const hGm]
  refine lintegral_mono fun q => ?_
  by_cases hq : q ∈ G
  · rw [indicator_of_mem hq]
    exact volume_grainFib_le_six hv hv2 f hA q.1 q.2
  · rw [indicator_of_notMem hq, fib_eq_zero_of_notMem]
    intro hq'
    exact hq (subset_toMeasurable _ _ hq')

end WangZahlLot.Obl.wz_intermediate_twist_normalization
