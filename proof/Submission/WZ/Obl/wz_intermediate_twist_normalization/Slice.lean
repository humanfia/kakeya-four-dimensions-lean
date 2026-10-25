-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_intermediate_twist_normalization.Slice.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_intermediate_twist_normalization.Saturate

/-!
# Volumes of tube slabs and fibres over planar sets

* `volume_tube_band_le`: a transverse `δ`-tube meets the horizontal band of heights `[a, b]`
  in volume at most `72 δ² (b - a)` (computed with the fibres of the untwisted projection
  `(x, y, z) ↦ (x + y, z)`).
* `fib_inter_pmap_preimage`: fibres of `A ∩ P_f⁻¹ S` are the fibres of `A` over `S`.
-/

namespace WangZahlLot.Obl.wz_intermediate_twist_normalization

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_small_twist_projection_estimate (Space tube fib measurable_fib
  volume_eq_lintegral_fib volume_grainFib_tube_le abs_sub_ctr_le_of_grainFib ctr)
open WangZahlLot.Obl.wz_grains_nonsingular_slices (ofTwist grainFib ofTwist_zero ofTwist_one
  ofTwist_two grainFib_mono)

/-- A set whose fibres are short and localized has small volume. -/
theorem volume_le_of_fib {f : ℝ → ℝ} (hf : Continuous f) {A : Set Space}
    (hA : MeasurableSet A) {Zs : Set ℝ} {ℓ w : ℝ} (hℓ : 0 ≤ ℓ) {φ : ℝ → ℝ}
    (hfib : ∀ u z, volume (grainFib f A u z) ≤ ENNReal.ofReal ℓ)
    (hloc : ∀ u z, (grainFib f A u z).Nonempty → z ∈ Zs ∧ |u - φ z| ≤ w) :
    volume A ≤ ENNReal.ofReal (ℓ * (2 * w)) * volume Zs := by
  rw [volume_eq_lintegral_fib hf hA, Measure.volume_eq_prod,
    lintegral_prod_symm' _ (measurable_fib hf hA)]
  calc ∫⁻ z, ∫⁻ u, fib f A (u, z)
      ≤ ∫⁻ z, Zs.indicator (fun _ => ENNReal.ofReal (ℓ * (2 * w))) z := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z ∈ Zs
        · rw [indicator_of_mem hz]
          calc ∫⁻ u, fib f A (u, z)
              ≤ ∫⁻ u, (closedBall (φ z) w).indicator (fun _ => ENNReal.ofReal ℓ) u := by
                refine lintegral_mono fun u => ?_
                by_cases hne : (grainFib f A u z).Nonempty
                · have hu : u ∈ closedBall (φ z) w := by
                    rw [mem_closedBall, Real.dist_eq]
                    exact (hloc u z hne).2
                  rw [indicator_of_mem hu]
                  exact hfib u z
                · rw [Set.not_nonempty_iff_eq_empty] at hne
                  simp [fib, hne]
            _ = ENNReal.ofReal ℓ * volume (closedBall (φ z) w) :=
                lintegral_indicator_const measurableSet_closedBall _
            _ ≤ ENNReal.ofReal (ℓ * (2 * w)) := by
                rw [Real.volume_closedBall, ← ENNReal.ofReal_mul hℓ]
        · rw [indicator_of_notMem hz]
          have h0 : ∀ u, fib f A (u, z) = 0 := by
            intro u
            by_contra hne
            have : (grainFib f A u z).Nonempty := by
              by_contra he
              rw [Set.not_nonempty_iff_eq_empty] at he
              exact hne (by simp [fib, he])
            exact hz (hloc u z this).1
          simp [h0]
    _ ≤ ENNReal.ofReal (ℓ * (2 * w)) * volume Zs := lintegral_indicator_const_le _ _

/-- The horizontal band of heights `[a, b]`. -/
def hband (a b : ℝ) : Set Space := {p | a ≤ p 2 ∧ p 2 ≤ b}

theorem measurableSet_hband (a b : ℝ) : MeasurableSet (hband a b) := by
  have h2 : Continuous fun p : Space => p 2 := by fun_prop
  exact (measurableSet_le measurable_const h2.measurable).inter
    (measurableSet_le h2.measurable measurable_const)

/-- **Volume of a tube in a horizontal band.** -/
theorem volume_tube_band_le {δ : ℝ} (hδ : 0 < δ) {x v : Space} (hv : ‖v‖ = 1)
    (hv2 : (1 / 2 : ℝ) ≤ |v 2|) {a b : ℝ} (hab : a ≤ b) :
    volume (tube δ x v ∩ hband a b) ≤ ENNReal.ofReal (72 * δ ^ 2 * (b - a)) := by
  set f : ℝ → ℝ := fun _ => 1 with hfdef
  have hfc : Continuous f := continuous_const
  have hm : MeasurableSet (tube δ x v ∩ hband a b) :=
    isOpen_thickening.measurableSet.inter (measurableSet_hband a b)
  have hfib : ∀ u z, volume (grainFib f (tube δ x v ∩ hband a b) u z) ≤
      ENNReal.ofReal (6 * δ) := by
    intro u z
    have h := volume_grainFib_tube_le (δ := δ) (x := x) (f := f) (u := u) (z := z) hv hv2
      one_pos (by simp [hfdef])
    rw [div_one] at h
    exact (measure_mono (grainFib_mono inter_subset_left u z)).trans h
  have hloc : ∀ u z, (grainFib f (tube δ x v ∩ hband a b) u z).Nonempty →
      z ∈ Icc a b ∧ |u - ctr f x v z| ≤ 6 * δ := by
    intro u z hne
    obtain ⟨y, hy⟩ := hne
    have hb := hy.2
    simp only [hband, mem_setOf_eq, ofTwist_two] at hb
    refine ⟨hb, ?_⟩
    have := abs_sub_ctr_le_of_grainFib (M := 1) hv hv2 (by simp [hfdef]) ⟨y, hy.1⟩
    linarith
  have h := volume_le_of_fib hfc hm (by positivity) hfib hloc
  rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  ring

/-- Fibres of `A ∩ P_f⁻¹ S` are the fibres of `A` over `S`. -/
theorem fib_inter_pmap_preimage (f : ℝ → ℝ) (A : Set Space) (S : Set (ℝ × ℝ)) (q : ℝ × ℝ) :
    fib f (A ∩ pmap f ⁻¹' S) q = S.indicator (fib f A) q := by
  by_cases hq : q ∈ S
  · rw [indicator_of_mem hq]
    simp only [fib]
    congr 1
    ext y
    simp only [grainFib, mem_setOf_eq, mem_inter_iff, mem_preimage, pmap_ofTwist]
    exact ⟨fun h => h.1, fun h => ⟨h, hq⟩⟩
  · rw [indicator_of_notMem hq]
    simp only [fib]
    have : grainFib f (A ∩ pmap f ⁻¹' S) q.1 q.2 = ∅ := by
      ext y
      simp only [grainFib, mem_setOf_eq, mem_inter_iff, mem_preimage, pmap_ofTwist,
        mem_empty_iff_false, iff_false, not_and]
      intro _
      exact hq
    rw [this, measure_empty]

/-- The volume of `A ∩ P_f⁻¹ S` as an integral over `S`. -/
theorem volume_inter_pmap_preimage {f : ℝ → ℝ} (hf : Continuous f) {A : Set Space}
    (hA : MeasurableSet A) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) :
    volume (A ∩ pmap f ⁻¹' S) = ∫⁻ q, S.indicator (fib f A) q := by
  have hm : MeasurableSet (A ∩ pmap f ⁻¹' S) :=
    hA.inter (hS.preimage (continuous_pmap hf).measurable)
  rw [volume_eq_lintegral_fib hf hm]
  exact lintegral_congr fun q => fib_inter_pmap_preimage f A S q

end WangZahlLot.Obl.wz_intermediate_twist_normalization
