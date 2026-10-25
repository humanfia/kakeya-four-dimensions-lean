-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_sticky_twisted_extraction.Slices.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_sticky_twisted_extraction.Compact

namespace WangZahlLot.Obl.wz_sticky_twisted_extraction

open Set Metric MeasureTheory
open scoped ENNReal

/-- Horizontal sections of the twisted image, as subsets of the real line. -/
def projectedSlice (f : ℝ → ℝ) (E : Set Space) (z : ℝ) : Set ℝ :=
  {u | (u, z) ∈ TwistedProjection f '' E}

/-- The vertical support of the image is bounded by the ambient unit ball. -/
theorem projectedSlice_eq_empty {f : ℝ → ℝ} {E : Set Space}
    (hE : E ⊆ ball 0 1) {z : ℝ} (hz : z ∉ Icc (-1) 1) :
    projectedSlice f E z = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨p, hp, hpu⟩ := hu
  have hpz : p 2 = z := congrArg Prod.snd hpu
  have hn : ‖p‖ < 1 := by simpa using hE hp
  have habs : |z| ≤ ‖p‖ := by
    rw [← hpz]
    exact PiLp.norm_apply_le p 2
  have hz' : z ∈ Icc (-1) 1 := by
    have hh := abs_le.mp (habs.trans hn.le)
    exact hh
  exact hz hz'

/-- A measurable bounded planar set is controlled by a uniform bound on its
horizontal sections. The bound uses the exact length of `[-1,1]`. -/
theorem planar_volume_le_of_slices {A : Set (ℝ × ℝ)} (hm : MeasurableSet A)
    {c : ENNReal}
    (hsupport : ∀ z : ℝ, z ∉ Icc (-1) 1 → (fun u : ℝ => (u, z)) ⁻¹' A = ∅)
    (hslice : ∀ z : ℝ, z ∈ Icc (-1) 1 →
      volume ((fun u : ℝ => (u, z)) ⁻¹' A) ≤ c) :
    volume A ≤ c * 2 := by
  change (volume.prod volume) A ≤ c * 2
  rw [Measure.prod_apply_symm hm]
  calc
    (∫⁻ z : ℝ, volume ((fun u : ℝ => (u, z)) ⁻¹' A)) ≤
        ∫⁻ z : ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ => c) z := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ Icc (-1) 1
      · simpa only [indicator_of_mem hz] using hslice z hz
      · simp only [hsupport z hz, measure_empty, indicator_of_notMem hz, le_refl]
    _ = c * 2 := by
      rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
      norm_num

/-- Once small one-dimensional slice images have been extracted, their integration
supplies the required small twisted area. -/
theorem twisted_volume_le_of_slices {n : ℕ} {Y : Fin n → Set Space}
    (hY : ∀ i, IsCompact (Y i)) (hball : (⋃ i, Y i) ⊆ ball 0 1)
    {f : ℝ → ℝ} (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a)
    (hslice : ∀ z : ℝ, z ∈ Icc (-1) 1 →
      volume (projectedSlice f (⋃ i, Y i) z) ≤ ENNReal.ofReal (a / 2)) :
    volume (TwistedProjection f '' (⋃ i, Y i)) ≤ ENNReal.ofReal a := by
  have hm := (isCompact_twistedProjection_union hY hf).measurableSet
  have hbound := planar_volume_le_of_slices hm
    (fun z hz => projectedSlice_eq_empty hball hz) hslice
  apply hbound.trans_eq
  rw [← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (div_nonneg ha (by norm_num))]
  congr 1
  ring

end WangZahlLot.Obl.wz_sticky_twisted_extraction
