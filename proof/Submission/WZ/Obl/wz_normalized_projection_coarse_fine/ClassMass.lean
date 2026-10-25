-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.ClassMass.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.Shear

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

noncomputable section

/-- Changing the common linear slope by at most `h` only widens the graph strip by `h`. -/
lemma graphStrip_subset_of_abs_sub_le {δ h c c' : ℝ} {f : ℝ → ℝ} {q : Space}
    (hc : |c - c'| ≤ h) : graphStrip δ f c q ⊆ graphStrip (δ + h) f c' q := by
  rintro p ⟨hz, hp⟩
  refine ⟨hz, ?_⟩
  have hz1 : |p.2| ≤ 1 := abs_le.mpr hz
  calc
    _ = |(p.1 - (q 0 + c * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2)) +
        (c - c') * p.2| := by congr 1; ring
    _ ≤ |p.1 - (q 0 + c * p.2 + q 1 * f p.2 + q 2 * p.2 * f p.2)| +
        |(c - c') * p.2| := abs_add_le _ _
    _ ≤ δ + h := by
      rw [abs_mul]
      have := mul_le_mul hc hz1 (abs_nonneg _) ((abs_nonneg _).trans hc)
      nlinarith

/-- Arbitrary planar majorants can be used in the tube-mass transfer. -/
theorem tube_mass_cubed_le_majorant_moment {f : ℝ → ℝ} (hf : Measurable f)
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (S : Fin n → Set (ℝ × ℝ)) (hS : ∀ i, MeasurableSet (S i))
    (hv : ∀ i, ‖v i‖ = 1) (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hmajor : ∀ i, projection f '' Y i ⊆ S i) :
    (∑ i, volume (Y i)) ^ 3 ≤ ENNReal.ofReal (6 * δ) ^ 3 *
      volume (projection f '' (⋃ i, Y i)) *
        (∫⁻ p : ℝ × ℝ, multiplicity S p ^ (3 / 2 : ℝ)) ^ 2 := by
  have hmass : ∑ i, volume (Y i) ≤
      ENNReal.ofReal (6 * δ) * ∑ i, volume (projection f '' Y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      volume_le_projection_volume hf hδ (hv i) (htrans i) (hY i)
  have hm := sum_outer_measure_cubed_le_moment volume hS hmajor
  rw [← image_iUnion] at hm
  calc
    _ ≤ (ENNReal.ofReal (6 * δ) * ∑ i, volume (projection f '' Y i)) ^ 3 :=
      pow_le_pow_left' hmass 3
    _ = ENNReal.ofReal (6 * δ) ^ 3 * (∑ i, volume (projection f '' Y i)) ^ 3 :=
      mul_pow _ _ _
    _ ≤ ENNReal.ofReal (6 * δ) ^ 3 * (volume (projection f '' (⋃ i, Y i)) * _) :=
      mul_le_mul' le_rfl hm
    _ = _ := (mul_assoc _ _ _).symm

/-- The moment for a thin slice of line parameters is bounded by a single cinematic family. -/
theorem tube_slice_mass_cubed_le_moment {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {δ h c : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space)
    (Y : Fin n → Set Space) (hv : ∀ i, ‖v i‖ = 1)
    (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hclass : ∀ i, |slope (v i) 0 - c| ≤ h) :
    (∑ i, volume (Y i)) ^ 3 ≤ ENNReal.ofReal (6 * δ) ^ 3 *
      volume (projection f '' (⋃ i, Y i)) *
        (∫⁻ p : ℝ × ℝ, multiplicity
          (fun i => graphStrip (12 * δ + h) f 0 (parameters (x i) (v i))) p
            ^ (3 / 2 : ℝ)) ^ 2 := by
  have hm := tube_mass_cubed_le_majorant_moment hf.continuous.measurable hδ x v Y
    (fun i => graphStrip (12 * δ + h) f c (parameters (x i) (v i)))
    (fun i => measurableSet_graphStrip hf.continuous _ _ _) hv htrans hY
    (fun i => ((image_mono (hY i)).trans
      (projection_tube_subset_strip hf hderiv hf0 (hv i) (htrans i) (hball i))).trans
        (graphStrip_subset_of_abs_sub_le (hclass i)))
  rwa [lintegral_graphStrip_shear] at hm

/-- The finite cinematic hypothesis at one scale, in notation suitable for geometric use. -/
def CinematicMomentAt (r η ε : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (q : Fin n → Space), (∀ i, ‖q i‖ ≤ 10) →
    (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
    (∀ (q₀ : Space) (s : ℝ), r ≤ s → s ≤ 1 →
      (Set.ncard {i | q i ∈ ball q₀ s} : ℝ) ≤ r ^ (-η) * (s / r)) →
    (∫⁻ p : ℝ × ℝ, multiplicity (fun i => graphStrip r f 0 (q i)) p
      ^ (3 / 2 : ℝ)) ≤ ENNReal.ofReal (r ^ (-ε))

/-- A separated Katz--Tao slice obeys the cubic mass/area consequence of the cinematic bound. -/
theorem tube_slice_mass_cubed_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hderiv : ∀ z ∈ Icc (-1 : ℝ) 1, |deriv f z| ≤ 2) (hf0 : |f 0| ≤ 1)
    {δ h c η ε : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Space)
    (Y : Fin n → Set Space) (hv : ∀ i, ‖v i‖ = 1)
    (htrans : ∀ i, (1 / 2 : ℝ) ≤ |v i 2|)
    (hball : ∀ i, Tube δ (x i) (v i) ⊆ ball 0 1)
    (hY : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hclass : ∀ i, |slope (v i) 0 - c| ≤ h)
    (hC : CinematicMomentAt (12 * δ + h) η ε f)
    (hsep : ∀ i j, i ≠ j → 12 * δ + h ≤
      dist (parameters (x i) (v i)) (parameters (x j) (v j)))
    (hcount : ∀ (q₀ : Space) (s : ℝ), 12 * δ + h ≤ s → s ≤ 1 →
      (Set.ncard {i | parameters (x i) (v i) ∈ ball q₀ s} : ℝ) ≤
        (12 * δ + h) ^ (-η) * (s / (12 * δ + h))) :
    (∑ i, volume (Y i)) ^ 3 ≤ ENNReal.ofReal (6 * δ) ^ 3 *
      volume (projection f '' (⋃ i, Y i)) *
        ENNReal.ofReal ((12 * δ + h) ^ (-ε)) ^ 2 := by
  have hq (i : Fin n) : ‖parameters (x i) (v i)‖ ≤ 10 := by
    have hx : x i ∈ Tube δ (x i) (v i) :=
      mem_thickening_iff.mpr ⟨x i, left_mem_segment ℝ _ _, by simpa using hδ⟩
    have hxn : ‖x i‖ ≤ 1 := (show ‖x i‖ < 1 by simpa using hball i hx).le
    exact (parameters_norm_le_five hxn (hv i) (htrans i)).trans (by norm_num)
  have hmoment := hC n (fun i => parameters (x i) (v i)) hq hsep hcount
  exact (tube_slice_mass_cubed_le_moment hf hderiv hf0 hδ x v Y hv htrans hball hY
    hclass).trans (mul_le_mul' le_rfl (pow_le_pow_left' hmoment 2))

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
