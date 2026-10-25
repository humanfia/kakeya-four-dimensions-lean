/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeBandCaps.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeFrameCaps
import Submission.Obl.k4_subcritical_corrected_scalar_charts.OffsetCaps
import Submission.Obl.k4_subcritical_corrected_scalar_charts.WitnessCount

/-! Integrate an original hidden band over a whole native box. The affine
transport retains its exact h^4 factor, even with large native shears. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4AffineMeshCaps

noncomputable section

/-- A whole normalized native box and an old hidden band cost h^4 times
the original hidden-cell density. No later chart slice enters this cap. -/
theorem native_band_box_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 3 → ℝ) (X : Ω → ℝ) (o : (Fin 3 → ℝ) → ℝ)
    (center : (Fin 3 → ℤ) → ℝ)
    {h δ w H V R : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hw : 0 < w)
    (hH : 1 ≤ H) (hV : 0 ≤ V) (hR : 0 ≤ R)
    (t₀ p r v z τ : ℝ)
    (hresolve : ∀ i, (∑ j, |nativeFrameMatrix h v z τ i j| * δ) ≤ 1)
    (hosc : ∀ q y, baseMesh δ (x y) = q → |o (x y) - center q| ≤ w)
    (hcap : ∀ q n, μ {y | baseMesh δ (x y) = q ∧ ⌊X y / w⌋ = n} ≤
      ENNReal.ofReal (V * δ ^ 3)) :
    μ {y | (∀ i, |nativeFrame h t₀ p r v z τ (x y) i| ≤ H) ∧
      |X y - o (x y)| ≤ R * w} ≤
        ENNReal.ofReal (16200 * (4 * R + 6) * V * h ^ 4 * H ^ 3) := by
  have hRV : 0 ≤ (4 * R + 6) * V := mul_nonneg (by linarith) hV
  have hband (q : Fin 3 → ℤ) :
      μ {y | baseMesh δ (x y) = q ∧ |X y - o (x y)| ≤ R * w} ≤
        ENNReal.ofReal (((4 * R + 6) * V) * δ ^ 3) := by
    have hc := offset_band_cell_cap μ (fun y => baseMesh δ (x y)) X (fun y => o (x y))
      (fun _ => True) q hw hR (ENNReal.ofReal (V * δ ^ 3))
      (by intro n; simpa only [and_true] using hcap q n)
      (by intro y hy _; exact hosc q y hy)
    simpa only [and_true, ← ENNReal.ofReal_mul (by linarith : 0 ≤ 4 * R + 6),
      mul_assoc] using hc
  have hnormalized (q : Fin 3 → ℤ) :
      μ {y | baseMesh 1 (nativeFrame h t₀ p r v z τ (x y)) = q ∧
        |X y - o (x y)| ≤ R * w} ≤
      ENNReal.ofReal (27 * ((4 * R + 6) * V) * h ^ 4) := by
    simpa only [one_pow, mul_one] using
      native_frame_cell_cap μ x (fun y => |X y - o (x y)| ≤ R * w)
        hh hδ (by norm_num : (0 : ℝ) < 1) hRV
        t₀ p r v z τ hresolve hband q
  have hc := Submission.Lib.K4MovingMeshBoxes.measure_movingBox_of_cell_cap μ
    (fun y => nativeFrame h t₀ p r v z τ (x y))
    (fun y => |X y - o (x y)| ≤ R * w)
    (by norm_num : (0 : ℝ) < 1) hH (by norm_num : (0 : ℝ) ≤ 0)
    (show 0 ≤ 27 * ((4 * R + 6) * V) * h ^ 4 by positivity)
    0 (0 : Fin 2 → ℝ) (0 : Fin 2 → ℝ) (fun _ => H)
    (by intro i; simp) (by intro i; exact hH)
    (by intro i; simpa using (zero_le_one.trans hH))
    (by intro q; simpa only [one_pow, mul_one] using hnormalized q)
  refine (measure_mono ?_).trans (hc.trans_eq ?_)
  · intro y hy
    refine ⟨⟨?_, ?_⟩, hy.2⟩
    · simpa only [sub_zero] using hy.1 0
    · intro i
      simpa only [Pi.zero_apply, mul_zero, zero_add, sub_zero] using hy.1 i.succ
  · congr 1
    ring

/-- Full original witnesses with multiplicity one are counted using the
whole native-band cap. A contact's retained mass is irrelevant. -/
theorem native_band_original_witness_count {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (x : Ω → Fin 3 → ℝ) (X : Ω → ℝ) (o : (Fin 3 → ℝ) → ℝ)
    (center : (Fin 3 → ℤ) → ℝ) (W : ι → Set Ω) (S : Finset ι)
    {h δ w H V R m : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hw : 0 < w)
    (hH : 1 ≤ H) (hV : 0 ≤ V) (hR : 0 ≤ R) (hm : 0 < m)
    (t₀ p r v z τ : ℝ)
    (hresolve : ∀ i, (∑ j, |nativeFrameMatrix h v z τ i j| * δ) ≤ 1)
    (hosc : ∀ q y, baseMesh δ (x y) = q → |o (x y) - center q| ≤ w)
    (hcap : ∀ q n, μ {y | baseMesh δ (x y) = q ∧ ⌊X y / w⌋ = n} ≤
      ENNReal.ofReal (V * δ ^ 3))
    (hW : ∀ i ∈ S, MeasurableSet (W i))
    (hunique : ∀ᵐ y ∂μ, ∀ i ∈ S, ∀ j ∈ S, y ∈ W i → y ∈ W j → i = j)
    (hbox : ∀ i ∈ S, ∀ y ∈ W i, ∀ e,
      |nativeFrame h t₀ p r v z τ (x y) e| ≤ H)
    (hband : ∀ i ∈ S, ∀ y ∈ W i, |X y - o (x y)| ≤ R * w)
    (hfloor : ∀ i ∈ S, ENNReal.ofReal m ≤ μ (W i)) :
    (S.card : ℝ) ≤ (16200 * (4 * R + 6) * V * h ^ 4 * H ^ 3) / m := by
  apply original_witness_count μ W S
    {y | (∀ i, |nativeFrame h t₀ p r v z τ (x y) i| ≤ H) ∧
      |X y - o (x y)| ≤ R * w}
    hW hunique (fun i hi y hy => ⟨hbox i hi y hy, hband i hi y hy⟩)
    hm (by positivity) hfloor
  exact native_band_box_cap μ x X o center hh hδ hw hH hV hR
    t₀ p r v z τ hresolve hosc hcap

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
