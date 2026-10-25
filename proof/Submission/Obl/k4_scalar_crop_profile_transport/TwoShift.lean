import Mathlib

/-!
# Laws whose integer label is one of two shifts of a source label

Let `Φ` be an observation with an integer label whose law has a density with respect to
`ref × count`, and let `Ψ` agree with `Φ` except that its label is the source label shifted by
`m` or by `m + 1`, pointwise. Then
* `two_shift_absolutelyContinuous`: the law of `Ψ` is absolutely continuous as well;
* `two_shift_upper_tail`: on a set `S`, the mass where a density of the restricted law of `Ψ`
  exceeds `T` is at most four times the mass where the source density exceeds `θ`, whenever
  `4 θ ≤ T`.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set
open scoped ENNReal

section TwoShift

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Shift of the integer label. -/
def labelShift (n : ℤ) (y : Y × ℤ) : Y × ℤ := (y.1, y.2 + n)

lemma measurable_labelShift (n : ℤ) : Measurable (labelShift (Y := Y) n) :=
  measurable_fst.prodMk (measurable_snd.add_const n)

lemma map_labelShift (ref : Measure Y) [SFinite ref] (n : ℤ) :
    (ref.prod (Measure.count : Measure ℤ)).map (labelShift n) = ref.prod Measure.count := by
  have h : labelShift (Y := Y) n = Prod.map id (· + n) := rfl
  rw [h, ← Measure.map_prod_map _ _ measurable_id (measurable_add_const n), Measure.map_id,
    map_add_right_eq_self]

lemma labelShift_preimage_measure (ref : Measure Y) [SFinite ref] (n : ℤ)
    {A : Set (Y × ℤ)} (hA : MeasurableSet A) :
    (ref.prod (Measure.count : Measure ℤ)) (labelShift n ⁻¹' A) =
      (ref.prod Measure.count) A := by
  rw [← Measure.map_apply (measurable_labelShift n) hA, map_labelShift]

/-- A label which is one of two shifts of an absolutely continuous labelled observation. -/
theorem two_shift_absolutelyContinuous (ref : Measure Y) [SFinite ref] (μ : Measure X)
    {Φ Ψ : X → Y × ℤ} (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (hac : μ.map Φ ≪ ref.prod Measure.count) (m : ℤ)
    (hshift : ∀ x, Ψ x = labelShift m (Φ x) ∨ Ψ x = labelShift (m + 1) (Φ x)) :
    μ.map Ψ ≪ ref.prod Measure.count := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.map_apply hΨ hs]
  have hsub : Ψ ⁻¹' s ⊆ Φ ⁻¹' (labelShift m ⁻¹' s) ∪ Φ ⁻¹' (labelShift (m + 1) ⁻¹' s) := by
    intro x hx
    rcases hshift x with h | h
    · left
      change labelShift m (Φ x) ∈ s
      rw [← h]
      exact hx
    · right
      change labelShift (m + 1) (Φ x) ∈ s
      rw [← h]
      exact hx
  apply measure_mono_null hsub
  apply measure_union_null
  · rw [← Measure.map_apply hΦ (measurable_labelShift m hs)]
    exact hac (by rw [labelShift_preimage_measure ref m hs]; exact hs0)
  · rw [← Measure.map_apply hΦ (measurable_labelShift (m + 1) hs)]
    exact hac (by rw [labelShift_preimage_measure ref (m + 1) hs]; exact hs0)

/-- Upper tails of a restricted law whose label is one of two shifts of a source label. -/
theorem two_shift_upper_tail (ref : Measure Y) [SFinite ref] (μ : Measure X)
    [IsFiniteMeasure μ] {Φ Ψ : X → Y × ℤ} (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    {H : Y × ℤ → ℝ≥0∞} (hH : Measurable H)
    (hHlaw : μ.map Φ = (ref.prod Measure.count).withDensity H)
    (S : Set X) {D : Y × ℤ → ℝ≥0∞} (hD : Measurable D)
    (hDlaw : (μ.restrict S).map Ψ = (ref.prod Measure.count).withDensity D) (m : ℤ)
    (hshift : ∀ x, Ψ x = labelShift m (Φ x) ∨ Ψ x = labelShift (m + 1) (Φ x))
    {T θ : ℝ≥0∞} (hθ : 4 * θ ≤ T) :
    μ (S ∩ {x | T < D (Ψ x)}) ≤ 4 * μ (S ∩ {x | θ < H (Φ x)}) := by
  set JR : Measure (Y × ℤ) := ref.prod Measure.count with hJR
  set A : Set (Y × ℤ) := {y | T < D y} with hAdef
  have hA : MeasurableSet A := measurableSet_lt measurable_const hD
  set lam := μ (S ∩ {x | T < D (Ψ x)}) with hlamdef
  set B := μ (S ∩ {x | θ < H (Φ x)}) with hBdef
  have hlam : (μ.restrict S).map Ψ A = lam := by
    rw [Measure.map_apply hΨ hA, Measure.restrict_apply (hΨ hA), inter_comm]
    rfl
  have hTA : T * JR A ≤ lam := by
    rw [← hlam, hDlaw, withDensity_apply _ hA, ← setLIntegral_const]
    exact setLIntegral_mono hD (fun y hy => hy.le)
  have hpiece : ∀ n : ℤ, μ (S ∩ {x | T < D (Ψ x)} ∩ {x | Ψ x = labelShift n (Φ x)}) ≤
      B + θ * JR A := by
    intro n
    have hB' : MeasurableSet (labelShift n ⁻¹' A ∩ {y | H y ≤ θ}) :=
      (measurable_labelShift n hA).inter (measurableSet_le hH measurable_const)
    calc μ (S ∩ {x | T < D (Ψ x)} ∩ {x | Ψ x = labelShift n (Φ x)})
        ≤ μ ((S ∩ {x | θ < H (Φ x)}) ∪ Φ ⁻¹' (labelShift n ⁻¹' A ∩ {y | H y ≤ θ})) := by
          apply measure_mono
          rintro x ⟨⟨hxS, hxD⟩, hxe⟩
          by_cases hH4 : θ < H (Φ x)
          · exact Or.inl ⟨hxS, hH4⟩
          · refine Or.inr ⟨?_, not_lt.mp hH4⟩
            change T < D (labelShift n (Φ x))
            have hxe' : Ψ x = labelShift n (Φ x) := hxe
            rw [← hxe']
            exact hxD
      _ ≤ B + μ (Φ ⁻¹' (labelShift n ⁻¹' A ∩ {y | H y ≤ θ})) := measure_union_le _ _
      _ ≤ B + θ * JR A := by
          gcongr
          rw [← Measure.map_apply hΦ hB', hHlaw, withDensity_apply _ hB']
          calc ∫⁻ y in labelShift n ⁻¹' A ∩ {y | H y ≤ θ}, H y ∂JR
              ≤ ∫⁻ _ in labelShift n ⁻¹' A ∩ {y | H y ≤ θ}, θ ∂JR :=
                setLIntegral_mono measurable_const (fun y hy => hy.2)
            _ = θ * JR (labelShift n ⁻¹' A ∩ {y | H y ≤ θ}) := setLIntegral_const _ _
            _ ≤ θ * JR (labelShift n ⁻¹' A) := by gcongr; exact inter_subset_left
            _ = θ * JR A := by rw [labelShift_preimage_measure ref n hA]
  have hsplit : lam ≤ μ (S ∩ {x | T < D (Ψ x)} ∩ {x | Ψ x = labelShift m (Φ x)}) +
      μ (S ∩ {x | T < D (Ψ x)} ∩ {x | Ψ x = labelShift (m + 1) (Φ x)}) := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro x hx
    rcases hshift x with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hfin : lam ≠ ∞ := measure_ne_top μ _
  have h1 : lam ≤ 2 * B + 2 * (θ * JR A) := by
    calc lam ≤ (B + θ * JR A) + (B + θ * JR A) :=
          hsplit.trans (add_le_add (hpiece m) (hpiece (m + 1)))
      _ = 2 * B + 2 * (θ * JR A) := by ring
  have h2 : 4 * (θ * JR A) ≤ lam := by
    calc 4 * (θ * JR A) = (4 * θ) * JR A := by ring
      _ ≤ T * JR A := by gcongr
      _ ≤ lam := hTA
  have h3 : lam + lam ≤ 4 * B + lam := by
    calc lam + lam = 2 * lam := by ring
      _ ≤ 2 * (2 * B + 2 * (θ * JR A)) := by gcongr
      _ = 4 * B + 4 * (θ * JR A) := by ring
      _ ≤ 4 * B + lam := by gcongr
  exact ENNReal.le_of_add_le_add_right hfin h3

end TwoShift

end Submission.Obl.k4_scalar_crop_profile_transport
