import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Wide.MatchingLength

set_option linter.unusedVariables false

/-!
# Cell counts of matching sets

The mass of a law on a set of transverse values is bounded by the cap of one transverse cell
times the volume of the thickened set, divided by the cell width; thickening a quadratic
offset-matching set only enlarges its width and range.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter Metric
open scoped ENNReal

noncomputable section

open scoped Classical in
/-- **Cells meeting a bounded set.** -/
theorem measure_le_of_cells {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (S : Set Ω)
    (f : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ) (c : ℝ≥0∞)
    (hcell : ∀ w : ℤ, μ {p | p ∈ S ∧ ⌊f p / δ⌋ = w} ≤ c)
    (E : Set ℝ) {L : ℝ} (hE : E ⊆ Icc (-L) L) :
    μ {p | p ∈ S ∧ f p ∈ E} * ENNReal.ofReal δ ≤ c * volume (thickening δ E) := by
  set W : Finset ℤ := (Finset.Icc ⌊-L / δ⌋ ⌊L / δ⌋).filter (fun w => ∃ x ∈ E, ⌊x / δ⌋ = w)
  have hsub : {p | p ∈ S ∧ f p ∈ E} ⊆ ⋃ w ∈ W, {p | p ∈ S ∧ ⌊f p / δ⌋ = w} := by
    intro p ⟨hS, hE'⟩
    have hb := hE hE'
    refine mem_biUnion (x := ⌊f p / δ⌋) ?_ ⟨hS, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, f p, hE', rfl⟩
    · exact Int.floor_mono (div_le_div_of_nonneg_right hb.1 hδ.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right hb.2 hδ.le)
  have hmass : μ {p | p ∈ S ∧ f p ∈ E} ≤ W.card * c := by
    calc μ {p | p ∈ S ∧ f p ∈ E} ≤ μ (⋃ w ∈ W, {p | p ∈ S ∧ ⌊f p / δ⌋ = w}) := measure_mono hsub
      _ ≤ ∑ w ∈ W, μ {p | p ∈ S ∧ ⌊f p / δ⌋ = w} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _w ∈ W, c := Finset.sum_le_sum fun w _ => hcell w
      _ = W.card * c := by rw [Finset.sum_const, nsmul_eq_mul]
  have hvol : (W.card : ℝ≥0∞) * ENNReal.ofReal δ ≤ volume (thickening δ E) := by
    have hdisj : Set.PairwiseDisjoint (↑W) (fun w : ℤ => Ico ((w : ℝ) * δ) (((w : ℝ) + 1) * δ)) := by
      intro a _ b _ hab
      refine Set.disjoint_left.mpr fun y h1 h2 => hab ?_
      have e1 : ⌊y / δ⌋ = a := by
        rw [Int.floor_eq_iff]; constructor
        · rw [le_div_iff₀ hδ]; exact h1.1
        · rw [div_lt_iff₀ hδ]; exact h1.2
      have e2 : ⌊y / δ⌋ = b := by
        rw [Int.floor_eq_iff]; constructor
        · rw [le_div_iff₀ hδ]; exact h2.1
        · rw [div_lt_iff₀ hδ]; exact h2.2
      rw [← e1, ← e2]
    calc (W.card : ℝ≥0∞) * ENNReal.ofReal δ
        = ∑ w ∈ W, volume (Ico ((w : ℝ) * δ) (((w : ℝ) + 1) * δ)) := by
          have : ∀ w ∈ W, volume (Ico ((w : ℝ) * δ) (((w : ℝ) + 1) * δ)) = ENNReal.ofReal δ := by
            intro w _; rw [Real.volume_Ico]; congr 1; ring
          rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      _ = volume (⋃ w ∈ W, Ico ((w : ℝ) * δ) (((w : ℝ) + 1) * δ)) :=
          (measure_biUnion_finset hdisj (fun w _ => measurableSet_Ico)).symm
      _ ≤ volume (thickening δ E) := by
          apply measure_mono
          intro y hy
          simp only [mem_iUnion, exists_prop] at hy
          obtain ⟨w, hw, hy⟩ := hy
          obtain ⟨-, x, hxE, hxw⟩ := Finset.mem_filter.mp hw
          rw [mem_thickening_iff]
          refine ⟨x, hxE, ?_⟩
          have hx1 : (w : ℝ) * δ ≤ x := by
            have := Int.floor_le (x / δ); rw [hxw, le_div_iff₀ hδ] at this; exact this
          have hx2 : x < ((w : ℝ) + 1) * δ := by
            have := Int.lt_floor_add_one (x / δ); rw [hxw, div_lt_iff₀ hδ] at this; exact this
          rw [Real.dist_eq, abs_lt]
          constructor <;> nlinarith [hy.1, hy.2]
  calc μ {p | p ∈ S ∧ f p ∈ E} * ENNReal.ofReal δ ≤ W.card * c * ENNReal.ofReal δ :=
        mul_le_mul_left hmass _
    _ = c * ((W.card : ℝ≥0∞) * ENNReal.ofReal δ) := by ring
    _ ≤ c * volume (thickening δ E) := mul_le_mul_right hvol _

/-- The quadratic offset-matching set (as in `Inherited.Wide.quadratic_offset_match_volume`). -/
def offsetMatch (δ₀ δ₁ δ₂ w L : ℝ) (O : Finset ℝ) : Set ℝ :=
  {U ∈ Icc (-L) L | ∃ c ∈ O, |δ₀ + δ₁ * U + δ₂ * U ^ 2 - c| ≤ w}

theorem offsetMatch_subset_Icc (δ₀ δ₁ δ₂ w L : ℝ) (O : Finset ℝ) :
    offsetMatch δ₀ δ₁ δ₂ w L O ⊆ Icc (-L) L := fun _ h => h.1

/-- Thickening a matching set enlarges only its width and range. -/
theorem thickening_offsetMatch {δ₀ δ₁ δ₂ w L δ : ℝ} (O : Finset ℝ) (hL : 0 ≤ L) (hδ : 0 < δ) :
    thickening δ (offsetMatch δ₀ δ₁ δ₂ w L O) ⊆
      offsetMatch δ₀ δ₁ δ₂ (w + δ * (|δ₁| + 2 * |δ₂| * (L + δ))) (L + δ) O := by
  intro y hy
  rw [mem_thickening_iff] at hy
  obtain ⟨x, ⟨hxI, c, hc, hxc⟩, hxy⟩ := hy
  rw [Real.dist_eq] at hxy
  have hxL := abs_le.mpr ⟨hxI.1, hxI.2⟩
  have hyL : |y| ≤ L + δ := by
    calc |y| = |x + (y - x)| := by ring_nf
      _ ≤ |x| + |y - x| := abs_add_le _ _
      _ ≤ L + δ := by linarith [hxy.le]
  refine ⟨abs_le.mp hyL, c, hc, ?_⟩
  have hid : δ₀ + δ₁ * y + δ₂ * y ^ 2 - c = (δ₀ + δ₁ * x + δ₂ * x ^ 2 - c) +
      (y - x) * (δ₁ + δ₂ * (x + y)) := by ring
  rw [hid]
  have hxy' : |x + y| ≤ 2 * (L + δ) := by
    calc |x + y| ≤ |x| + |y| := abs_add_le _ _
      _ ≤ 2 * (L + δ) := by linarith
  calc |(δ₀ + δ₁ * x + δ₂ * x ^ 2 - c) + (y - x) * (δ₁ + δ₂ * (x + y))|
      ≤ |δ₀ + δ₁ * x + δ₂ * x ^ 2 - c| + |y - x| * (|δ₁| + |δ₂| * |x + y|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul]
        gcongr
        exact (abs_add_le _ _).trans (by rw [abs_mul])
    _ ≤ w + δ * (|δ₁| + |δ₂| * (2 * (L + δ))) := by
        have h1 : |y - x| ≤ δ := hxy.le
        gcongr
    _ = w + δ * (|δ₁| + 2 * |δ₂| * (L + δ)) := by ring

theorem volume_offsetMatch_le {δ₀ δ₁ δ₂ e θ w L : ℝ} (O : Finset ℝ)
    (hL : 0 ≤ L) (he : 0 < e) (hgap : e ≤ |δ₁| + |δ₂|) (hθ : 0 < θ) (hθe : θ ≤ e / 2)
    (hw : 0 ≤ w) :
    volume (offsetMatch δ₀ δ₁ δ₂ w L O) ≤
      ENNReal.ofReal (θ * (4 * L + 2) / e + 4 * O.card * w / θ) :=
  Inherited.Wide.quadratic_offset_match_volume O hL he hgap hθ hθe hw

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
