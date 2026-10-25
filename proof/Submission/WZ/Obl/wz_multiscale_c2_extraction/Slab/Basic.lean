-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Reg.VerticalHeight
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.GridCube

/-!
# Basic notions for the slab application of sticky Lemma 5.3

* `SlabLinearity`: the frozen conclusion of `wz_slab_local_linearity` (o104), the hypothesis
  `hlin` of o105, with the frozen `AD` written as `Reg.Assouad`.
* `sliceArea A z`: the planar Lebesgue measure of the horizontal slice of `A` at height `z`;
  it is a measure in `A` for each `z`, and integrates to the volume of a measurable set.
-/

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab

open Set Metric MeasureTheory
open scoped ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- The body of the frozen slab local linearity statement (sticky Lemma 5.3) once `η` and
`ρ₀` are chosen, with the frozen `AD` written as `Reg.Assouad`. -/
def SlabSpec (σ ε η ρ₀ : ℝ) : Prop :=
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∀ (z₀ c₀ : ℝ) (Z : Set ℝ) (f : ℝ → ℝ) (K : Finset (Fin 3 → ℤ)) (V : Space → Space),
      -1 ≤ z₀ → z₀ + Real.sqrt ρ ≤ 1 → Z ⊆ Icc z₀ (z₀ + Real.sqrt ρ) →
      (∀ z ∈ Icc z₀ (z₀ + Real.sqrt ρ), ∀ z' ∈ Icc z₀ (z₀ + Real.sqrt ρ),
        |f z - f z'| ≤ |z - z'|) →
      (∀ z ∈ Icc z₀ (z₀ + Real.sqrt ρ), |f z| ≤ 4) →
      (fun (E : Set Space) =>
        (∀ p ∈ E, |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ p 2 ∈ Z ∧ |p 0 + f z₀ * p 1 - c₀| ≤ Real.sqrt ρ) →
        ENNReal.ofReal (ρ ^ (1 + σ / 2 + η)) ≤ volume E →
        (∀ p ∈ E, ‖V p‖ = 1 ∧ ρ ^ (2 * η) ≤ (V p 0) ^ 2 + (V p 1) ^ 2) →
        (∀ p ∈ E, ∀ q ∈ E, dist (V p) (V q) ≤ dist p q) →
        (∀ z ∈ Z, Reg.Assouad ρ (1 - σ) (ρ ^ (-η))
          {u : ℝ | ∃ p ∈ E, p 2 = z ∧ u = p 0 + f z * p 1}) →
        (∀ p ∈ E, volume ((fun q : Space => inner ℝ (V p) q) '' (E ∩ ball p (Real.sqrt ρ))) ≤
          ENNReal.ofReal (ρ ^ ((1 + σ) / 2 - η))) →
        ∃ Zl : Set ℝ, Zl ⊆ Z ∧ ENNReal.ofReal (ρ ^ ((1 : ℝ) / 2 + ε)) ≤ volume Zl ∧
          ∃ a b : ℝ, ∀ z ∈ Zl, |f z - (a + b * z)| ≤ ρ)
      (⋃ k ∈ K, {p : Space | ∀ i : Fin 3, ρ * (k i : ℝ) ≤ p i ∧ p i < ρ * ((k i : ℝ) + 1)})

/-- The frozen slab local linearity statement, the hypothesis `hlin` of o105. -/
def SlabLinearity : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ ε : ℝ, 0 < ε → ∃ η ρ₀ : ℝ, 0 < η ∧ 0 < ρ₀ ∧ SlabSpec σ ε η ρ₀

/-- The point with coordinates `(a, b, z)`. -/
noncomputable def pt (a b z : ℝ) : Space := WithLp.toLp 2 ![a, b, z]

@[simp] lemma pt_zero (a b z : ℝ) : pt a b z 0 = a := rfl
@[simp] lemma pt_one (a b z : ℝ) : pt a b z 1 = b := rfl
@[simp] lemma pt_two (a b z : ℝ) : pt a b z 2 = z := rfl

lemma continuous_pt_slice (z : ℝ) : Continuous (fun q : ℝ × ℝ => pt q.1 q.2 z) := by
  apply (PiLp.continuous_toLp 2 _).comp
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_const

/-- The planar measure of the horizontal slice of `A` at height `z`. -/
noncomputable def sliceArea (A : Set Space) (z : ℝ) : ℝ≥0∞ :=
  volume ((fun q : ℝ × ℝ => pt q.1 q.2 z) ⁻¹' A)

lemma sliceArea_mono {A B : Set Space} (h : A ⊆ B) (z : ℝ) :
    sliceArea A z ≤ sliceArea B z :=
  measure_mono (preimage_mono h)

lemma sliceArea_biUnion_le {ι : Type*} (s : Finset ι) (A : ι → Set Space) (z : ℝ) :
    sliceArea (⋃ i ∈ s, A i) z ≤ ∑ i ∈ s, sliceArea (A i) z := by
  unfold sliceArea
  rw [preimage_iUnion₂]
  exact measure_biUnion_finset_le _ _

lemma sliceArea_eq_zero {A : Set Space} {z : ℝ} (h : ∀ p ∈ A, p 2 ≠ z) :
    sliceArea A z = 0 := by
  unfold sliceArea
  have : (fun q : ℝ × ℝ => pt q.1 q.2 z) ⁻¹' A = ∅ := by
    ext q
    simp only [mem_preimage, mem_empty_iff_false, iff_false]
    intro hq
    exact h _ hq (pt_two _ _ _)
  rw [this, measure_empty]

/-- Only the points at height `z` matter for the slice at `z`. -/
lemma sliceArea_inter_height (A : Set Space) {H : Set ℝ} {z : ℝ} (hz : z ∈ H) :
    sliceArea (A ∩ (fun p : Space => p 2) ⁻¹' H) z = sliceArea A z := by
  unfold sliceArea
  congr 1
  ext q
  simp only [mem_preimage, mem_inter_iff, pt_two]
  exact ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩

lemma sliceArea_inter_height_of_not_mem (A : Set Space) {H : Set ℝ} {z : ℝ} (hz : z ∉ H) :
    sliceArea (A ∩ (fun p : Space => p 2) ⁻¹' H) z = 0 := by
  apply sliceArea_eq_zero
  rintro p ⟨-, hp⟩ rfl
  exact hz hp

lemma ofTwist_zero_eq_pt (u y z : ℝ) :
    WangZahlLot.Obl.wz_grains_nonsingular_slices.ofTwist (fun _ => 0) u y z = pt u y z := by
  ext i
  fin_cases i <;> simp [WangZahlLot.Obl.wz_grains_nonsingular_slices.ofTwist, pt]

lemma sliceArea_eq_lintegral {A : Set Space} (hA : MeasurableSet A) (z : ℝ) :
    sliceArea A z = ∫⁻ u, volume
      (WangZahlLot.Obl.wz_grains_nonsingular_slices.grainFib (fun _ => 0) A u z) := by
  have hm : MeasurableSet ((fun q : ℝ × ℝ => pt q.1 q.2 z) ⁻¹' A) :=
    (continuous_pt_slice z).measurable hA
  unfold sliceArea
  rw [Measure.volume_eq_prod, Measure.prod_apply hm]
  refine lintegral_congr fun u => ?_
  congr 1
  ext y
  simp only [mem_preimage, WangZahlLot.Obl.wz_grains_nonsingular_slices.mem_grainFib,
    ofTwist_zero_eq_pt]

/-- Fubini in horizontal slices. -/
theorem volume_eq_lintegral_sliceArea {A : Set Space} (hA : MeasurableSet A) :
    volume A = ∫⁻ z, sliceArea A z := by
  rw [WangZahlLot.Obl.wz_grains_nonsingular_slices.volume_eq_lintegral_grainFib
    continuous_const hA]
  exact lintegral_congr fun z => (sliceArea_eq_lintegral hA z).symm

/-- The volume of the part of a measurable set at heights in a measurable set `H`. -/
theorem volume_inter_height_eq {A : Set Space} (hA : MeasurableSet A) {H : Set ℝ}
    (hH : MeasurableSet H) :
    volume (A ∩ (fun p : Space => p 2) ⁻¹' H) = ∫⁻ z in H, sliceArea A z := by
  have hm : MeasurableSet (A ∩ (fun p : Space => p 2) ⁻¹' H) :=
    hA.inter ((by fun_prop : Continuous fun p : Space => p 2).measurable hH)
  rw [volume_eq_lintegral_sliceArea hm, ← lintegral_indicator hH]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ H
  · rw [indicator_of_mem hz, sliceArea_inter_height A hz]
  · rw [indicator_of_notMem hz, sliceArea_inter_height_of_not_mem A hz]

/-- Slices of a shading of a quantitatively non-horizontal tube are small. -/
theorem sliceArea_le_of_subset_tube {δ θ : ℝ} {x v : Space} (hδ : 0 < δ) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hv : ‖v‖ = 1) (hvθ : θ ≤ |v 2|) {A : Set Space}
    (hA : A ⊆ thickening δ (segment ℝ x (x + v))) (z : ℝ) :
    sliceArea A z ≤ ENNReal.ofReal (24 * δ ^ 2 / θ ^ 2) := by
  have hT : MeasurableSet (thickening δ (segment ℝ x (x + v))) :=
    isOpen_thickening.measurableSet
  calc sliceArea A z ≤ sliceArea (thickening δ (segment ℝ x (x + v))) z := sliceArea_mono hA z
    _ = _ := sliceArea_eq_lintegral hT z
    _ ≤ _ := Reg.vertical_tube_slice_area hδ hθ hθ1 hv hvθ subset_rfl z

/-- The superadditivity of the lower Lebesgue integral over a finite sum. -/
theorem sum_lintegral_le_lintegral_sum {ι : Type*} (s : Finset ι) (μ : Measure ℝ)
    (g : ι → ℝ → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ z, g i z ∂μ ≤ ∫⁻ z, ∑ i ∈ s, g i z ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc ∫⁻ z, g a z ∂μ + ∑ i ∈ s, ∫⁻ z, g i z ∂μ
        ≤ ∫⁻ z, g a z ∂μ + ∫⁻ z, ∑ i ∈ s, g i z ∂μ := add_le_add le_rfl ih
      _ ≤ ∫⁻ z, (g a z + ∑ i ∈ s, g i z) ∂μ := le_lintegral_add _ _
      _ = ∫⁻ z, ∑ i ∈ insert a s, g i z ∂μ := by
        congr 1
        funext z
        rw [Finset.sum_insert ha]

/-- A function whose integral over a measurable set exceeds `c` times its measure exceeds `c`
somewhere on the set. -/
theorem exists_gt_of_mul_lt {H : Set ℝ} (hH : MeasurableSet H) (g : ℝ → ℝ≥0∞) {c : ℝ≥0∞}
    (h : c * volume H < ∫⁻ z in H, g z) : ∃ z ∈ H, c < g z := by
  by_contra hcon
  push_neg at hcon
  have h1 : ∫⁻ z in H, g z ≤ ∫⁻ _z in H, c := setLIntegral_mono' hH hcon
  rw [setLIntegral_const] at h1
  exact (lt_of_lt_of_le h h1).false

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Slab
