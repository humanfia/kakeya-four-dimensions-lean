import Mathlib
import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory
open scoped ENNReal BigOperators

/-- Disjoint whole-domain floors give a summable original-reference budget. -/
theorem reference_budget_of_original_floors {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (ρ : Measure Ω) (E : ι → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) (w : ι → ENNReal)
    (C : ENNReal) (hfloor : ∀ i, w i ≤ C * ρ (E i)) :
    ∑ i, w i ≤ C * ρ univ := by
  calc
    _ ≤ ∑ i, C * ρ (E i) := Finset.sum_le_sum (fun i _ => hfloor i)
    _ = C * ∑ i, ρ (E i) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right
      (sum_measure_le_measure_univ (fun i _ => (hE i).nullMeasurableSet)
        (fun i _ j _ hij => (hdisj hij).aedisjoint)) _

/-- Rewrite the slice's real reference numerator in the original palette
units occurring in the frozen output. -/
theorem sliced_weight_identity {p : ENNReal} (hp : p ≠ ⊤) {D : ℝ} (hD : D ≠ 0)
    (χ a d : ℝ) (hχ : 0 ≤ χ) (hD₀ : 0 ≤ D) (ha : 0 ≤ a) :
    ENNReal.ofReal (χ * D * a ^ d) * p =
      ENNReal.ofReal ((p.toReal * D ^ 2 * a ^ d) * χ / D) := by
  calc
    _ = ENNReal.ofReal (χ * D * a ^ d) * ENNReal.ofReal p.toReal := by
      rw [ENNReal.ofReal_toReal hp]
    _ = ENNReal.ofReal ((χ * D * a ^ d) * p.toReal) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ = _ := by congr 1; field_simp

/-- The fine intercept bins occupied by one original assignment. -/
noncomputable def interceptBins {α : Type} (A : Set α) (f : α → ℝ) (χ : ℝ)
    (hfinite : ((fun l => ⌊f l / χ⌋) '' A).Finite) : Finset ℤ := hfinite.toFinset

/-- An assignment lying in a coarse parameter interval has few fine slices. -/
theorem finite_intercept_bins {α : Type} (A : Set α) (f : α → ℝ)
    {D χ : ℝ} (hD : 0 ≤ D) (hχ : 0 < χ)
    (hdiam : ∀ l ∈ A, ∀ l' ∈ A, |f l - f l'| ≤ D) :
    ((fun l => ⌊f l / χ⌋) '' A).Finite ∧
      (((fun l => ⌊f l / χ⌋) '' A).ncard : ℝ) ≤ 2 * D / χ + 2 := by
  have h := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
    (f '' A) hD hχ 0 (by
      rintro _ ⟨l, hl, rfl⟩ _ ⟨l', hl', rfl⟩
      simpa only [Real.dist_eq] using hdiam l hl l' hl')
  have heq : (fun x : ℝ => ⌊(x - 0) / χ⌋) '' (f '' A) =
      (fun l => ⌊f l / χ⌋) '' A := by simp only [image_image, sub_zero]
  simpa only [heq] using h

/-- Every parent's total sliced numerator is at most four times its old one.
Only the coarse interval diameter is charged, not the number of other parents. -/
theorem sliced_numerator_budget {n : ℕ} (B : Fin n → Finset ℤ) (w : Fin n → ℝ)
    {D χ : ℝ} (hD : 0 < D) (hχ : 0 < χ) (hχD : χ ≤ D)
    (hw : ∀ i, 0 ≤ w i) (hB : ∀ i, ((B i).card : ℝ) ≤ 2 * D / χ + 2) :
    ∑ i, ∑ _z ∈ B i, w i * χ / D ≤ 4 * ∑ i, w i := by
  calc
    _ = ∑ i, ((B i).card : ℝ) * (w i * χ / D) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i, 4 * w i := by
      apply Finset.sum_le_sum
      intro i _
      have hterm : 0 ≤ w i * χ / D := div_nonneg (mul_nonneg (hw i) hχ.le) hD.le
      calc
        _ ≤ (2 * D / χ + 2) * (w i * χ / D) :=
          mul_le_mul_of_nonneg_right (hB i) hterm
        _ = 2 * w i + 2 * w i * (χ / D) := by field_simp
        _ ≤ 4 * w i := by
          have : χ / D ≤ 1 := (div_le_one hD).mpr hχD
          nlinarith [hw i]
    _ = _ := by rw [Finset.mul_sum]

/-- A finite family of fine slices. -/
def interceptSlice {α : Type} {n : ℕ} (A : Fin n → Set α) (f : α → ℝ)
    (χ : ℝ) (p : Fin n × ℤ) : Set α := A p.1 ∩ {l | ⌊f l / χ⌋ = p.2}

theorem measurableSet_interceptSlice {α : Type} [MeasurableSpace α] {n : ℕ}
    {A : Fin n → Set α} {f : α → ℝ} (hA : ∀ i, MeasurableSet (A i))
    (hf : Measurable f) (χ : ℝ) (p : Fin n × ℤ) :
    MeasurableSet (interceptSlice A f χ p) :=
  (hA p.1).inter (((hf.div_const χ).floor) (measurableSet_singleton p.2))

/-- Splitting disjoint assignments into intercept fibres preserves disjointness. -/
theorem disjoint_interceptSlice {α : Type} {n : ℕ}
    {A : Fin n → Set α} (f : α → ℝ) (χ : ℝ)
    (hA : ∀ i i', i ≠ i' → Disjoint (A i) (A i')) :
    Pairwise (fun p q : Fin n × ℤ =>
      Disjoint (interceptSlice A f χ p) (interceptSlice A f χ q)) := by
  intro p q hpq
  apply disjoint_left.mpr
  rintro l ⟨hl, hp⟩ ⟨hl', hq⟩
  by_cases h : p.1 = q.1
  · apply hpq
    exact Prod.ext h (hp.symm.trans hq)
  · exact disjoint_left.mp (hA p.1 q.1 h) hl hl'

/-- Retain whole fine slices against their reference numerator. The deletion
estimate uses the current measure; its floors therefore hold under every larger
original measure. -/
theorem heavy_intercept_slices {α : Type} [MeasurableSpace α] {n : ℕ}
    (μ : Measure (α × ℝ)) (A : Fin n → Set α) (f : α → ℝ)
    (B : Fin n → Finset ℤ) (w : Fin n → ℝ) {D χ δ : ℝ}
    (hD : 0 < D) (hχ : 0 < χ) (hχD : χ ≤ D) (hδ : 0 ≤ δ)
    (hw : ∀ i, 0 ≤ w i) (hB : ∀ i, ((B i).card : ℝ) ≤ 2 * D / χ + 2)
    (hcover : ∀ i l, l ∈ A i → ⌊f l / χ⌋ ∈ B i) :
    ∃ Good : Finset (Fin n × ℤ),
      (∀ p ∈ Good, p.2 ∈ B p.1) ∧
      (∀ p ∈ Good, ENNReal.ofReal (δ * (w p.1 * χ / D)) ≤
        μ (interceptSlice A f χ p ×ˢ Icc (0 : ℝ) 1)) ∧
      (∑ p ∈ Good, ENNReal.ofReal (w p.1 * χ / D)) ≤
        ENNReal.ofReal (4 * ∑ i, w i) ∧
      μ {p | (∃ i, p.1 ∈ A i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
        ¬ ∃ q ∈ Good, p.1 ∈ interceptSlice A f χ q} ≤
        ENNReal.ofReal (δ * (4 * ∑ i, w i)) := by
  classical
  let All : Finset (Fin n × ℤ) := Finset.univ.biUnion fun i =>
    (B i).image (fun z => (i, z))
  let event := fun q : Fin n × ℤ => interceptSlice A f χ q ×ˢ Icc (0 : ℝ) 1
  let W := fun q : Fin n × ℤ => ENNReal.ofReal (w q.1 * χ / D)
  let Good := All.filter fun q => ENNReal.ofReal δ * W q ≤ μ (event q)
  have memAll (q : Fin n × ℤ) : q ∈ All ↔ q.2 ∈ B q.1 := by
    rcases q with ⟨i, z⟩
    simp [All]
  have hbudget : ∑ q ∈ All, W q ≤ ENNReal.ofReal (4 * ∑ i, w i) := by
    have heq : ∑ q ∈ All, W q = ∑ i, ∑ z ∈ B i, W (i, z) := by
      rw [Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_image]
        intro x _ y _ hxy
        exact (Prod.mk.inj hxy).2
      · intro i _ i' _ hii'
        apply Finset.disjoint_left.mpr
        rintro q hq hq'
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
        obtain ⟨z', hz', heq⟩ := Finset.mem_image.mp hq'
        exact hii' (congrArg Prod.fst heq).symm
    rw [heq]
    have hterm (i : Fin n) : 0 ≤ w i * χ / D :=
      div_nonneg (mul_nonneg (hw i) hχ.le) hD.le
    have hnn : ∀ i, 0 ≤ ∑ _z ∈ B i, w i * χ / D := by
      intro i; exact Finset.sum_nonneg (fun _ _ => hterm i)
    change (∑ i, ∑ _z ∈ B i, ENNReal.ofReal (w i * χ / D)) ≤ _
    simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hterm _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i)]
    exact ENNReal.ofReal_le_ofReal (sliced_numerator_budget B w hD hχ hχD hw hB)
  refine ⟨Good, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact (memAll q).mp (Finset.mem_filter.mp hq).1
  · intro q hq
    simpa only [Good, W, ENNReal.ofReal_mul hδ] using (Finset.mem_filter.mp hq).2
  · exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hbudget
  · have hsub : {p | (∃ i, p.1 ∈ A i) ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧
        ¬ ∃ q ∈ Good, p.1 ∈ interceptSlice A f χ q} ⊆
        ⋃ q ∈ All \ Good, event q := by
      rintro p ⟨⟨i, hi⟩, ht, hnot⟩
      let q := (i, ⌊f p.1 / χ⌋)
      have hq : q ∈ All := (memAll q).mpr (hcover i p.1 hi)
      have hmem : p.1 ∈ interceptSlice A f χ q := ⟨hi, rfl⟩
      have hng : q ∉ Good := fun hg => hnot ⟨q, hg, hmem⟩
      exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨Finset.mem_sdiff.mpr ⟨hq, hng⟩, hmem, ht⟩⟩
    calc
      _ ≤ μ (⋃ q ∈ All \ Good, event q) := measure_mono hsub
      _ ≤ ∑ q ∈ All \ Good, μ (event q) := measure_biUnion_finset_le _ _
      _ ≤ ∑ q ∈ All \ Good, ENNReal.ofReal δ * W q := by
        apply Finset.sum_le_sum
        intro q hq
        have hn : ¬ ENNReal.ofReal δ * W q ≤ μ (event q) := by
          intro hh
          apply (Finset.mem_sdiff.mp hq).2
          exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hq).1, hh⟩
        exact (lt_of_not_ge hn).le
      _ ≤ ∑ q ∈ All, ENNReal.ofReal δ * W q :=
        Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
      _ = ENNReal.ofReal δ * ∑ q ∈ All, W q := by rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (4 * ∑ i, w i) :=
        mul_le_mul_right hbudget _
      _ = _ := (ENNReal.ofReal_mul hδ).symm

end Submission.Obl.k4_horizontal_supercritical_three_projections
