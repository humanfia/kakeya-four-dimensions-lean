-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.GridDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

/-- Additivity over a measurable partition also holds for intersections with an arbitrary set. -/
lemma measure_inter_partition {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (μ : Measure α) (X : Set α) (Q : ι → Set α)
    (hQ : ∀ i, MeasurableSet (Q i)) (hdis : Pairwise (fun i j => Disjoint (Q i) (Q j))) :
    μ (X ∩ ⋃ i, Q i) = ∑' i, μ (X ∩ Q i) := by
  have hh := measure_iUnion (μ := μ.restrict X) hdis hQ
  simpa only [Measure.restrict_apply (MeasurableSet.iUnion hQ),
    Measure.restrict_apply (hQ _), inter_comm] using hh

/-- A bounded-diameter measurable partition separates every set into light and dense pieces.
The conclusion uses outer measure and does not require measurability of `X`. -/
theorem density_split_of_partition {α ι : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    [Countable ι] (μ : Measure α) (Q : ι → Set α)
    (hQ : ∀ i, MeasurableSet (Q i)) (hcover : ∀ p : α, ∃ i, p ∈ Q i)
    (hdis : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    {ρ : ℝ} (hdiam : ∀ i, ∀ p ∈ Q i, ∀ q ∈ Q i, dist p q < ρ)
    {v K : ℝ≥0∞} (hvol : ∀ i, μ (Q i) = v)
    (hthick : ∀ i, μ (thickening ρ (Q i)) ≤ K * v)
    (X : Set α) (θ : ℝ≥0∞) :
    ∃ L : Set α, MeasurableSet L ∧
      (∀ S : Set α, μ (X ∩ L ∩ S) ≤ θ * μ (thickening ρ S)) ∧
      θ * μ (thickening ρ (X \ L)) ≤ K * μ (X \ L) := by
  classical
  let light (i : ι) : Prop := μ (X ∩ Q i) < θ * v
  let L := ⋃ i : {i // light i}, Q i
  have hLm : MeasurableSet L := MeasurableSet.iUnion fun i => hQ i
  have hmemL (i : ι) (p : α) (hp : p ∈ Q i) : p ∈ L ↔ light i := by
    constructor
    · intro h
      obtain ⟨j, hj⟩ := mem_iUnion.mp h
      have he : i = j := by
        by_contra hij
        exact (Set.disjoint_left.mp (hdis hij)) hp hj
      simpa only [he] using j.property
    · intro hi
      exact mem_iUnion.mpr ⟨⟨i, hi⟩, hp⟩
  refine ⟨L, hLm, ?_, ?_⟩
  · intro S
    let I := {i : ι // light i ∧ (Q i ∩ S).Nonempty}
    have hsub : X ∩ L ∩ S ⊆ ⋃ i : I, X ∩ Q i := by
      rintro p ⟨⟨hpX, hpL⟩, hpS⟩
      obtain ⟨i, hi⟩ := hcover p
      exact mem_iUnion.mpr ⟨⟨i, (hmemL i p hi).mp hpL, p, hi, hpS⟩, hpX, hi⟩
    have hnear : (⋃ i : I, Q i) ⊆ thickening ρ S := by
      intro p hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      obtain ⟨q, hqQ, hqS⟩ := i.property.2
      exact mem_thickening_iff.mpr ⟨q, hqS, hdiam i p hi q hqQ⟩
    have hdisI : Pairwise (fun i j : I => Disjoint (Q i) (Q j)) := by
      intro i j hij
      exact hdis (fun he => hij (Subtype.ext he))
    calc
      _ ≤ μ (⋃ i : I, X ∩ Q i) := measure_mono hsub
      _ ≤ ∑' i : I, μ (X ∩ Q i) := measure_iUnion_le _
      _ ≤ ∑' _i : I, θ * v := ENNReal.tsum_le_tsum (fun i => i.property.1.le)
      _ = θ * ∑' i : I, μ (Q i) := by simp only [hvol, ENNReal.tsum_mul_left]
      _ = θ * μ (⋃ i : I, Q i) := by rw [measure_iUnion hdisI (fun i => hQ i)]
      _ ≤ θ * μ (thickening ρ S) := mul_le_mul' le_rfl (measure_mono hnear)
  · let I := {i : ι // ¬light i}
    have he : X \ L = X ∩ ⋃ i : I, Q i := by
      ext p
      constructor
      · rintro ⟨hpX, hpL⟩
        obtain ⟨i, hi⟩ := hcover p
        exact ⟨hpX, mem_iUnion.mpr ⟨⟨i, fun h => hpL ((hmemL i p hi).mpr h)⟩, hi⟩⟩
      · rintro ⟨hpX, hp⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp hp
        exact ⟨hpX, fun h => i.property ((hmemL i p hi).mp h)⟩
    have hnear : thickening ρ (X \ L) ⊆ ⋃ i : I, thickening ρ (Q i) := by
      intro p hp
      obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
      rw [he] at hq
      obtain ⟨i, hi⟩ := mem_iUnion.mp hq.2
      exact mem_iUnion.mpr ⟨i, mem_thickening_iff.mpr ⟨q, hi, hpq⟩⟩
    have hdisI : Pairwise (fun i j : I => Disjoint (Q i) (Q j)) := by
      intro i j hij
      exact hdis (fun he => hij (Subtype.ext he))
    calc
      _ ≤ θ * μ (⋃ i : I, thickening ρ (Q i)) := mul_le_mul' le_rfl (measure_mono hnear)
      _ ≤ θ * ∑' i : I, μ (thickening ρ (Q i)) := mul_le_mul' le_rfl (measure_iUnion_le _)
      _ = ∑' i : I, θ * μ (thickening ρ (Q i)) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' i : I, K * μ (X ∩ Q i) := by
        apply ENNReal.tsum_le_tsum
        intro i
        calc
          _ ≤ θ * (K * v) := mul_le_mul' le_rfl (hthick i)
          _ = K * (θ * v) := by ring
          _ ≤ K * μ (X ∩ Q i) := mul_le_mul' le_rfl (le_of_not_gt i.property)
      _ = K * μ (X \ L) := by
        rw [he, measure_inter_partition μ X (fun i : I => Q i) (fun i => hQ i) hdisI,
          ENNReal.tsum_mul_left]


/-- Half-open squares in a planar grid of arbitrary positive side length. -/
def planarCell (ρ : ℝ) (i : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Ico (ρ * i.1) (ρ * (i.1 + 1)) ×ˢ Ico (ρ * i.2) (ρ * (i.2 + 1))

lemma measurableSet_planarCell (ρ : ℝ) (i : ℤ × ℤ) : MeasurableSet (planarCell ρ i) :=
  measurableSet_Ico.prod measurableSet_Ico

lemma floor_eq_of_grid_interval {ρ u : ℝ} (hρ : 0 < ρ) (i : ℤ)
    (hu : u ∈ Ico (ρ * i) (ρ * (i + 1))) : ⌊u / ρ⌋ = i := by
  apply Int.floor_eq_iff.mpr
  exact ⟨(le_div_iff₀ hρ).mpr (by nlinarith [hu.1]),
    (div_lt_iff₀ hρ).mpr (by nlinarith [hu.2])⟩

lemma planarCell_cover {ρ : ℝ} (hρ : 0 < ρ) (p : ℝ × ℝ) : ∃ i, p ∈ planarCell ρ i := by
  refine ⟨(⌊p.1 / ρ⌋, ⌊p.2 / ρ⌋), ?_⟩
  have hmem (u : ℝ) : u ∈ Ico (ρ * (⌊u / ρ⌋ : ℤ)) (ρ * ((⌊u / ρ⌋ : ℤ) + 1)) := by
    constructor
    · have hh := (le_div_iff₀ hρ).mp (Int.floor_le (u / ρ))
      nlinarith
    · have hh := (div_lt_iff₀ hρ).mp (Int.lt_floor_add_one (u / ρ))
      nlinarith
  exact ⟨hmem p.1, hmem p.2⟩

lemma planarCell_disjoint {ρ : ℝ} (hρ : 0 < ρ) :
    Pairwise (fun i j => Disjoint (planarCell ρ i) (planarCell ρ j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  exact hij (Prod.ext
    ((floor_eq_of_grid_interval hρ _ hi.1).symm.trans (floor_eq_of_grid_interval hρ _ hj.1))
    ((floor_eq_of_grid_interval hρ _ hi.2).symm.trans (floor_eq_of_grid_interval hρ _ hj.2)))

lemma planarCell_diameter {ρ : ℝ} (i : ℤ × ℤ) {p q : ℝ × ℝ}
    (hp : p ∈ planarCell ρ i) (hq : q ∈ planarCell ρ i) : dist p q < ρ := by
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  obtain ⟨⟨hp1, hp2⟩, ⟨hp3, hp4⟩⟩ := hp
  obtain ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩ := hq
  constructor <;> rw [abs_lt] <;> constructor <;> nlinarith

lemma volume_planarCell (ρ : ℝ) (i : ℤ × ℤ) :
    volume (planarCell ρ i) = ENNReal.ofReal ρ ^ 2 := by
  have he (k : ℤ) : ρ * (k + 1) - ρ * k = ρ := by ring
  rw [planarCell, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico,
    he, he, pow_two]

lemma volume_thickening_planarCell {ρ : ℝ} (hρ : 0 < ρ) (i : ℤ × ℤ) :
    volume (thickening ρ (planarCell ρ i)) ≤ 9 * ENNReal.ofReal ρ ^ 2 := by
  let Q := Ioo (ρ * i.1 - ρ) (ρ * (i.1 + 1) + ρ) ×ˢ
    Ioo (ρ * i.2 - ρ) (ρ * (i.2 + 1) + ρ)
  have hsub : thickening ρ (planarCell ρ i) ⊆ Q := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq] at hpq
    obtain ⟨hp1, hp2⟩ := abs_lt.mp hpq.1
    obtain ⟨hp3, hp4⟩ := abs_lt.mp hpq.2
    obtain ⟨⟨hq1, hq2⟩, ⟨hq3, hq4⟩⟩ := hq
    exact ⟨⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩⟩
  have hvol : volume Q = 9 * ENNReal.ofReal ρ ^ 2 := by
    have he (k : ℤ) : ρ * (k + 1) + ρ - (ρ * k - ρ) = 3 * ρ := by ring
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo, he, he,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    ring
  exact (measure_mono hsub).trans_eq hvol

/-- The planar grid density split with the explicit neighborhood factor nine. -/
theorem planar_grid_density_split (X : Set (ℝ × ℝ)) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ≥0∞) :
    ∃ L : Set (ℝ × ℝ), MeasurableSet L ∧
      (∀ S : Set (ℝ × ℝ), volume (X ∩ L ∩ S) ≤ θ * volume (thickening ρ S)) ∧
      θ * volume (thickening ρ (X \ L)) ≤ 9 * volume (X \ L) := by
  exact density_split_of_partition volume (planarCell ρ) (measurableSet_planarCell ρ)
    (planarCell_cover hρ) (planarCell_disjoint hρ)
    (fun i _ hp _ hq => planarCell_diameter i hp hq) (volume_planarCell ρ)
    (volume_thickening_planarCell hρ) X θ

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
