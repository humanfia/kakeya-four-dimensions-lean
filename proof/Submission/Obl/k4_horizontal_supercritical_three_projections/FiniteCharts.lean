import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.ChartPartition
import Submission.Obl.k4_horizontal_supercritical_three_projections.Ensemble

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory
open scoped ENNReal BigOperators
open Parent Submission.Obl.k4_row_cell_regularization

structure FiniteChartPartition (α : Type) where
  n : ℕ
  G : Fin n → Set α
  q : Fin n → Fin 3 → ℤ

namespace FiniteChartPartition

variable {α : Type} [MeasurableSpace α]

structure Good (L : FiniteChartPartition α) (b : α → Fin 6 → ℝ) (π : Measure ℝ)
    (A : Set α) (χ D K E : ℝ) : Prop where
  measurable : ∀ i, MeasurableSet (L.G i)
  disjoint : ∀ i j, i ≠ j → Disjoint (L.G i) (L.G j)
  subset : ∀ i, L.G i ⊆ A
  cover : ∀ l ∈ A, ∃ i, l ∈ L.G i
  nonempty : ∀ i, (L.G i).Nonempty
  bins : ∀ i l, l ∈ L.G i →
    ⌊b l 3 / χ⌋ = L.q i 0 ∧ ⌊b l 0 / D⌋ = L.q i 1 ∧ ⌊b l 1 / D⌋ = L.q i 2
  corner : ∀ i, |(L.q i 0 : ℝ) * χ| + |(L.q i 1 : ℝ) * D| +
    |(L.q i 2 : ℝ) * D| ≤ 10 * K
  coordinates : ∀ i l, l ∈ L.G i →
    ⌊b l 3 / χ⌋ = L.q i 0 ∧ ⌊b l 1 / D⌋ = L.q i 2 ∧
    b l 0 ∈ Ico ((L.q i 1 : ℝ) * D) ((L.q i 1 : ℝ) * D + D) ∧
    |b l 1 - (L.q i 2 : ℝ) * D| ≤ D ∧
    (∀ e, |b l e| ≤ 10 * K) ∧ |b l 4 + b l 0| ≤ E
  budget : ∑ i, chartWeight π χ D (L.q i) ≤ 441 * K ^ 2

end FiniteChartPartition

/-- Bounded original lines split into finitely many actual charts. The
reference budget is independent of the fine direction mesh. -/
theorem finite_bounded_charts {α : Type} [MeasurableSpace α]
    (b : α → Fin 6 → ℝ) (hb : Measurable b) (π : Measure ℝ) [IsProbabilityMeasure π]
    (A : Set α) (hA : MeasurableSet A) {χ D K E : ℝ}
    (hχ : 0 < χ) (hχ₁ : χ ≤ 1) (hD : 0 < D) (hD₁ : D ≤ 1) (hK : 1 ≤ K)
    (hbound : ∀ l ∈ A, (∀ e, |b l e| ≤ 3 * K) ∧ |b l 0| ≤ K ∧ |b l 3| ≤ K ∧
      |b l 4 + b l 0| ≤ E) :
    ∃ L : FiniteChartPartition α, L.Good b π A χ D K E := by
  classical
  let codes := (fun l => chartLabel D χ (b l)) '' A
  have hsub : codes ⊆ (chartLabels D χ (3 * K) : Set ((ℤ × ℤ) × ℤ)) := by
    rintro c ⟨l, hl, rfl⟩
    exact mem_chartLabels hD hχ (b l) ((hbound l hl).1 0) ((hbound l hl).1 1) ((hbound l hl).1 3)
  have hfin : codes.Finite := (chartLabels D χ (3 * K)).finite_toSet.subset hsub
  let I := hfin.toFinset
  let e := (Fintype.equivFin I).symm
  let code := fun i : Fin (Fintype.card I) => (e i).val
  let L : FiniteChartPartition α := {
    n := Fintype.card I
    G := fun i => A ∩ {l | chartLabel D χ (b l) = code i}
    q := fun i => ![(code i).2, (code i).1.1, (code i).1.2] }
  have hcode (i) : code i ∈ codes := by
    simpa only [I, Set.Finite.mem_toFinset] using (e i).property
  have hnonempty (i) : (L.G i).Nonempty := by
    obtain ⟨l, hl, hli⟩ := hcode i
    exact ⟨l, hl, hli⟩
  have hbins (i) (l) (hl : l ∈ L.G i) :
      ⌊b l 3 / χ⌋ = L.q i 0 ∧ ⌊b l 0 / D⌋ = L.q i 1 ∧ ⌊b l 1 / D⌋ = L.q i 2 := by
    exact ⟨congrArg Prod.snd hl.2, congrArg (fun c => c.1.1) hl.2,
      congrArg (fun c => c.1.2) hl.2⟩
  have hcenter {x δ : ℝ} {j : ℤ} (hδ : 0 < δ) (hj : ⌊x / δ⌋ = j) :
      |(j : ℝ) * δ| ≤ |x| + δ := by
    have herr := fine_intercept_error hδ hj
    calc
      _ = |x - (x - (j : ℝ) * δ)| := by congr 1; ring
      _ ≤ |x| + |x - (j : ℝ) * δ| := abs_sub _ _
      _ ≤ _ := add_le_add le_rfl herr
  refine ⟨L, ?_⟩
  refine {
    measurable := fun i => hA.inter ((measurable_chartLabel hb D χ) (measurableSet_singleton (code i)))
    disjoint := ?_
    subset := fun i => inter_subset_left
    cover := ?_
    nonempty := hnonempty
    bins := hbins
    corner := ?_
    coordinates := ?_
    budget := ?_ }
  · intro i j hij
    apply disjoint_left.mpr
    intro l hli hlj
    apply hij
    apply e.injective
    exact Subtype.ext (hli.2.symm.trans hlj.2)
  · intro l hl
    have hmem : chartLabel D χ (b l) ∈ I := by
      simpa only [I, Set.Finite.mem_toFinset] using (show chartLabel D χ (b l) ∈ codes from ⟨l, hl, rfl⟩)
    refine ⟨e.symm ⟨_, hmem⟩, hl, ?_⟩
    change chartLabel D χ (b l) = (e (e.symm ⟨_, hmem⟩)).val
    rw [e.apply_symm_apply]
  · intro i
    obtain ⟨l, hl⟩ := hnonempty i
    obtain ⟨hv, hp, hq⟩ := hbins i l hl
    have h := hbound l hl.1
    have hv' := hcenter hχ hv
    have hp' := hcenter hD hp
    have hq' := hcenter hD hq
    linarith [h.1 1, h.2.1, h.2.2.1]
  · intro i l hl
    obtain ⟨hv, hp, hq⟩ := hbins i l hl
    have h₀ := (le_div_iff₀ hD).mp (Int.floor_le (b l 0 / D))
    have h₁ := (div_lt_iff₀ hD).mp (Int.lt_floor_add_one (b l 0 / D))
    rw [hp] at h₀ h₁
    refine ⟨hv, hq, ⟨h₀, by linarith⟩, fine_intercept_error hD hq, ?_, (hbound l hl.1).2.2.2⟩
    intro j
    linarith [(hbound l hl.1).1 j]
  · have heq : (∑ i, chartWeight π χ D (L.q i)) =
        ∑ c ∈ I, D ^ 2 * binWeight π χ c.2 := by
      have h := Equiv.sum_comp e (fun c : I => D ^ 2 * binWeight π χ c.val.2)
      rw [Finset.sum_coe_sort I (fun c => D ^ 2 * binWeight π χ c.2)] at h
      simpa only [L, code, chartWeight, binWeight, Measure.real, Matrix.cons_val_zero, mul_comm] using h
    rw [heq]
    calc
      _ ≤ ∑ c ∈ chartLabels D χ (3 * K), D ^ 2 * binWeight π χ c.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro c hc
          apply hsub
          simpa only [I, Set.Finite.mem_toFinset] using hc
        · intro c _ _
          exact mul_nonneg (sq_nonneg _) (binWeight_nonneg π χ _)
      _ ≤ 49 * (3 * K) ^ 2 := chart_reference_budget π hD hD₁ hχ (by linarith)
        (intervalBins χ 0 (3 * K))
      _ = _ := by ring

end Submission.Obl.k4_horizontal_supercritical_three_projections
