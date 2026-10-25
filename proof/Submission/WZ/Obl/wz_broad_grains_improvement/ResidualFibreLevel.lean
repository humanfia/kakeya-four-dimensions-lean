-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.ResidualFibreLevel.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.Dyadic
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.DyadicShading

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set MeasureTheory
open scoped ENNReal Classical

variable {α : Type*} [MeasurableSpace α]

/-- Fibrewise dyadic selection exposes its common-cut property, so all
retained pointwise incidence fractions survive unchanged. -/
theorem fibre_dyadic_level_common (μ : Measure α) {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set α) (hZ : ∀ i, MeasurableSet (Z i)) :
    ∃ (k : ℕ) (Z₁ : Fin n → Set α),
      (∀ i, MeasurableSet (Z₁ i) ∧ Z₁ i ⊆ Z i ∧ (i ∉ S → Z₁ i = ∅)) ∧
      ∑ i ∈ S, μ (Z i) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) * ∑ i, μ (Z₁ i) ∧
      ∀ (j : Fin N) (p : α), (∃ i, f i = j ∧ p ∈ Z₁ i) →
        2 ^ k ≤ (Finset.univ.filter fun i => f i = j ∧ p ∈ Z₁ i).card ∧
        (Finset.univ.filter fun i => f i = j ∧ p ∈ Z₁ i).card < 2 ^ (k + 1) ∧
        (∀ i, f i = j → (p ∈ Z₁ i ↔ i ∈ S ∧ p ∈ Z i)) := by
  classical
  let Y' : Fin n → Set (Fin N × α) := fun i => if i ∈ S then {f i} ×ˢ Z i else ∅
  have hY' : ∀ i, MeasurableSet (Y' i) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [Y', if_pos hi]
      exact (measurableSet_singleton _).prod (hZ i)
    · simp only [Y', if_neg hi]
      exact MeasurableSet.empty
  have hY'sub : ∀ i, Y' i ⊆ {f i} ×ˢ univ := by
    intro i q hq
    by_cases hi : i ∈ S
    · simp only [Y', if_pos hi] at hq
      exact ⟨hq.1, mem_univ _⟩
    · simp only [Y', if_neg hi] at hq
      exact hq.elim
  obtain ⟨k, Z', -, hZ', hmass, hlevel⟩ :=
    WangZahlLot.Obl.wz_coarse_tube_grains.RIS.dyadic_shading_refinement_common
      (fibreMeasure μ N) Y' hY'
  let Z₁ : Fin n → Set α := fun i => (fun p => (f i, p)) ⁻¹' Z' i
  have hZ'sub : ∀ i, Z' i ⊆ {f i} ×ˢ univ := fun i => (hZ' i).2.trans (hY'sub i)
  have hZ₁m : ∀ i, MeasurableSet (Z₁ i) := fun i => measurable_prodMk_left (hZ' i).1
  have hmassY : ∀ i, fibreMeasure μ N (Y' i) = if i ∈ S then μ (Z i) else 0 := by
    intro i
    by_cases hi : i ∈ S
    · rw [fibreMeasure_single μ (f i) (hY' i) (hY'sub i), if_pos hi]
      congr 1
      ext p
      simp [Y', hi]
    · simp only [Y', if_neg hi, measure_empty]
  have hmassZ : ∀ i, fibreMeasure μ N (Z' i) = μ (Z₁ i) := fun i =>
    fibreMeasure_single μ (f i) (hZ' i).1 (hZ'sub i)
  refine ⟨k, Z₁, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hZ₁m i, ?_, ?_⟩
    · intro p hp
      have h1 := (hZ' i).2 hp
      by_cases hi : i ∈ S
      · simp only [Y', if_pos hi] at h1
        exact h1.2
      · simp only [Y', if_neg hi] at h1
        exact h1.elim
    · intro hi
      ext p
      simp only [Z₁, mem_preimage, mem_empty_iff_false, iff_false]
      intro hp
      have h1 := (hZ' i).2 hp
      simp only [Y', if_neg hi] at h1
      exact h1
  · have h1 : ∑ i ∈ S, μ (Z i) = ∑ i, fibreMeasure μ N (Y' i) := by
      simp_rw [hmassY]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have h2 : ∑ i, fibreMeasure μ N (Z' i) = ∑ i, μ (Z₁ i) :=
      Finset.sum_congr rfl fun i _ => hmassZ i
    rw [h1, ← h2]
    simpa [Fintype.card_fin] using hmass
  · intro j p hp
    obtain ⟨i, hij, hpi⟩ := hp
    have hmem : (j, p) ∈ ⋃ i, Z' i := mem_iUnion.mpr ⟨i, by rw [← hij]; exact hpi⟩
    have hset : (Finset.univ.filter fun i => (j, p) ∈ Z' i) =
        Finset.univ.filter fun i => f i = j ∧ p ∈ Z₁ i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Z₁, mem_preimage]
      constructor
      · intro h
        have := (hZ'sub i h).1
        simp only [mem_singleton_iff] at this
        exact ⟨this.symm, by rw [← this]; exact h⟩
      · rintro ⟨h1, h2⟩
        rw [← h1]
        exact h2
    have hlev := hlevel (j, p) hmem
    refine ⟨by simpa only [hset] using hlev.1,
      by simpa only [hset] using hlev.2.1, ?_⟩
    intro i hfi
    have hi := hlev.2.2 i
    change ((j,p) ∈ Z' i ↔ (j,p) ∈ Y' i) at hi
    change ((f i,p) ∈ Z' i ↔ i ∈ S ∧ p ∈ Z i)
    rw [hfi,hi]
    by_cases hiS : i ∈ S <;> simp [Y',hiS,hfi]


end WangZahlLot.Obl.wz_broad_grains_improvement
