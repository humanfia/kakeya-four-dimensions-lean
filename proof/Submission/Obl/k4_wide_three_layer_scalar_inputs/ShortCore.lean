import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.ShortBound
import Submission.Obl.k4_wide_three_layer_scalar_inputs.ReferenceSelection
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs

open Set MeasureTheory Filter
open Inherited.Native Inherited.Core

noncomputable section

/-- Delete one measurable exceptional set, retaining an absolute mass
floor. All later restrictions remain submeasures of the original law. -/
theorem restrict_compl_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E)
    {mass cost kept : ℝ} (hkept : 0 ≤ kept) (hcost : 0 ≤ cost)
    (hmass : ENNReal.ofReal mass ≤ μ univ)
    (hbad : μ E ≤ ENNReal.ofReal cost) (hkeep : kept + cost ≤ mass) :
    ENNReal.ofReal kept ≤ (μ.restrict Eᶜ) univ := by
  have h := (ENNReal.ofReal_le_ofReal hkeep).trans hmass
  rw [ENNReal.ofReal_add hkept hcost] at h
  have hsplit : μ univ ≤ μ Eᶜ + ENNReal.ofReal cost := by
    calc μ univ = μ Eᶜ + μ E := by
          rw [← measure_union disjoint_compl_left hE, compl_union_self]
      _ ≤ _ := add_le_add le_rfl hbad
  simpa using (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp (h.trans hsplit)

variable {α : Type} [MeasurableSpace α]

theorem measurableSet_shortBad (cfg : Inherited.Data α) (k : ℕ) (s : ℝ)
    {ε R χ D R' m K₁ Mst : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (hB : BlocksAt cfg k s R')
    (hb : Measurable (cfg.b k)) (KB : Finset (Fin 3 → ℤ)) :
    MeasurableSet (shortBad cfg k s L m K₁ Mst KB) := by
  have hblock : ∀ i key, MeasurableSet (blockLab cfg k s L m i key) := by
    intro i key
    exact (((hB.sets i).2.1.inter (measurableSet_goodLab L)).inter
      (measurableSet_slotKey hb _ _ _ key))
  have hpiece : ∀ h i jj key, MeasurableSet (pieceLab cfg k s L m h i jj key) := by
    intro h i jj key
    exact (L.meas h i).inter (measurableSet_slotKey hb _ _ _ key)
  unfold shortBad
  refine (MeasurableSet.union ?_ ?_).union ?_
  · refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun key =>
      MeasurableSet.iUnion fun _ => ?_
    exact ((hblock i key).prod measurableSet_Icc).inter (MeasurableSet.const _)
  · refine MeasurableSet.iUnion fun h => MeasurableSet.iUnion fun i =>
      MeasurableSet.iUnion fun jj => MeasurableSet.iUnion fun key =>
        MeasurableSet.iUnion fun _ => ?_
    exact ((hpiece h i jj key).prod measurableSet_Icc).inter (MeasurableSet.const _)
  · refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun i₀ =>
      MeasurableSet.iUnion fun key => MeasurableSet.iUnion fun _ => ?_
    exact (((hblock i key).inter (hpiece 0 i₀ (cfg.j k s i) key)).prod
      measurableSet_Icc).inter (MeasurableSet.const _)

/-- The full original assignment references have budget one. The
assignments are disjoint within a time slot, before any restriction. -/
theorem full_assignment_references {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {n T : ℕ}
    (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set Ω)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')) :
    ∑ i, ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) * ν (A i) ≤ 1 := by
  have hh := Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget
    (fun _ : Unit => ν) (fun _ : Unit => (1 : ENNReal)) (fun _ : Fin n => ()) j A
    (fun _ => measure_univ) (by simp) hA (fun i i' hne _ heq => hdisj i i' hne heq)
  simp only [one_mul, Fintype.card_fin] at hh
  rw [← Finset.mul_sum]
  calc ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) * ∑ i, ν (A i)
      ≤ ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) * (2 ^ T : ℕ) :=
        mul_le_mul' le_rfl hh
    _ = 1 := by
      rw [ENNReal.ofReal_inv_of_pos (by positivity)]
      norm_num [ENNReal.ofReal_pow]
      exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

/-- The short comparison and original atlas cover hold on one common
retained law. No projected family is replaced or pruned separately. -/
theorem short_comparison_core (cfg : Inherited.Data α) (k : ℕ) (s : ℝ)
    {ε R χ D R' m K₁ Mst mass cost kept : ℝ} {depth : Fin 3 → ℝ}
    (L : LayerDatum cfg k ε R χ D depth) (hB : BlocksAt cfg k s R')
    (hb : Measurable (cfg.b k)) (hρμ : L.ρs ≤ cfg.μ k)
    (KB : Finset (Fin 3 → ℤ)) (hkept : 0 ≤ kept) (hcost : 0 ≤ cost)
    (hmass : ENNReal.ofReal mass ≤ L.ρs univ)
    (hbad : L.ρs (shortBad cfg k s L m K₁ Mst KB) ≤ ENNReal.ofReal cost)
    (hkeep : kept + cost ≤ mass) :
    ∃ τ : Measure (α × ℝ), τ ≤ L.ρs ∧ ENNReal.ofReal kept ≤ τ univ ∧
      (∀ᵐ p ∂τ, ∀ h : Fin 3, ∃ i, p.1 ∈ L.C h i) ∧
      (∀ᵐ p ∂τ, ∃ i, p.1 ∈ cfg.B k s i ∧
        p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i)) ∧
      (∀ᵐ p ∂τ, ∀ i, p.1 ∈ cfg.B k s i →
        p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i) →
        slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1 ∈ KB →
        blockHeavy cfg k s L m K₁ i
          (slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1) ∧
        (∀ h ih, p.1 ∈ L.C h ih → pieceHeavy cfg k s L m K₁ h ih (cfg.j k s i)
          (slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1)) ∧
        (∀ i₀, p.1 ∈ L.C 0 i₀ → ¬ pairBad cfg k s L m Mst i i₀
          (slotKey (cfg.b k) χ m (slotStart cfg k s (cfg.j k s i)) p.1))) := by
  let Bad := shortBad cfg k s L m K₁ Mst KB
  have hBad := measurableSet_shortBad cfg k s L hB hb KB (m := m) (K₁ := K₁) (Mst := Mst)
  let τ := L.ρs.restrict Badᶜ
  have hτ : τ ≤ L.ρs := Measure.restrict_le_self
  have hcover : ∀ᵐ p ∂τ, ∀ h : Fin 3, ∃ i, p.1 ∈ L.C h i :=
    ae_mono hτ L.cover
  refine ⟨τ, hτ, restrict_compl_mass L.ρs Bad hBad hkept hcost hmass hbad hkeep,
    hcover, ae_mono (hτ.trans hρμ) hB.cover, ?_⟩
  filter_upwards [ae_restrict_mem hBad.compl, hcover] with p hp hc i hi ht hKB
  exact short_good cfg k s L m K₁ Mst KB hp
    (mem_iUnion.mpr (hc 0)) i hi ht hKB

/-- Choose an original true block after the common restriction, keeping
its full original prior in the density floor. -/
theorem exists_dense_original_block (cfg : Inherited.Data α) (k : ℕ) (s : ℝ)
    {R' mass : ℝ} (hB : BlocksAt cfg k s R')
    [IsProbabilityMeasure (cfg.ν k)] (τ : Measure (α × ℝ))
    (hτ : τ ≤ cfg.μ k) (hmass : 0 < mass)
    (hm : ENNReal.ofReal mass ≤ τ univ) :
    ∃ (i : Fin (cfg.n k s)) (lam : Measure (α × ℝ)), lam ≤ τ ∧
      (∀ᵐ p ∂lam, p.1 ∈ cfg.B k s i ∧ p.2 ∈ cfg.I (cfg.T k s) (cfg.j k s i)) ∧
      ENNReal.ofReal mass * (ENNReal.ofReal (slotLen cfg k s) * cfg.ν k (cfg.A k s i)) ≤
        lam univ := by
  let E := fun i => cfg.B k s i ×ˢ cfg.I (cfg.T k s) (cfg.j k s i)
  have hE : ∀ i, MeasurableSet (E i) := fun i => (hB.sets i).2.1.prod measurableSet_Icc
  obtain ⟨i, hi⟩ := exists_dense_reference_entry τ E
    (fun i => ENNReal.ofReal (slotLen cfg k s) * cfg.ν k (cfg.A k s i)) hmass hm
    (ae_mono hτ hB.cover)
    (full_assignment_references (cfg.ν k) (cfg.j k s) (cfg.A k s)
      (fun i => (hB.sets i).1) hB.disj)
  refine ⟨i, τ.restrict (E i), Measure.restrict_le_self, ?_, ?_⟩
  · exact ae_restrict_mem (hE i)
  · simpa using hi

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs
