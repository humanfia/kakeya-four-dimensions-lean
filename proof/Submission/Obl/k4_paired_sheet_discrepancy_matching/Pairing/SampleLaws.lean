/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/SampleLaws.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.TestedSample
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.FinitePairLaw

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep.TestedSample

open MeasureTheory Set Metric

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

abbrev block (b : Fin s.J) : Set ℝ :=
  Icc ((s.j b : ℝ) / (2 : ℝ) ^ s.T) (((s.j b : ℝ) + 1) / (2 : ℝ) ^ s.T)

noncomputable def baseAt (b : Fin s.J) (p : PairPoint) : EuclideanSpace ℝ (Fin 3) :=
  base s.T (s.j b : ℝ) s.κ (s.c b) (s.u b) (s.Q b) p.1 p.2.1

noncomputable def hiddenAt (b : Fin s.J) (p : PairPoint) : ℝ :=
  Bk (s.γ b) * (x p.1 p.2.1) 3

/-- Normalize both times while retaining the original trajectory measure. -/
noncomputable def frameLaw (b : Fin s.J) : Measure PairPoint :=
  ENNReal.ofReal ((2 : ℝ) ^ s.T) ^ 2 •
    ((νk (s.γ b)).prod (volume.prod volume))

noncomputable def frameWeight (b : Fin s.J) : ℝ := ωk (s.γ b) / (2 : ℝ) ^ s.T

abbrev Active := FinitePairLaw.active s.H

noncomputable def pairMeasure : Measure s.Active :=
  FinitePairLaw.supportedLaw (fun i => s.frameLaw (s.frame i))
    (fun i => s.frameWeight (s.frame i)) s.H

abbrev src (p : s.Active) : Fin s.m := FinitePairLaw.source s.H p
noncomputable def wit (p : s.Active) : Fin s.m := FinitePairLaw.witness s.H p
abbrev point (p : s.Active) : PairPoint := FinitePairLaw.point s.H p

noncomputable def sourceBase (p : s.Active) : EuclideanSpace ℝ (Fin 3) :=
  s.baseAt (s.frame (s.src p)) (s.point p)

noncomputable def sourceHidden (p : s.Active) : ℝ :=
  s.hiddenAt (s.frame (s.src p)) (s.point p)

theorem measurable_baseAt (b : Fin s.J) : Measurable (s.baseAt b) := by
  unfold baseAt base y x
  fun_prop

theorem measurable_hiddenAt (b : Fin s.J) : Measurable (s.hiddenAt b) := by
  unfold hiddenAt x
  fun_prop

theorem measurable_sourceBase : Measurable s.sourceBase := by
  have h : Measurable (fun p : Fin s.m × PairPoint => s.baseAt (s.frame p.1) p.2) := by
    apply measurable_from_prod_countable_right
    intro i
    change Measurable (s.baseAt (s.frame i))
    exact s.measurable_baseAt (s.frame i)
  exact h.comp measurable_subtype_coe

theorem measurable_sourceHidden : Measurable s.sourceHidden := by
  have h : Measurable (fun p : Fin s.m × PairPoint => s.hiddenAt (s.frame p.1) p.2) := by
    apply measurable_from_prod_countable_right
    intro i
    change Measurable (s.hiddenAt (s.frame i))
    exact s.measurable_hiddenAt (s.frame i)
  exact h.comp measurable_subtype_coe

theorem measurableSet_src_eq (i : Fin s.m) : MeasurableSet {p | s.src p = i} :=
  (FinitePairLaw.measurable_source s.H) (measurableSet_singleton i)

theorem measurableSet_wit_eq (i : Fin s.m) : MeasurableSet {p | s.wit p = i} :=
  FinitePairLaw.measurableSet_witness_eq s.H (fun i j => (s.hH i j).1) i

theorem witness_mem (p : s.Active) : s.point p ∈ s.H (s.src p) (s.wit p) :=
  FinitePairLaw.witness_mem s.H p

theorem frame_src_wit (p : s.Active) : s.frame (s.src p) = s.frame (s.wit p) :=
  ((s.hH _ _).2 _ (s.witness_mem p)).2.2.2.2.1.symm

theorem row_source (i : Fin s.m) {p : PairPoint} (hp : p ∈ FinitePairLaw.row s.H i) :
    (p.1, p.2.1) ∈ s.S i := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hp
  exact ((s.hH i j).2 p hj).1

theorem row_base_norm (i : Fin s.m) {p : PairPoint}
    (hp : p ∈ FinitePairLaw.row s.H i) : ‖s.baseAt (s.frame i) p‖ ≤ 1 / 8 := by
  have hS := (s.hS i).2.2 _ (s.row_source i hp)
  exact (hS.2.2.2.2 _ hS.2.2.2.1).2.2.1

theorem sourceBase_norm (p : s.Active) : ‖s.sourceBase p‖ ≤ 1 / 8 :=
  s.row_base_norm _ p.property

theorem rows_disjoint (i i' : Fin s.m) (hne : i ≠ i') (heq : s.frame i = s.frame i') :
    Disjoint (FinitePairLaw.row s.H i) (FinitePairLaw.row s.H i') := by
  apply Set.disjoint_left.mpr
  intro p hp hp'
  exact Set.disjoint_left.mp (s.hdisj i i' hne (congrArg s.γ heq) (congrArg s.j heq))
    (s.row_source i hp) (s.row_source i' hp')

theorem columns_disjoint (j : Fin s.m) : Pairwise (fun i i' => Disjoint (s.H i j) (s.H i' j)) := by
  intro i i' hne
  apply Set.disjoint_left.mpr
  intro p hp hp'
  have hi := ((s.hH i j).2 p hp).2.2.2.2.1
  have hi' := ((s.hH i' j).2 p hp').2.2.2.2.1
  exact Set.disjoint_left.mp (s.rows_disjoint i i' hne (hi.symm.trans hi'))
    (mem_iUnion.mpr ⟨j, hp⟩) (mem_iUnion.mpr ⟨j, hp'⟩)

theorem frameLaw_row_density (i : Fin s.m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : MeasurableSet U) :
    s.frameLaw (s.frame i) (FinitePairLaw.row s.H i ∩ s.baseAt (s.frame i) ⁻¹' U) ≤
      ENNReal.ofReal (s.β i) * volume U := by
  have heq : FinitePairLaw.row s.H i ∩ s.baseAt (s.frame i) ⁻¹' U =
      {p | (∃ j, p ∈ s.H i j) ∧ s.baseAt (s.frame i) p ∈ U} := by
    ext p
    simp only [FinitePairLaw.row, mem_inter_iff, mem_iUnion, mem_preimage, mem_setOf_eq]
  rw [heq]
  exact (s.hβ i).2.2 U hU |>.1

theorem frameLaw_column_density (i : Fin s.m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (hU : MeasurableSet U) :
    s.frameLaw (s.frame i) ((⋃ j, s.H j i) ∩ s.baseAt (s.frame i) ⁻¹' U) ≤
      ENNReal.ofReal (s.β i) * volume U := by
  have heq : (⋃ j, s.H j i) ∩ s.baseAt (s.frame i) ⁻¹' U =
      {p | (∃ j, p ∈ s.H j i) ∧ s.baseAt (s.frame i) p ∈ U} := by
    ext p
    simp only [mem_inter_iff, mem_iUnion, mem_preimage, mem_setOf_eq]
  rw [heq]
  exact (s.hβ i).2.2 U hU |>.2

theorem row_finite (i : Fin s.m) : s.frameLaw (s.frame i) (FinitePairLaw.row s.H i) ≠ ⊤ := by
  have heq : FinitePairLaw.row s.H i = FinitePairLaw.row s.H i ∩
      s.baseAt (s.frame i) ⁻¹' closedBall 0 (1 / 8) := by
    apply (inter_eq_left.mpr ?_).symm
    intro p hp
    exact mem_closedBall_zero_iff.mpr (s.row_base_norm i hp)
  rw [heq]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (isCompact_closedBall _ _).measure_ne_top)
    (s.frameLaw_row_density i _ measurableSet_closedBall)

theorem pairMeasure_finite : IsFiniteMeasure s.pairMeasure :=
  FinitePairLaw.supportedLaw_finite _ _ s.H (fun i j => (s.hH i j).1) s.row_finite

noncomputable def sourceCeiling (b : Fin s.J) : ℝ :=
  s.frameWeight b * (s.σ * Nk ^ a)

theorem frameWeight_nonneg (hω : ∀ γ, 0 ≤ ωk γ) (b : Fin s.J) :
    0 ≤ s.frameWeight b := div_nonneg (hω _) (by positivity)

theorem sourceCeiling_nonneg (hω : ∀ γ, 0 ≤ ωk γ) (hNk : 0 ≤ Nk) (b : Fin s.J) :
    0 ≤ s.sourceCeiling b :=
  mul_nonneg (s.frameWeight_nonneg hω b)
    (mul_nonneg s.σ_pos.le (Real.rpow_nonneg hNk _))

theorem source_density (hω : ∀ γ, 0 ≤ ωk γ) (i : Fin s.m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    s.pairMeasure {p | s.src p = i ∧ s.sourceBase p ∈ U} ≤
      ENNReal.ofReal (s.sourceCeiling (s.frame i)) * volume U := by
  have hw := s.frameWeight_nonneg hω (s.frame i)
  have hb := FinitePairLaw.source_bound (fun i => s.frameLaw (s.frame i))
    (fun i => s.frameWeight (s.frame i)) s.H (fun i j => (s.hH i j).1) i
    (s.baseAt (s.frame i) ⁻¹' U)
  calc
    _ ≤ s.pairMeasure {p | s.src p = i ∧ s.point p ∈ s.baseAt (s.frame i) ⁻¹' U} := by
      apply measure_mono
      rintro p ⟨hi, hp⟩
      exact ⟨hi, by simpa only [mem_preimage, sourceBase, hi] using hp⟩
    _ ≤ ENNReal.ofReal (s.frameWeight (s.frame i)) * s.frameLaw (s.frame i)
        (FinitePairLaw.row s.H i ∩ s.baseAt (s.frame i) ⁻¹' U) := hb
    _ ≤ ENNReal.ofReal (s.frameWeight (s.frame i) * s.β i) * volume U := by
      rw [ENNReal.ofReal_mul hw, mul_assoc]
      exact mul_le_mul' le_rfl (s.frameLaw_row_density i U hU)
    _ ≤ ENNReal.ofReal (s.sourceCeiling (s.frame i)) * volume U := by
      apply mul_le_mul' _ le_rfl
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (s.hβ i).2.1 hw)

theorem witness_density (hω : ∀ γ, 0 ≤ ωk γ) (i : Fin s.m)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    s.pairMeasure {p | s.wit p = i ∧ s.sourceBase p ∈ U} ≤
      ENNReal.ofReal (s.sourceCeiling (s.frame i)) * volume U := by
  have hw := s.frameWeight_nonneg hω (s.frame i)
  have hb := FinitePairLaw.witness_bound s.frameLaw s.frameWeight s.frame s.H
    (fun i j => (s.hH i j).1)
    (fun i j p hp => ((s.hH i j).2 p hp).2.2.2.2.1.symm)
    s.columns_disjoint i (s.baseAt (s.frame i) ⁻¹' U)
    (hU.preimage (s.measurable_baseAt _))
  calc
    _ ≤ s.pairMeasure {p | s.wit p = i ∧ s.point p ∈ s.baseAt (s.frame i) ⁻¹' U} := by
      apply measure_mono
      rintro p ⟨hi, hp⟩
      have hf : s.frame (s.src p) = s.frame i :=
        (s.frame_src_wit p).trans (congrArg s.frame hi)
      exact ⟨hi, by simpa only [mem_preimage, sourceBase, hf] using hp⟩
    _ ≤ ENNReal.ofReal (s.frameWeight (s.frame i)) * s.frameLaw (s.frame i)
        ((⋃ j, s.H j i) ∩ s.baseAt (s.frame i) ⁻¹' U) := hb
    _ ≤ ENNReal.ofReal (s.frameWeight (s.frame i) * s.β i) * volume U := by
      rw [ENNReal.ofReal_mul hw, mul_assoc]
      exact mul_le_mul' le_rfl (s.frameLaw_column_density i U hU)
    _ ≤ ENNReal.ofReal (s.sourceCeiling (s.frame i)) * volume U := by
      apply mul_le_mul' _ le_rfl
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (s.hβ i).2.1 hw)

/-- The raw band's frame cap survives passage to the one chosen witness. -/
theorem band_density (hω : ∀ γ, 0 ≤ ωk γ) (b : Fin s.J) (ρ : ℝ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (g : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hρ : 0 < ρ) (hU : MeasurableSet U) (hg : Measurable g) :
    s.pairMeasure {p | s.frame (s.src p) = b ∧ s.sourceBase p ∈ U ∧
      |s.sourceHidden p - g (s.sourceBase p)| ≤ ρ} ≤
      ENNReal.ofReal (s.sourceCeiling b * (max ρ (δ Nk L) / δ Nk L) ^ dc) * volume U := by
  let V : Set PairPoint := {p | s.baseAt b p ∈ U ∧ |s.hiddenAt b p - g (s.baseAt b p)| ≤ ρ}
  have hV : MeasurableSet V :=
    (hU.preimage (s.measurable_baseAt b)).inter
      (measurableSet_le (((s.measurable_hiddenAt b).sub (hg.comp (s.measurable_baseAt b))).abs)
        measurable_const)
  have hb := FinitePairLaw.frame_bound s.frameLaw s.frameWeight s.frame s.H
    (fun i j => (s.hH i j).1) s.rows_disjoint b V hV
  have heq : ((⋃ i, ⋃ (_ : s.frame i = b), FinitePairLaw.row s.H i) ∩ V) =
      {p | (∃ i j, s.frame i = b ∧ p ∈ s.H i j) ∧ s.baseAt b p ∈ U ∧
        |s.hiddenAt b p - g (s.baseAt b p)| ≤ ρ} := by
    ext p
    simp only [FinitePairLaw.row, mem_inter_iff, mem_iUnion, exists_prop, V, mem_setOf_eq]
    aesop
  calc
    _ ≤ s.pairMeasure {p | s.frame (s.src p) = b ∧ s.point p ∈ V} := by
      apply measure_mono
      rintro p ⟨hf, hp, hnear⟩
      refine ⟨hf, ?_⟩
      simpa only [V, mem_setOf_eq, sourceBase, sourceHidden, hf] using And.intro hp hnear
    _ ≤ ENNReal.ofReal (s.frameWeight b) * s.frameLaw b
        ((⋃ i, ⋃ (_ : s.frame i = b), FinitePairLaw.row s.H i) ∩ V) := hb
    _ ≤ ENNReal.ofReal (s.frameWeight b) *
        (ENNReal.ofReal (s.σ * Nk ^ a * (max ρ (δ Nk L) / δ Nk L) ^ dc) * volume U) := by
      apply mul_le_mul' le_rfl
      rw [heq]
      exact s.hband b ρ U g hρ hU hg
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (s.frameWeight_nonneg hω b)]
      congr 2
      dsimp [sourceCeiling]
      ring

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.NormalizationStep.TestedSample
