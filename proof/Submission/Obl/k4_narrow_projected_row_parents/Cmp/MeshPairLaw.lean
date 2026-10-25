/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/MeshPairLaw.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Lib.K4OriginalStatePreparation.Smoothing
import Submission.Lib.K4MeshJitter.Pairs

/-!
# A pair law resampled inside finite comparison cells

The coupling from `K4OriginalStatePreparation` keeps the original event while resampling
its base point. Recording both original labels gives the pair law needed for local sheet
matching. Index events have exactly their original mass, and the finite cell caps give
exact index-base density bounds with no factor for the number of cells.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Set
open Submission.Lib.K4OriginalStatePreparation
open scoped ENNReal

noncomputable section

variable {Ω Y Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [Fintype Q]
  {n₁ n₂ : ℕ}

/-- Pieces of the actual original law, partitioned by its finite cell code. -/
def codePieces (μ : Measure Ω) (code : Ω → Q) : Q → Measure Ω :=
  fun q => μ.restrict {p | code p = q}

theorem codePieces_sum [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (code : Ω → Q) (hcode : Measurable code) :
    (∑ q, codePieces μ code q) = μ := by
  apply Submission.Lib.K4MeshJitter.partition_restrict_sum μ (fun q => {p | code p = q})
    (fun q => hcode (measurableSet_singleton q))
  · intro q q' hne
    exact Set.disjoint_left.mpr fun p hp hp' => hne (hp.symm.trans hp')
  · exact Filter.Eventually.of_forall fun p => ⟨code p, rfl⟩

/-- Normalized restriction to a cell of finite positive volume. -/
def uniformCellLaw (β : Measure Y) (cell : Set Y) (V : ℝ≥0∞) : Measure Y :=
  V⁻¹ • β.restrict cell

theorem uniformCellLaw_probability (β : Measure Y) (cell : Set Y) (V : ℝ≥0∞)
    (hV : V ≠ 0) (hVtop : V ≠ ⊤) (hvol : β cell = V) :
    IsProbabilityMeasure (uniformCellLaw β cell V) := by
  constructor
  simp only [uniformCellLaw, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, hvol]
  exact ENNReal.inv_mul_cancel hV hVtop

theorem uniformCellLaw_cap (β : Measure Y) (cell : Set Y) (V : ℝ≥0∞)
    (U : Set Y) (hU : MeasurableSet U) :
    uniformCellLaw β cell V U ≤ V⁻¹ * β (U ∩ cell) := by
  rw [uniformCellLaw, Measure.smul_apply, Measure.restrict_apply hU, smul_eq_mul]

theorem uniformCellLaw_support (β : Measure Y) (cell : Set Y) (V : ℝ≥0∞)
    (hcell : MeasurableSet cell) :
    ∀ᵐ y ∂uniformCellLaw β cell V, y ∈ cell :=
  Measure.ae_smul_measure (ae_restrict_mem hcell) _

/-- The complete original pair of labels, with the resampled base point. -/
def meshPairLaw (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂) : Measure ((Fin n₁ × Fin n₂) × Y) :=
  (cellCoupling pieces cellLaw).map (fun p => ((i₁ p.1, i₂ p.1), p.2))

theorem measurable_pairBase (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂)
    (hi₁ : Measurable i₁) (hi₂ : Measurable i₂) :
    Measurable (fun p : Ω × Y => ((i₁ p.1, i₂ p.1), p.2)) :=
  ((hi₁.comp measurable_fst).prodMk (hi₂.comp measurable_fst)).prodMk measurable_snd

theorem meshPairLaw_finite (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    [∀ q, IsFiniteMeasure (pieces q)] [∀ q, IsProbabilityMeasure (cellLaw q)]
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂) :
    IsFiniteMeasure (meshPairLaw pieces cellLaw i₁ i₂) := by
  have := cellCoupling_finite pieces cellLaw
  unfold meshPairLaw
  infer_instance

/-- An event depending only on the two original labels has unchanged mass. -/
theorem meshPairLaw_index_mass (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    [∀ q, IsFiniteMeasure (pieces q)] [∀ q, IsProbabilityMeasure (cellLaw q)]
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂)
    (hi₁ : Measurable i₁) (hi₂ : Measurable i₂) (E : Set (Fin n₁ × Fin n₂)) :
    meshPairLaw pieces cellLaw i₁ i₂ {p | p.1 ∈ E} =
      (∑ q, pieces q) {p | (i₁ p, i₂ p) ∈ E} := by
  have hE : MeasurableSet E := Set.Finite.measurableSet (Set.toFinite E)
  have hset : MeasurableSet {p : (Fin n₁ × Fin n₂) × Y | p.1 ∈ E} :=
    hE.preimage measurable_fst
  have hpre : (fun p : Ω × Y => ((i₁ p.1, i₂ p.1), p.2)) ⁻¹' {p | p.1 ∈ E} =
      {p | (i₁ p, i₂ p) ∈ E} ×ˢ (univ : Set Y) := by ext p; simp
  rw [meshPairLaw, Measure.map_apply (measurable_pairBase i₁ i₂ hi₁ hi₂)
    hset, hpre]
  simp only [cellCoupling, Measure.finsetSum_apply, Measure.prod_prod, measure_univ, mul_one]

/-- A finite table of index-cell caps becomes an exact index-base marginal bound. -/
theorem meshPairLaw_first_cap (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    [∀ q, IsFiniteMeasure (pieces q)] [∀ q, IsProbabilityMeasure (cellLaw q)]
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂)
    (hi₁ : Measurable i₁) (hi₂ : Measurable i₂)
    (β : Measure Y) (cell : Q → Set Y) (hcell : ∀ q, MeasurableSet (cell q))
    (hdisj : Pairwise (fun q q' => Disjoint (cell q) (cell q')))
    (V A : ℝ≥0∞) (hV : V ≠ 0) (hVtop : V ≠ ⊤) (i : Fin n₁)
    (hcap : ∀ q, pieces q {p | i₁ p = i} ≤ A * V)
    (hk : ∀ q (U : Set Y), MeasurableSet U →
      cellLaw q U ≤ V⁻¹ * β (U ∩ cell q))
    (U : Set Y) (hU : MeasurableSet U) :
    meshPairLaw pieces cellLaw i₁ i₂ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ A * β U := by
  have hset : MeasurableSet {p : (Fin n₁ × Fin n₂) × Y | p.1.1 = i ∧ p.2 ∈ U} :=
    (measurable_fst.fst (measurableSet_singleton i)).inter (hU.preimage measurable_snd)
  have hpre : (fun p : Ω × Y => ((i₁ p.1, i₂ p.1), p.2)) ⁻¹'
      {p | p.1.1 = i ∧ p.2 ∈ U} = {p | i₁ p = i} ×ˢ U := by ext p; simp
  rw [meshPairLaw, Measure.map_apply (measurable_pairBase i₁ i₂ hi₁ hi₂) hset, hpre]
  exact cellCoupling_density pieces cellLaw β cell hcell hdisj V A hV hVtop _ hcap hk U hU

/-- The analogous ceiling for the other color, using its own original weights. -/
theorem meshPairLaw_second_cap (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    [∀ q, IsFiniteMeasure (pieces q)] [∀ q, IsProbabilityMeasure (cellLaw q)]
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂)
    (hi₁ : Measurable i₁) (hi₂ : Measurable i₂)
    (β : Measure Y) (cell : Q → Set Y) (hcell : ∀ q, MeasurableSet (cell q))
    (hdisj : Pairwise (fun q q' => Disjoint (cell q) (cell q')))
    (V A : ℝ≥0∞) (hV : V ≠ 0) (hVtop : V ≠ ⊤) (i : Fin n₂)
    (hcap : ∀ q, pieces q {p | i₂ p = i} ≤ A * V)
    (hk : ∀ q (U : Set Y), MeasurableSet U →
      cellLaw q U ≤ V⁻¹ * β (U ∩ cell q))
    (U : Set Y) (hU : MeasurableSet U) :
    meshPairLaw pieces cellLaw i₁ i₂ {p | p.1.2 = i ∧ p.2 ∈ U} ≤ A * β U := by
  have hset : MeasurableSet {p : (Fin n₁ × Fin n₂) × Y | p.1.2 = i ∧ p.2 ∈ U} :=
    (measurable_fst.snd (measurableSet_singleton i)).inter (hU.preimage measurable_snd)
  have hpre : (fun p : Ω × Y => ((i₁ p.1, i₂ p.1), p.2)) ⁻¹'
      {p | p.1.2 = i ∧ p.2 ∈ U} = {p | i₂ p = i} ×ˢ U := by ext p; simp
  rw [meshPairLaw, Measure.map_apply (measurable_pairBase i₁ i₂ hi₁ hi₂) hset, hpre]
  exact cellCoupling_density pieces cellLaw β cell hcell hdisj V A hV hVtop _ hcap hk U hU

/-- A statement valid throughout the resampling cell holds for the resulting pair law. -/
theorem meshPairLaw_ae (pieces : Q → Measure Ω) (cellLaw : Q → Measure Y)
    [∀ q, IsFiniteMeasure (pieces q)] [∀ q, IsProbabilityMeasure (cellLaw q)]
    (i₁ : Ω → Fin n₁) (i₂ : Ω → Fin n₂)
    (hi₁ : Measurable i₁) (hi₂ : Measurable i₂) (cell : Q → Set Y)
    (hc : ∀ q, ∀ᵐ y ∂cellLaw q, y ∈ cell q)
    (R : ((Fin n₁ × Fin n₂) × Y) → Prop) (hR : MeasurableSet {p | R p})
    (hp : ∀ q, ∀ᵐ p ∂pieces q, ∀ y ∈ cell q, R ((i₁ p, i₂ p), y)) :
    ∀ᵐ p ∂meshPairLaw pieces cellLaw i₁ i₂, R p := by
  rw [meshPairLaw, ae_map_iff (measurable_pairBase i₁ i₂ hi₁ hi₂).aemeasurable hR,
    cellCoupling, ae_finsetSum_measure_iff]
  intro q _
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hp q),
    Measure.quasiMeasurePreserving_snd.ae (hc q)] with z hz hy
  exact hz z.2 hy

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
