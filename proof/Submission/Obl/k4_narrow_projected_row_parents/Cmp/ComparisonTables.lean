/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ComparisonTables.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ComparisonMesh

/-!
# Comparison tables with their original reference weights

This is the finite-table application layer of Lemma 8.3. Each table stores an actual
original source law, its finite comparison mesh, two measurable label maps and the
separate color reference weights. Current individual index masses need no lower floor.
Summing the comparison estimates costs the sum of references, not the number of domains.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set
open scoped ENNReal Classical

noncomputable section

def NearbyListBound {n₁ n₂ : ℕ} (a L d : ℝ)
    (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) : Prop :=
  ∀ (i₀ : Fin n₁) (M : ℝ), a ≤ M →
    ((Finset.univ.filter fun i : Fin n₁ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
      ‖f₁ i (emb x) - f₁ i₀ (emb x)‖ ≤ M).card : ℝ) ≤ L * (M / a) ^ d ∧
    ((Finset.univ.filter fun j : Fin n₂ => ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 2 →
      ‖f₂ j (emb x) - f₁ i₀ (emb x)‖ ≤ M).card : ℝ) ≤ L * (M / a) ^ d

/-- The conclusion of the abstract sheet comparison, for fixed constants. The
actual matching theorem supplies this estimate; no new axiom is introduced. -/
def ComparisonEstimate (D : ℕ) (d ε C : ℝ) : Prop :=
  ∀ (a L CT Λ : ℝ), 0 < a → 1 ≤ L → 0 < CT → C * L ^ (1 / ε) ≤ Λ →
  ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ)
    (f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ) (T₁ : Fin n₁ → ℝ) (T₂ : Fin n₂ → ℝ)
    (μ : Measure ((Fin n₁ × Fin n₂) × EuclideanSpace ℝ (Fin 3))),
  IsFiniteMeasure μ →
  (∀ i, IsSheet D (f₁ i)) → (∀ j, IsSheet D (f₂ j)) →
  (∀ i, 0 ≤ T₁ i) → (∀ j, 0 ≤ T₂ j) →
  (∀ (i : Fin n₁) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    μ {p | p.1.1 = i ∧ p.2 ∈ U} ≤ ENNReal.ofReal (CT * T₁ i) * volume U) →
  (∀ (j : Fin n₂) (U : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet U →
    μ {p | p.1.2 = j ∧ p.2 ∈ U} ≤ ENNReal.ofReal (CT * T₂ j) * volume U) →
  (∀ᵐ p ∂μ, ‖p.2‖ ≤ 1 / 4 ∧ ‖f₁ p.1.1 (emb p.2) - f₂ p.1.2 (emb p.2)‖ ≤ a) →
  NearbyListBound a L d f₁ f₂ →
  μ {p | ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 ∧
    Λ * a ≤ ‖f₁ p.1.1 (emb x) - f₂ p.1.2 (emb x)‖} ≤
    ENNReal.ofReal (C * CT * Λ ^ (-ε) * (∑ i, T₁ i + ∑ j, T₂ j))

structure ComparisonTable (Ω : Type*) [MeasurableSpace Ω] (D : ℕ) (d a L CT : ℝ) where
  law : Measure Ω
  finite : IsFiniteMeasure law
  mesh : ComparisonMesh law
  n₁ : ℕ
  n₂ : ℕ
  i₁ : Ω → Fin n₁
  i₂ : Ω → Fin n₂
  measurable_i₁ : Measurable i₁
  measurable_i₂ : Measurable i₂
  f₁ : Fin n₁ → EuclideanSpace ℂ (Fin 3) → ℂ
  f₂ : Fin n₂ → EuclideanSpace ℂ (Fin 3) → ℂ
  sheet₁ : ∀ i, IsSheet D (f₁ i)
  sheet₂ : ∀ j, IsSheet D (f₂ j)
  T₁ : Fin n₁ → ℝ
  T₂ : Fin n₂ → ℝ
  nonneg₁ : ∀ i, 0 ≤ T₁ i
  nonneg₂ : ∀ j, 0 ≤ T₂ j
  cap₁ : ∀ q i, law {p | mesh.code p = q ∧ i₁ p = i} ≤ ENNReal.ofReal (CT * T₁ i) * mesh.vol
  cap₂ : ∀ q j, law {p | mesh.code p = q ∧ i₂ p = j} ≤ ENNReal.ofReal (CT * T₂ j) * mesh.vol
  lip : NNReal
  lip₁ : ∀ i, LipschitzOnWith lip (fun x => f₁ i (emb x)) (closedBall 0 (1 / 2))
  lip₂ : ∀ j, LipschitzOnWith lip (fun x => f₂ j (emb x)) (closedBall 0 (1 / 2))
  resolved : 2 * (lip : ℝ) * mesh.diameter ≤ a / 2
  agreement : ∀ᵐ p ∂law, ‖f₁ (i₁ p) (emb (mesh.base p)) - f₂ (i₂ p) (emb (mesh.base p))‖ ≤ a / 2
  lists : NearbyListBound a L d f₁ f₂

namespace ComparisonTable

variable {Ω : Type*} [MeasurableSpace Ω] {D : ℕ} {d a L CT : ℝ}
  (t : ComparisonTable Ω D d a L CT)

def referenceTotal : ℝ := ∑ i, t.T₁ i + ∑ j, t.T₂ j

theorem referenceTotal_nonneg : 0 ≤ t.referenceTotal :=
  add_nonneg (Finset.sum_nonneg fun i _ => t.nonneg₁ i)
    (Finset.sum_nonneg fun j _ => t.nonneg₂ j)

def bad (Λ : ℝ) : Set Ω :=
  {p | ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 ∧
    Λ * a ≤ ‖t.f₁ (t.i₁ p) (emb x) - t.f₂ (t.i₂ p) (emb x)‖}

theorem measurableSet_bad (Λ : ℝ) : MeasurableSet (t.bad Λ) := by
  have hE : MeasurableSet {ij : Fin t.n₁ × Fin t.n₂ |
      ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 ∧
        Λ * a ≤ ‖t.f₁ ij.1 (emb x) - t.f₂ ij.2 (emb x)‖} :=
    Set.Finite.measurableSet (Set.toFinite _)
  exact hE.preimage (t.measurable_i₁.prodMk t.measurable_i₂)

/-- Apply matching to the resampled pair law and return the estimate to its literal
original source law. -/
theorem bad_mass_le {ε C Λ : ℝ} (H : ComparisonEstimate D d ε C)
    (ha : 0 < a) (hL : 1 ≤ L) (hCT : 0 < CT) (hΛ : C * L ^ (1 / ε) ≤ Λ) :
    t.law (t.bad Λ) ≤ ENNReal.ofReal (C * CT * Λ ^ (-ε) * t.referenceTotal) := by
  haveI := t.finite
  haveI (q : Fin t.mesh.n) : IsFiniteMeasure (t.mesh.pieces q) := by
    dsimp [ComparisonMesh.pieces, codePieces]
    infer_instance
  haveI (q : Fin t.mesh.n) : IsProbabilityMeasure (t.mesh.cellLaws q) :=
    uniformCellLaw_probability volume (t.mesh.cell q) t.mesh.vol
      t.mesh.vol_ne_zero t.mesh.vol_ne_top (t.mesh.cell_volume q)
  have hfin := meshPairLaw_finite t.mesh.pieces t.mesh.cellLaws t.i₁ t.i₂
  have hmar₁ := fun i U hU => meshPairLaw_first_cap t.mesh.pieces t.mesh.cellLaws t.i₁ t.i₂
    t.measurable_i₁ t.measurable_i₂ volume t.mesh.cell t.mesh.measurable_cell t.mesh.disjoint_cell
    t.mesh.vol (ENNReal.ofReal (CT * t.T₁ i)) t.mesh.vol_ne_zero t.mesh.vol_ne_top i
    (t.mesh.pieces_index_cap t.i₁ t.measurable_i₁ i _ (fun q => t.cap₁ q i))
    t.mesh.cellLaws_cap U hU
  have hmar₂ := fun j U hU => meshPairLaw_second_cap t.mesh.pieces t.mesh.cellLaws t.i₁ t.i₂
    t.measurable_i₁ t.measurable_i₂ volume t.mesh.cell t.mesh.measurable_cell t.mesh.disjoint_cell
    t.mesh.vol (ENNReal.ofReal (CT * t.T₂ j)) t.mesh.vol_ne_zero t.mesh.vol_ne_top j
    (t.mesh.pieces_index_cap t.i₂ t.measurable_i₂ j _ (fun q => t.cap₂ q j))
    t.mesh.cellLaws_cap U hU
  have hclose := t.mesh.cell_agreement t.i₁ t.i₂ (fun i x => t.f₁ i (emb x))
    (fun j x => t.f₂ j (emb x)) t.lip t.resolved t.lip₁ t.lip₂ t.agreement
  have hae := meshPairLaw_ae t.mesh.pieces t.mesh.cellLaws t.i₁ t.i₂
    t.measurable_i₁ t.measurable_i₂ t.mesh.cell t.mesh.cellLaws_support
    (fun p => ‖p.2‖ ≤ 1 / 4 ∧ ‖t.f₁ p.1.1 (emb p.2) - t.f₂ p.1.2 (emb p.2)‖ ≤ a)
    (measurableSet_pair_sheet_close t.f₁ t.f₂ t.sheet₁ t.sheet₂ (by norm_num) a) hclose
  have h := H a L CT Λ ha hL hCT hΛ t.n₁ t.n₂ t.f₁ t.f₂ t.T₁ t.T₂
    (t.mesh.pairedLaw t.i₁ t.i₂) hfin t.sheet₁ t.sheet₂ t.nonneg₁ t.nonneg₂ hmar₁ hmar₂ hae t.lists
  have hmass := t.mesh.pairedLaw_index_mass t.i₁ t.i₂ t.measurable_i₁ t.measurable_i₂
    {ij | ∃ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 ∧
      Λ * a ≤ ‖t.f₁ ij.1 (emb x) - t.f₂ ij.2 (emb x)‖}
  exact hmass ▸ h

end ComparisonTable

/-- All common domains share one estimate and one reference budget. There is no
factor for the number of domains. -/
theorem comparison_tables_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {D : ℕ} {d a L CT ε C Λ : ℝ} (H : ComparisonEstimate D d ε C)
    (hC : 0 ≤ C) (ha : 0 < a) (hL : 1 ≤ L) (hCT : 0 < CT)
    (hΛ : C * L ^ (1 / ε) ≤ Λ)
    (t : ι → ComparisonTable Ω D d a L CT) :
    (∑ i, (t i).law ((t i).bad Λ)) ≤
      ENNReal.ofReal (C * CT * Λ ^ (-ε) * ∑ i, (t i).referenceTotal) := by
  have hΛ0 : 0 ≤ Λ :=
    (mul_nonneg hC (Real.rpow_nonneg ((zero_le_one : (0 : ℝ) ≤ 1).trans hL) _)).trans hΛ
  calc
    _ ≤ ∑ i, ENNReal.ofReal (C * CT * Λ ^ (-ε) * (t i).referenceTotal) :=
      Finset.sum_le_sum fun i _ => (t i).bad_mass_le H ha hL hCT hΛ
    _ = _ := by
      rw [Finset.mul_sum]
      exact (ENNReal.ofReal_sum_of_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (mul_nonneg hC hCT.le) (Real.rpow_nonneg hΛ0 _))
          (t i).referenceTotal_nonneg).symm

/-- When a domain table uses the original restriction, its agreement estimate is
charged to that same original measure. -/
theorem comparison_tables_union {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {D : ℕ} {d a L CT ε C Λ : ℝ} (H : ComparisonEstimate D d ε C)
    (hC : 0 ≤ C) (ha : 0 < a) (hL : 1 ≤ L) (hCT : 0 < CT)
    (hΛ : C * L ^ (1 / ε) ≤ Λ) (μ : Measure Ω)
    (domain : ι → Set Ω) (t : ι → ComparisonTable Ω D d a L CT)
    (hlaw : ∀ i, (t i).law = μ.restrict (domain i)) :
    μ (⋃ i, domain i ∩ (t i).bad Λ) ≤
      ENNReal.ofReal (C * CT * Λ ^ (-ε) * ∑ i, (t i).referenceTotal) := by
  calc
    _ ≤ ∑ i, μ (domain i ∩ (t i).bad Λ) := measure_iUnion_fintype_le _ _
    _ = ∑ i, (t i).law ((t i).bad Λ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hlaw i, Measure.restrict_apply ((t i).measurableSet_bad Λ), inter_comm]
    _ ≤ _ := comparison_tables_sum H hC ha hL hCT hΛ t

/-- Delete the union of the original bad-pair events once. Every remaining pairing
agrees uniformly on its entire comparison ball in every retained domain. -/
theorem exists_comparison_restriction {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {D : ℕ} {d a L CT ε C Λ : ℝ} (H : ComparisonEstimate D d ε C)
    (hC : 0 ≤ C) (ha : 0 < a) (hL : 1 ≤ L) (hCT : 0 < CT)
    (hΛ : C * L ^ (1 / ε) ≤ Λ) (μ : Measure Ω)
    (domain : ι → Set Ω) (hdomain : ∀ i, MeasurableSet (domain i))
    (t : ι → ComparisonTable Ω D d a L CT)
    (hlaw : ∀ i, (t i).law = μ.restrict (domain i)) :
    ∃ G : Set Ω, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal (C * CT * Λ ^ (-ε) * ∑ i, (t i).referenceTotal) ∧
      ∀ i p, p ∈ G → p ∈ domain i → ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
        ‖(t i).f₁ ((t i).i₁ p) (emb x) - (t i).f₂ ((t i).i₂ p) (emb x)‖ ≤ Λ * a := by
  let Bad : Set Ω := ⋃ i, domain i ∩ (t i).bad Λ
  have hBad : MeasurableSet Bad :=
    MeasurableSet.iUnion fun i => (hdomain i).inter ((t i).measurableSet_bad Λ)
  refine ⟨Badᶜ, hBad.compl, ?_, ?_⟩
  · simpa only [compl_compl] using comparison_tables_union H hC ha hL hCT hΛ μ domain t hlaw
  · intro i p hp hd x hx
    by_contra h
    exact hp (mem_iUnion.mpr ⟨i, hd, x, hx, (not_le.mp h).le⟩)

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
