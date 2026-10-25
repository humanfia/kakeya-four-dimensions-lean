/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/PrunedDomainTables.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.PrunedComparisonTable
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.GlobalDomainComparison

/-! Prepare both original colors on all literal common domains. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section

theorem exists_pruned_domain_tables {Ω Q : Type*} [MeasurableSpace Ω]
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → Q)
    {D : ℕ} {d a B F L : ℝ} (K : NNReal)
    (M : ∀ q, ComparisonMesh (codePieces μ code q))
    (signal : Ω → ℝ) (hs : Measurable signal)
    (f₁ f₂ : ∀ q, OriginalSheetFamily (codePieces μ code q) D a K (M q).base signal)
    (ha : 0 < a) (hB : 0 < B) (hF : 0 < F) (hL : 14 * B * F ≤ L)
    (T : Q → ℝ) (hT : ∀ q, 0 < T q)
    (palette : Q → ℝ≥0∞) (hp : ∀ q, palette q ≠ 0) (hpt : ∀ q, palette q ≠ ⊤)
    (hresolve : ∀ q, 2 * (K : ℝ) * (M q).diameter ≤ a / 2)
    (hvolume : ∀ q, (∑ _j : Fin (M q).n, (M q).vol) ≤ 1)
    (hnative : ∀ q (R : ℝ), a ≤ R → ∀ j x,
      codePieces μ code q {p | (M q).code p = j ∧ ⌊signal p / R⌋ = x} ≤
        (ENNReal.ofReal (B * T q * (R / a) ^ d) * palette q) * (M q).vol) :
    ∃ (law : Q → Measure Ω) (active : Finset Q)
      (table : (q : active) → ComparisonTable Ω D d a L (6 * B)),
      (∀ q, law q ≤ codePieces μ code q) ∧
      (∀ q, codePieces μ code q univ ≤ law q univ +
        ((f₁ q).n : ℝ≥0∞) * (ENNReal.ofReal (T q / F) * palette q) +
        ((f₂ q).n : ℝ≥0∞) * (ENNReal.ofReal (T q / F) * palette q)) ∧
      (∀ q, q ∉ active → law q = 0) ∧
      (∀ q, (table q).law = law q.val) ∧
      (∑ q, (table q).referenceTotal) ≤
        ∑ q, (((f₁ q).n : ℝ) * (T q * (palette q).toReal) +
          ((f₂ q).n : ℝ) * (T q * (palette q).toReal)) ∧
      ∀ q : active,
        QuarterListBound a L d (table q).f₁ (table q).f₂ ∧
        ∃ (idx₁ : Fin (table q).n₁ → Fin (f₁ q.val).n)
          (idx₂ : Fin (table q).n₂ → Fin (f₂ q.val).n),
          Function.Injective idx₁ ∧ Function.Injective idx₂ ∧
          (∀ i, ENNReal.ofReal (T q.val / F) * palette q.val ≤
            codePieces μ code q.val ((f₁ q.val).witness (idx₁ i))) ∧
          (∀ j, ENNReal.ofReal (T q.val / F) * palette q.val ≤
            codePieces μ code q.val ((f₂ q.val).witness (idx₂ j))) ∧
          (∀ i, (table q).f₁ i = (f₁ q.val).f (idx₁ i)) ∧
          (∀ j, (table q).f₂ j = (f₂ q.val).f (idx₂ j)) ∧
          ∀ᵐ p ∂law q.val,
            idx₁ ((table q).i₁ p) = (f₁ q.val).index p ∧
            idx₂ ((table q).i₂ p) = (f₂ q.val).index p := by
  let loss (q : Q) : ℝ≥0∞ :=
    ((f₁ q).n : ℝ≥0∞) * (ENNReal.ofReal (T q / F) * palette q) +
      ((f₂ q).n : ℝ≥0∞) * (ENNReal.ofReal (T q / F) * palette q)
  let reference (q : Q) : ℝ :=
    ((f₁ q).n : ℝ) * (T q * (palette q).toReal) +
      ((f₂ q).n : ℝ) * (T q * (palette q).toReal)
  have hlocal (q : Q) : ∃ τ : Measure Ω,
      τ ≤ codePieces μ code q ∧ codePieces μ code q univ ≤ τ univ + loss q ∧
      (τ = 0 ∨ ∃ t : ComparisonTable Ω D d a L (6 * B),
        t.law = τ ∧ t.referenceTotal ≤ reference q ∧ QuarterListBound a L d t.f₁ t.f₂ ∧
        ∃ (idx₁ : Fin t.n₁ → Fin (f₁ q).n) (idx₂ : Fin t.n₂ → Fin (f₂ q).n),
          Function.Injective idx₁ ∧ Function.Injective idx₂ ∧
          (∀ i, ENNReal.ofReal (T q / F) * palette q ≤ codePieces μ code q ((f₁ q).witness (idx₁ i))) ∧
          (∀ j, ENNReal.ofReal (T q / F) * palette q ≤ codePieces μ code q ((f₂ q).witness (idx₂ j))) ∧
          (∀ i, t.f₁ i = (f₁ q).f (idx₁ i)) ∧ (∀ j, t.f₂ j = (f₂ q).f (idx₂ j)) ∧
          ∀ᵐ p ∂τ, idx₁ (t.i₁ p) = (f₁ q).index p ∧ idx₂ (t.i₂ p) = (f₂ q).index p) := by
    haveI : IsFiniteMeasure (codePieces μ code q) := by
      dsimp only [codePieces]
      infer_instance
    rcases exists_pruned_comparison_table (codePieces μ code q) (M q) K signal hs
      (f₁ q) (f₂ q) ha hB hF (hT q) hL (palette q) (hp q) (hpt q)
      (hresolve q) (hvolume q) (hnative q) with hzero | hpos
    · exact ⟨0, bot_le, by simpa only [Measure.coe_zero, Pi.zero_apply, zero_add] using hzero, Or.inl rfl⟩
    · obtain ⟨τ, t, hle, -, hmass, hlaw, href, hquarter, hdecode⟩ := hpos
      exact ⟨τ, hle, hmass, Or.inr ⟨t, hlaw, href, hquarter, hdecode⟩⟩
  choose law hle hbudget hcases using hlocal
  let active : Finset Q := Finset.univ.filter (fun q => law q ≠ 0)
  have hinactive (q : Q) (hq : q ∉ active) : law q = 0 := by
    by_contra h
    exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hactive (q : active) : law q.val ≠ 0 := (Finset.mem_filter.mp q.property).2
  have ht (q : active) := (hcases q.val).resolve_left (hactive q)
  choose table hlaw href hquarter hdecode using ht
  have hnonneg (q : Q) : 0 ≤ reference q := by
    have hTq := (hT q).le
    dsimp [reference]
    positivity
  have hrefsum : (∑ q, (table q).referenceTotal) ≤ ∑ q, reference q := by
    calc
      _ ≤ ∑ q : active, reference q.val := Finset.sum_le_sum fun q _ => href q
      _ = ∑ q ∈ active, reference q := Finset.sum_coe_sort active reference
      _ ≤ ∑ q, reference q := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun q _ _ => hnonneg q)
  refine ⟨law, active, table, hle, ?_, hinactive, hlaw, hrefsum, ?_⟩
  · intro q
    simpa only [loss, add_assoc] using hbudget q
  · intro q
    exact ⟨hquarter q, hdecode q⟩

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
