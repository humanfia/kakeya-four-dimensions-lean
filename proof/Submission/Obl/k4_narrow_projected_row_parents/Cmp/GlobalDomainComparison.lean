/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/GlobalDomainComparison.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ComparisonTables
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.DomainLawAssembly

/-! One global retained law from prepared tables on the actual code partition. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section

/-- Inactive domains carry zero prepared mass. Active comparison tables are
charged to their original reference sum, and all deletions give one submeasure. -/
theorem global_domain_comparison {Ω Q : Type*} [MeasurableSpace Ω]
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (code : Ω → Q) (hcode : Measurable code)
    (law : Q → Measure Ω) (hle : ∀ q, law q ≤ codePieces μ code q)
    (loss : Q → ℝ≥0∞)
    (hbudget : ∀ q, codePieces μ code q univ ≤ law q univ + loss q)
    (active : Finset Q) (hinactive : ∀ q, q ∉ active → law q = 0)
    {D : ℕ} {d a L CT ε C Λ B : ℝ}
    (H : ComparisonEstimate D d ε C) (hC : 0 ≤ C)
    (ha : 0 < a) (hL : 1 ≤ L) (hCT : 0 < CT)
    (hΛ : C * L ^ (1 / ε) ≤ Λ)
    (table : (q : active) → ComparisonTable Ω D d a L CT)
    (hlaw : ∀ q, (table q).law = law q.val)
    (href : (∑ q, (table q).referenceTotal) ≤ B) :
    ∃ (ν ρ : Measure Ω) (G : Set Ω),
      ν ≤ μ ∧ ρ = ν.restrict G ∧ ρ ≤ μ ∧ MeasurableSet G ∧
      μ univ ≤ ρ univ + (∑ q, loss q) + ENNReal.ofReal (C * CT * Λ ^ (-ε) * B) ∧
      (∀ q, ν.restrict {p | code p = q} = law q) ∧
      (∀ᵐ p ∂ν, code p ∈ active) ∧
      ∀ (q : active) p, p ∈ G → code p = q.val →
        ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
          ‖(table q).f₁ ((table q).i₁ p) (emb x) -
            (table q).f₂ ((table q).i₂ p) (emb x)‖ ≤ Λ * a := by
  let ν : Measure Ω := ∑ q, law q
  obtain ⟨hν, hrestrict⟩ := assemble_domain_submeasures μ code hcode law hle
  have hmass := assembled_domain_mass_budget μ code hcode law loss hbudget
  have htable (q : active) : (table q).law = ν.restrict {p | code p = q.val} :=
    (hlaw q).trans (hrestrict q.val).symm
  obtain ⟨G, hG, hbad, hagree⟩ := exists_comparison_restriction H hC ha hL hCT hΛ ν
    (fun q : active => {p | code p = q.val})
    (fun q => hcode (measurableSet_singleton q.val)) table htable
  have hΛ0 : 0 ≤ Λ :=
    (mul_nonneg hC (Real.rpow_nonneg ((zero_le_one : (0 : ℝ) ≤ 1).trans hL) _)).trans hΛ
  have hfactor : 0 ≤ C * CT * Λ ^ (-ε) :=
    mul_nonneg (mul_nonneg hC hCT.le) (Real.rpow_nonneg hΛ0 _)
  have hbad' : ν Gᶜ ≤ ENNReal.ofReal (C * CT * Λ ^ (-ε) * B) :=
    hbad.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left href hfactor))
  have hsplit : ν univ = (ν.restrict G) univ + ν Gᶜ := by
    rw [Measure.restrict_apply_univ, measure_add_measure_compl hG]
  have hactive : ∀ᵐ p ∂ν, code p ∈ active := by
    change ∀ᵐ p ∂(∑ q, law q), code p ∈ active
    rw [ae_finsetSum_measure_iff]
    intro q hq
    by_cases hqa : q ∈ active
    · have hmem : ∀ᵐ p ∂law q, code p = q :=
        (ae_restrict_mem (hcode (measurableSet_singleton q))).filter_mono (ae_mono (hle q))
      exact hmem.mono fun p hp => hp ▸ hqa
    · rw [hinactive q hqa]
      simp
  refine ⟨ν, ν.restrict G, G, hν, rfl, (Measure.restrict_le_self).trans hν, hG, ?_,
    hrestrict, hactive, ?_⟩
  · calc
      μ univ ≤ ν univ + ∑ q, loss q := hmass
      _ = (ν.restrict G) univ + (∑ q, loss q) + ν Gᶜ := by rw [hsplit]; ac_rfl
      _ ≤ _ := add_le_add le_rfl hbad'
  · intro q p hp hq
    exact hagree q p hp hq

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
