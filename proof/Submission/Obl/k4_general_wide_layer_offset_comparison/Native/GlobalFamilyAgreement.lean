-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/GlobalFamilyAgreement.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ComparisonTables

/-! Preserve uniform sheet agreement when decoding to original family indices. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open scoped Classical

noncomputable section

theorem global_original_family_agreement {Ω Q : Type*} [MeasurableSpace Ω]
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (ν : Measure Ω) (code : Ω → Q) (hcode : Measurable code)
    (active : Finset Q) (hactive : ∀ᵐ p ∂ν, code p ∈ active)
    (G : Set Ω) (hG : MeasurableSet G)
    {D : ℕ} {d a L CT Λ : ℝ}
    (table : (q : active) → ComparisonTable Ω D d a L CT)
    (hlaw : ∀ q, (table q).law = ν.restrict {p | code p = q.val})
    (hagreement : ∀ (q : active) p, p ∈ G → code p = q.val →
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
        ‖(table q).f₁ ((table q).i₁ p) (emb x) -
          (table q).f₂ ((table q).i₂ p) (emb x)‖ ≤ Λ * a)
    (n₁ n₂ : Q → ℕ)
    (f₁ : ∀ q, Fin (n₁ q) → EuclideanSpace ℂ (Fin 3) → ℂ)
    (f₂ : ∀ q, Fin (n₂ q) → EuclideanSpace ℂ (Fin 3) → ℂ)
    (idx₁ : (q : active) → Fin (table q).n₁ → Fin (n₁ q.val))
    (idx₂ : (q : active) → Fin (table q).n₂ → Fin (n₂ q.val))
    (hsame₁ : ∀ q i, (table q).f₁ i = f₁ q.val (idx₁ q i))
    (hsame₂ : ∀ q j, (table q).f₂ j = f₂ q.val (idx₂ q j))
    (old₁ : ∀ q, Ω → Fin (n₁ q)) (old₂ : ∀ q, Ω → Fin (n₂ q))
    (hdecode : ∀ q, ∀ᵐ p ∂(table q).law,
      idx₁ q ((table q).i₁ p) = old₁ q.val p ∧ idx₂ q ((table q).i₂ p) = old₂ q.val p) :
    ∀ᵐ p ∂ν.restrict G, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
      ‖f₁ (code p) (old₁ (code p) p) (emb x) - f₂ (code p) (old₂ (code p) p) (emb x)‖ ≤ Λ * a := by
  have hcurrent (q : active) : ∀ᵐ p ∂ν, code p = q.val →
      idx₁ q ((table q).i₁ p) = old₁ q.val p ∧ idx₂ q ((table q).i₂ p) = old₂ q.val p := by
    have hqmeas : MeasurableSet {p | code p = q.val} := hcode (measurableSet_singleton q.val)
    apply (ae_restrict_iff' hqmeas).mp
    rw [← hlaw q]
    exact hdecode q
  have hall : ∀ᵐ p ∂ν, ∀ q : active, code p = q.val →
      idx₁ q ((table q).i₁ p) = old₁ q.val p ∧ idx₂ q ((table q).i₂ p) = old₂ q.val p :=
    ae_all_iff.mpr hcurrent
  filter_upwards [ae_restrict_mem hG, ae_restrict_of_ae hactive, ae_restrict_of_ae hall]
    with p hp hpa hpd
  let q : active := ⟨code p, hpa⟩
  obtain ⟨hd₁, hd₂⟩ := hpd q rfl
  intro x hx
  have h := hagreement q p hp rfl x hx
  rw [hsame₁, hsame₂, hd₁, hd₂] at h
  exact h

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
