import Submission.Obl.k4_general_wide_layer_offset_comparison.ParentPreparation
import Submission.Obl.k4_general_wide_layer_offset_comparison.SampleAssembly

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter

noncomputable section

/-- The remaining analytic engine starts with three literal wide layers. Its
output already certifies geometry at the final intrinsic height; simultaneous
floor renewal may only restrict the source and discard entries. -/
def TablePreparation : Prop :=
  Matching → ∀ (α : Type) [MeasurableSpace α] (p : Parent α), p.Valid →
    ∀ r u v m : ℝ, p.ComparedExponents r u v m →
    ∀ (H₀ : ℕ → ℝ) (σ : ℕ → Measure (α × ℝ))
      (L : ℕ → Fin 3 → ProjectedLayer α),
    (∀ k, 2 ≤ H₀ k ∧ p.K k ≤ H₀ k) →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H₀ k ≤ p.N k ^ ε) →
    (∀ k, σ k ≤ p.ρ k ∧ ENNReal.ofReal ((H₀ k)⁻¹) ≤ σ k univ) →
    (∀ k a, (L k a).Valid p k (depth r u v a) m (H₀ k)) →
    (∀ k a, (L k a).Covers (σ k)) →
    (∀ᶠ k in atTop, ∀ a i e, |((L k a).G i).coeff e| ≤ p.N k ^ (m / 1000)) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∃ H h R : ℝ, p.K k ≤ H ∧ H ≤ p.N k ^ ε ∧ 1 ≤ h ∧ 1 ≤ R ∧
        4 * h * R ≤ H ∧ ∃ t : p.ComparisonTable k r u v m H R,
          ENNReal.ofReal h⁻¹ ≤ t.law univ

/-- Fixed exponent choice, one subsequence, coefficient calibration and final
floor renewal reduce the exact comparison conclusion to `TablePreparation`. -/
theorem comparedLayerCore_of_tables (hprepare : TablePreparation) : ComparedLayerCore := by
  intro hmatching α _ p hp hwide Ucap hcap
  obtain ⟨τ, hτ, r, u, v, m, hexp, hmcap, H₀, σ, L, hH₀, hHsub,
      hσ, hL, hcover, hcoeff⟩ := p.prepared_three_layers hp hwide hcap
  have hpτ : (p.reindex τ).Valid := Parent.Valid.reindex p hp hτ.tendsto_atTop
  have ht := hprepare hmatching α (p.reindex τ) hpτ r u v m hexp
    H₀ σ L hH₀ hHsub hσ hL hcover hcoeff
  refine ⟨τ, hτ, r, u, v, m, hexp, hmcap, ?_⟩
  intro ε hε
  filter_upwards [ht ε hε] with k hk
  obtain ⟨H, h, R, hKH, hHN, hh, hR, hH, t, hm⟩ := hk
  letI : IsFiniteMeasure t.law :=
    ⟨((t.le_rho.trans (hpτ.basic k).2.2.2.2.1) univ).trans_lt
      ((Parent.Basic.mass_le (p.reindex τ) hpτ.basic k).trans_lt ENNReal.ofReal_lt_top)⟩
  exact ⟨H, t.loss_one, hKH, hHN, t.renew hh hR hH hm⟩

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
