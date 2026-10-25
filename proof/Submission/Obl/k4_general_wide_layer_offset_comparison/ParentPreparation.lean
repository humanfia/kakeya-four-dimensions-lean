import Submission.Obl.k4_general_wide_layer_offset_comparison.ComparedInterface
import Submission.Obl.k4_general_wide_layer_offset_comparison.Coefficients

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Filter Set
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α]

/-- The accepted projected-parent parameter record with the same original fields. -/
def parameters (p : Parent α) : Parameters :=
  ⟨p.N, p.K, p.d, p.κ, p.ℓ, p.S, p.U, p.e₀⟩

/-- The accepted projected-parent data record with the same original fields. -/
def model (p : Parent α) : PreparedModel α :=
  ⟨p.ν, p.μ, p.ρ, p.π, p.b, p.P, p.T, p.n, p.j, p.A, p.B, p.c, p.F⟩

theorem Valid.parameters {p : Parent α} (hp : p.Valid) : p.parameters.Valid :=
  ⟨hp.scale, hp.scale_limit, hp.subpower, hp.dimension_nonneg, hp.dimension_lt_one,
    hp.rate_pos, hp.rate_le_one, hp.transverse_pos, hp.palette_pos,
    hp.palette_le_one, hp.depth_pos, hp.defect_pos⟩

end Parent

namespace ProjectedLayer

/-- Copy the original projected label fields into the compared-layer interface. -/
def ofOriginal {α : Type} (L : ProjLayer α) : ProjectedLayer α :=
  ⟨L.β, L.n, L.C, L.tag, L.u, L.v, L.G⟩

theorem ofOriginal_valid {α : Type} [MeasurableSpace α] {p : Parent α}
    {k : ℕ} {s m H : ℝ} {L : ProjLayer α}
    (hL : LayerValid p.parameters p.model k s m H L) :
    (ofOriginal L).Valid p k s m H := by
  rcases hL with ⟨⟨hβ, hlo, hhi, hmeas, hdisj, hi⟩, hbudget⟩
  refine ⟨hβ, ?_, hhi, hmeas, hdisj, hi, hbudget⟩
  simpa [Parent.parameters, ofOriginal] using hlo

end ProjectedLayer

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The exact initial data for the comparison engine: three actual projected
layers with one intrinsic subpower loss, common original residual and uniform
coefficient bounds, chosen after the exponent cap and before every final loss. -/
theorem prepared_three_layers (hp : p.Valid) (hwide : p.WideLayers)
    {Ucap : ℝ} (hcap : 0 < Ucap) :
    ∃ (τ : ℕ → ℕ), StrictMono τ ∧ ∃ r u v m : ℝ,
      p.ComparedExponents r u v m ∧ m ≤ Ucap ∧
      ∃ (H : ℕ → ℝ) (σ : ℕ → Measure (α × ℝ)) (L : ℕ → Fin 3 → ProjectedLayer α),
        (∀ k, 2 ≤ H k ∧ p.K (τ k) ≤ H k) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N (τ k) ^ ε) ∧
        (∀ k, σ k ≤ p.ρ (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ σ k univ) ∧
        (∀ k a, (L k a).Valid p (τ k) (depth r u v a) m (H k)) ∧
        (∀ k a, (L k a).Covers (σ k)) ∧
        (∀ᶠ k in atTop, ∀ a i e, |((L k a).G i).coeff e| ≤ p.N (τ k) ^ (m / 1000)) := by
  have hw : RawLayer p.N p.K p.d p.ℓ p.U p.ρ p.π p.b p.P p.model.x true := by
    simpa [Parent.WideLayers, RawLayer, Parent.model, PreparedModel.x,
      Submission.Lib.K4ContactNormalization.point,
      Submission.Obl.k4_critical_intercept_concentration.Data.x] using hwide
  obtain ⟨τ, hτ, r, u, v, m, hexp, hcap, H, σ, L, hH, hsub, hσ, hL, hcover⟩ :=
    exists_three_layers p.parameters p.model hp.parameters hw hcap
  have hc := eventually_layer_coefficients p.parameters p.model hp.parameters hτ
    (fun k => by linarith [(hH k).1]) hsub hexp L hL
  refine ⟨τ, hτ, r, u, v, m, hexp, hcap, H, σ, fun k a => ProjectedLayer.ofOriginal (L k a),
    hH, hsub, hσ, ?_, hcover, hc⟩
  intro k a
  exact ProjectedLayer.ofOriginal_valid (hL k a)

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
