import Submission.Obl.k4_horizontal_supercritical_three_projections.Parameters
import Submission.Obl.k4_horizontal_supercritical_three_projections.Layers
import Submission.Obl.k4_horizontal_supercritical_three_projections.Model

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Filter

namespace HorizontalModel

variable {α : Type} [MeasurableSpace α] (m : HorizontalModel α)

/-- A single-step scalar preparation theorem at the three fixed depths. -/
def ProjectionPreparation : Prop :=
  ∀ buffer : ℝ, 100 < buffer →
    ∃ (p : ProjectionDepths m.d m.κ m.U m.e₀ buffer) (R : ℝ), 1 < R ∧
      ∀ M : ℝ, 100 * p.s₀ < M → ∀ h : Fin 3,
        SingleProjection m.N m.d (![p.s, p.s + p.u, p.s + p.v] h) R M
          (2 * m.κ * p.s₀) m.b m.π m.ρ

/-- The three stored layers have original floors and a separate common dense
residual covered by all layers. -/
def Projected : Prop :=
  ∀ buffer : ℝ, 100 < buffer →
    ∃ (p : ProjectionDepths m.d m.κ m.U m.e₀ buffer) (R : ℝ), 1 < R ∧
      ∀ M : ℝ, 100 * p.s₀ < M → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        ∃ (ζ : Measure (α × ℝ)) (L : Fin 3 → ProjectionLayer α),
          ζ ≤ m.ρ k ∧ ENNReal.ofReal (m.N k ^ (-ε)) ≤ ζ univ ∧
          (∀ᵐ z ∂ζ, ∀ h, z ∈ (L h).covered) ∧
          ∀ h, (L h).Good (m.N k) m.d (![p.s, p.s + p.u, p.s + p.v] h) ε R
            (m.N k ^ (-M)) (m.N k ^ (-2 * m.κ * p.s₀)) (m.b k) (m.π k) (m.ρ k)

/-- Uniform projection steps on dense submeasures suffice for the exact common
residual interface. No earlier floor is asserted for a later restricted law. -/
theorem projected_of_preparation (h : m.Valid) (hp : m.ProjectionPreparation) : m.Projected := by
  intro buffer hb
  obtain ⟨p, R, hR, H⟩ := hp buffer hb
  refine ⟨p, R, hR, ?_⟩
  intro M hM ε hε
  have hdense := fun η hη => Valid.residual_dense m h hη (η := η)
  have hsteps := H M hM
  have H' := three_layers_of_single m.N m.d R M (2 * m.κ * p.s₀)
    ![p.s, p.s + p.u, p.s + p.v] m.b m.π m.ρ
    (fun k => le_trans (by norm_num) (h.N_ge k)) hdense hsteps hε
  simpa only [neg_mul] using H'

end HorizontalModel
end Submission.Obl.k4_horizontal_supercritical_three_projections
