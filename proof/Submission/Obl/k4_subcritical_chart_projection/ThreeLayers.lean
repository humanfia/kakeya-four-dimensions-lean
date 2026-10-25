import Submission.Obl.k4_subcritical_chart_projection.FrozenAdapter
import Submission.Obl.k4_horizontal_supercritical_three_projections.Layers

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Submission.Obl.k4_subcritical_chart_projection

open Set MeasureTheory Filter
open Submission.Obl.k4_horizontal_supercritical_three_projections

/-- A projection selection on every dense submeasure of one corrected
chart system. Every output floor still refers to the original residual. -/
def ChartProjectionStep {α : Type} [MeasurableSpace α] (m : Model α)
    (M s₀ R : ℝ) (depth : Fin 3 → ℝ) (h : Fin 3) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧
    ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ᶠ k in atTop,
      ∀ C : Charts (m.b k) (m.ρ k) (m.π k)
        (m.N k ^ (-M)) (m.N k ^ (-(2 * m.κ * s₀))) (m.N k ^ (-s₀))
        (m.N k ^ (-(20 * s₀))) m.d (m.N k ^ ξ) (m.N k ^ (-ξ))
        (fun h => m.N k ^ (-(depth h - s₀))),
      ∀ ζ : Measure (α × ℝ), ζ ≤ C.law → ENNReal.ofReal (m.N k ^ (-η)) ≤ ζ univ →
        ∃ (L : ProjectionLayer α) (ζ' : Measure (α × ℝ)),
          ζ' ≤ ζ ∧ ENNReal.ofReal (m.N k ^ (-ε)) ≤ ζ' univ ∧
          (∀ᵐ p ∂ζ', p ∈ L.covered) ∧
          L.Good (m.N k) m.d (depth h) ε R
            (m.N k ^ (-M)) (m.N k ^ (-2 * m.κ * s₀)) (m.b k) (m.π k) (m.ρ k)

/-- Repackage the three existing physical-layer certificates into the
frozen simultaneous output, without changing their floors or reference sums. -/
theorem projectedAt_of_layers {α : Type} [MeasurableSpace α] (m : Model α)
    {k : ℕ} {M s₀ R ε : ℝ} {depth : Fin 3 → ℝ}
    (ζ : Measure (α × ℝ)) (L : Fin 3 → ProjectionLayer α)
    (hζ : ζ ≤ m.ρ k) (hmass : ENNReal.ofReal (m.N k ^ (-ε)) ≤ ζ univ)
    (hcover : ∀ᵐ p ∂ζ, ∀ h, p ∈ (L h).covered)
    (hgood : ∀ h, (L h).Good (m.N k) m.d (depth h) ε R
      (m.N k ^ (-M)) (m.N k ^ (-2 * m.κ * s₀)) (m.b k) (m.π k) (m.ρ k)) :
    ProjectedAt m k M s₀ R ε depth := by
  refine ⟨ζ, (fun h => (L h).n), (fun h => (L h).C), (fun h => (L h).q),
    (fun h => (L h).G), hζ, hmass, hcover, ?_, ?_, ?_, ?_⟩
  · exact fun h => (hgood h).1
  · exact fun h => (hgood h).2.1
  · exact fun h => (hgood h).2.2.1
  · exact fun h => (hgood h).2.2.2

/-- Select the three laws in succession, spending the positive losses
backwards and using one common chart system. Earlier coverage persists under
every later restriction; original whole-domain floors are untouched. -/
theorem projected_of_chart_steps {α : Type} [MeasurableSpace α] (m : Model α)
    (hN : ∀ k, 1 ≤ m.N k) {M s₀ R : ℝ} {depth : Fin 3 → ℝ}
    (hready : ChartsReady m M s₀ depth)
    (hstep : ∀ h, ChartProjectionStep m M s₀ R depth h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ProjectedAt m k M s₀ R ε depth := by
  intro ε hε
  obtain ⟨η₂, hη₂, ξ₂, hξ₂, H₂⟩ := hstep 2 ε hε
  let ε₁ := min ε η₂
  have hε₁ : 0 < ε₁ := lt_min hε hη₂
  obtain ⟨η₁, hη₁, ξ₁, hξ₁, H₁⟩ := hstep 1 ε₁ hε₁
  let ε₀ := min ε η₁
  have hε₀ : 0 < ε₀ := lt_min hε hη₁
  obtain ⟨η₀, hη₀, ξ₀, hξ₀, H₀⟩ := hstep 0 ε₀ hε₀
  let ξ := min η₀ (min ξ₀ (min ξ₁ ξ₂))
  have hξ : 0 < ξ := lt_min hη₀ (lt_min hξ₀ (lt_min hξ₁ hξ₂))
  have hξη : ξ ≤ η₀ := min_le_left _ _
  have hξ₀' : ξ ≤ ξ₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hξ₁' : ξ ≤ ξ₁ := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hξ₂' : ξ ≤ ξ₂ := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  filter_upwards [H₀ ξ hξ hξ₀', H₁ ξ hξ hξ₁', H₂ ξ hξ hξ₂', hready ξ hξ]
    with k H₀ H₁ H₂ hC
  obtain ⟨C⟩ := hC
  have hm : ENNReal.ofReal (m.N k ^ (-η₀)) ≤ C.law univ :=
    (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg hξη))).trans C.mass_le
  obtain ⟨L₀, ζ₀, hζ₀, hm₀, hc₀, hg₀⟩ := H₀ C C.law le_rfl hm
  have hm₁ : ENNReal.ofReal (m.N k ^ (-η₁)) ≤ ζ₀ univ := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hm₀
    exact Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg (min_le_right _ _))
  obtain ⟨L₁, ζ₁, hζ₁, hm₁', hc₁, hg₁⟩ := H₁ C ζ₀ hζ₀ hm₁
  have hm₂ : ENNReal.ofReal (m.N k ^ (-η₂)) ≤ ζ₁ univ := by
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hm₁'
    exact Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg (min_le_right _ _))
  obtain ⟨L₂, ζ₂, hζ₂, hm₂', hc₂, hg₂⟩ := H₂ C ζ₁ (hζ₁.trans hζ₀) hm₂
  apply projectedAt_of_layers m ζ₂ ![L₀, L₁, L₂]
    ((hζ₂.trans (hζ₁.trans hζ₀)).trans C.le) hm₂'
  · have hc₀' := ae_mono (hζ₂.trans hζ₁) hc₀
    have hc₁' := ae_mono hζ₂ hc₁
    filter_upwards [hc₀', hc₁', hc₂] with p hp₀ hp₁ hp₂ h
    fin_cases h <;> simpa using (by assumption : p ∈ _)
  · intro h
    have hχ : 0 ≤ m.N k ^ (-M) := Real.rpow_nonneg (le_trans zero_le_one (hN k)) _
    have hD : 0 ≤ m.N k ^ (-2 * m.κ * s₀) := Real.rpow_nonneg (le_trans zero_le_one (hN k)) _
    fin_cases h
    · exact hg₀.mono (hN k) (min_le_left _ _) le_rfl hχ hD
    · exact hg₁.mono (hN k) (min_le_left _ _) le_rfl hχ hD
    · exact hg₂

end Submission.Obl.k4_subcritical_chart_projection
