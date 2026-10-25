-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.ListCore; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Consensus
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Common.Apply
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Frame.Build
import Submission.Obl.k4_general_compared_layers_velocity_lists.ComparedInterface

/-!
# The native list core

`comparedListCore_of_field`: under the frozen statement of o273
(`CommonFieldPrinciple`), compared samples yield residual velocity list frames
(`ComparedListCore`). The three stages of paper Prop. 8.4 after the long comparison:

* coefficient consensus at native fine states (`Field/Agree`,
  `Parent.Valid.consensus_of_sample_mesh`);
* the common affine transverse field (`Field/Common`,
  `Parent.Valid.fieldReady_of_consensus`);
* the residual velocity lists (`Field/Frame`, `Parent.Valid.listFrame_of_fieldReady`).
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter

noncomputable section

/-- **The native list core**, conditional on the common affine field principle (o273). -/
theorem comparedListCore_of_field (hfield : CommonFieldPrinciple) : ComparedListCore := by
  intro α _ p h
  obtain ⟨Λn, hΛn, hcons⟩ := h.consensus_of_sample_mesh
  obtain ⟨C₀, Λ₃, hC₀, hΛ₃, hfr⟩ := h.fieldReady_of_consensus hfield
  have hCΛ : 0 < C₀ * (Λ₃ + 1) := mul_pos (by linarith) (by linarith)
  refine ⟨Λn * (1 + C₀ * (Λ₃ + 1)), mul_pos hΛn (by linarith), ?_⟩
  intro r u v m hexp hroom ε hε
  obtain ⟨δ₄, ε₁, hδ₄, hε₁, hframe⟩ := h.listFrame_of_fieldReady hexp ε hε
  obtain ⟨δ₃, η, hδ₃, hη, hfield'⟩ := hfr hexp ε₁ hε₁
  have hx := hexp
  obtain ⟨⟨hr, hv, hvr, hrvm, hℓrm, hrU⟩, hu, hur, hvd, hm10000, hκu⟩ := hx
  have hd1 := h.dimension_lt_one
  have hℓ := h.transverse_pos
  have hℓr := mul_pos hℓ hr
  have hm : 0 < m := by nlinarith
  have h1d : 0 < 1 - p.d := by linarith
  have hθ0 : 0 ≤ (1 - p.d) * u / 2 := by positivity
  have hθu : (1 - p.d) * u / 2 ≤ u := by nlinarith [h.dimension_nonneg]
  have h3r : r + r + u ≤ m := by nlinarith
  set βb := C₀ * (Λ₃ * m + (r + (1 - p.d) * u / 2)) with hβb_def
  have hΛm : m ≤ Λ₃ * m := by nlinarith
  have hβb : m + r ≤ βb := by
    have h1 : m + r ≤ Λ₃ * m + (r + (1 - p.d) * u / 2) := by linarith
    have h2 : 0 ≤ Λ₃ * m + (r + (1 - p.d) * u / 2) := by linarith
    have h3 : 0 ≤ (C₀ - 1) * (Λ₃ * m + (r + (1 - p.d) * u / 2)) :=
      mul_nonneg (by linarith) h2
    rw [hβb_def]
    nlinarith
  have hβle : βb ≤ C₀ * (Λ₃ + 1) * m := by
    have h1 : Λ₃ * m + (r + (1 - p.d) * u / 2) ≤ (Λ₃ + 1) * m := by nlinarith
    calc βb ≤ C₀ * ((Λ₃ + 1) * m) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = C₀ * (Λ₃ + 1) * m := by ring
  have hroom' : Λn * (r + βb + (r + u)) ≤ p.U := by
    have h1 : r + βb + (r + u) ≤ (1 + C₀ * (Λ₃ + 1)) * m := by
      calc r + βb + (r + u) ≤ m + C₀ * (Λ₃ + 1) * m := by linarith
        _ = (1 + C₀ * (Λ₃ + 1)) * m := by ring
    calc Λn * (r + βb + (r + u)) ≤ Λn * ((1 + C₀ * (Λ₃ + 1)) * m) :=
          mul_le_mul_of_nonneg_left h1 hΛn.le
      _ = Λn * (1 + C₀ * (Λ₃ + 1)) * m := by ring
      _ ≤ p.U := hroom
  obtain ⟨δ₂, hδ₂, hc⟩ := hcons hexp hβb hroom' η hη
  refine ⟨min δ₂ (min δ₃ δ₄), lt_min hδ₂ (lt_min hδ₃ hδ₄), ?_⟩
  filter_upwards [hc, hfield', hframe, h.scale_limit.eventually (eventually_ge_atTop (1 : ℝ))]
    with k hck hfk hlk hN
  rintro H hH hKH hHN ⟨s⟩
  have hle : ∀ δ' : ℝ, min δ₂ (min δ₃ δ₄) ≤ δ' → H ≤ p.N k ^ δ' := fun δ' hδ' =>
    hHN.trans (Real.rpow_le_rpow_of_exponent_le hN hδ')
  obtain ⟨c⟩ := hck H hH hKH (hle δ₂ (min_le_left _ _)) s
  obtain ⟨F⟩ := hfk H hH hKH (hle δ₃ ((min_le_right _ _).trans (min_le_left _ _))) s c
  exact hlk H hH hKH (hle δ₄ ((min_le_right _ _).trans (min_le_right _ _))) s F

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
