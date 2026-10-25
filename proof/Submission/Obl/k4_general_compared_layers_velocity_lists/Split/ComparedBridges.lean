-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Split.ComparedBridges; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Split.Raw
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.CommonField
import Submission.Obl.k4_general_compared_layers_velocity_lists.Split.ComparedUnpacked

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Split

open MeasureTheory Filter
noncomputable section

theorem comparedLayerCore_of_raw (h : RawComparisonStatement) : ComparedLayerCore := by
  intro hmatch α _ p hp hwide Ucap hUcap
  have h' := h α p.N p.K p.d p.κ p.ℓ p.S p.U p.e₀
    p.ν p.μ p.ρ p.π p.b p.P p.T p.n p.j p.A p.B p.c p.F
  change Matching → Unpacked.Validity p → p.WideLayers →
    ∀ Ucap : ℝ, 0 < Ucap → ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ r u v m : ℝ,
      p.ComparedExponents r u v m ∧ m ≤ Ucap ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∃ H : ℝ,
        2 ≤ H ∧ p.K (τ k) ≤ H ∧ H ≤ p.N (τ k) ^ ε ∧
          Unpacked.Samples p (τ k) r u v m H at h'
  obtain ⟨τ, hτ, r, u, v, m, hexp, hm, samples⟩ :=
    h' hmatch (Unpacked.validity_of_valid p hp) hwide Ucap hUcap
  refine ⟨τ, hτ, r, u, v, m, hexp, hm, ?_⟩
  intro ε hε
  filter_upwards [samples ε hε] with k hk
  obtain ⟨H, hH, hKH, hHN, hs⟩ := hk
  exact ⟨H, hH, hKH, hHN, Unpacked.sample_of_samples (p.reindex τ) hs⟩

theorem comparedListCore_of_raw (hfield : CommonFieldPrinciple)
    (h : RawListsStatement) : ComparedListCore := by
  intro α _ p hp
  have h' := h hfield α p.N p.K p.d p.κ p.ℓ p.S p.U p.e₀
    p.ν p.μ p.ρ p.π p.b p.P p.T p.n p.j p.A p.B p.c p.F
  change Unpacked.Validity p →
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ r u v m : ℝ, p.ComparedExponents r u v m → Λ * m ≤ p.U →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop,
        ∀ H : ℝ, 2 ≤ H → p.K k ≤ H → H ≤ p.N k ^ δ →
          Unpacked.Samples p k r u v m H → Unpacked.Frames p k r v m ε at h'
  obtain ⟨Λ, hΛ, prepare⟩ := h' (Unpacked.validity_of_valid p hp)
  refine ⟨Λ, hΛ, ?_⟩
  intro r u v m hexp hbudget ε hε
  obtain ⟨δ, hδ, hprepare⟩ := prepare r u v m hexp hbudget ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hprepare] with k hk
  intro H hH hKH hHN
  rintro ⟨f⟩
  exact Unpacked.frame_of_frames p (hk H hH hKH hHN (Unpacked.samples_of_sample p f))

end
end Submission.Obl.k4_general_compared_layers_velocity_lists.Split
