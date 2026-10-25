-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Split.ConstructFromCore; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Split.ComparedBridges

namespace Submission.Obl.k4_general_compared_layers_velocity_lists.Split

open MeasureTheory Filter
noncomputable section

/-- A prover of the first child can work entirely with the named parent and
compared-sample interface, then use this exact frozen-statement return. -/
theorem rawComparison_of_core (h : ComparedLayerCore) : RawComparisonStatement := by
  intro α _ N K d κ ℓ S U e₀ ν μ ρ π b P T n j A B c F
  let p : Parent α := {
    N := N, K := K, d := d, κ := κ, ℓ := ℓ, S := S, U := U, e₀ := e₀,
    ν := ν, μ := μ, ρ := ρ, π := π, b := b, P := P, T := T, n := n,
    j := j, A := A, B := B, c := c, F := F }
  change Matching → Unpacked.Validity p → p.WideLayers →
    ∀ Ucap : ℝ, 0 < Ucap → ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ r u v m : ℝ,
      p.ComparedExponents r u v m ∧ m ≤ Ucap ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∃ H : ℝ,
        2 ≤ H ∧ p.K (τ k) ≤ H ∧ H ≤ p.N (τ k) ^ ε ∧
          Unpacked.Samples p (τ k) r u v m H
  intro hmatch hp hwide Ucap hUcap
  obtain ⟨τ, hτ, r, u, v, m, hexp, hm, samples⟩ :=
    h hmatch α p (Unpacked.valid_of_validity p hp) hwide Ucap hUcap
  refine ⟨τ, hτ, r, u, v, m, hexp, hm, ?_⟩
  intro ε hε
  filter_upwards [samples ε hε] with k hk
  obtain ⟨H, hH, hKH, hHN, ⟨f⟩⟩ := hk
  exact ⟨H, hH, hKH, hHN,
    Unpacked.samples_of_sample p (Parent.ComparedSample.fromReindex p f)⟩

/-- The second child's prover may use o273 as a named explicit hypothesis;
this packs the quantitative native list core into its exact Mathlib-only type. -/
theorem rawLists_of_core (h : CommonFieldPrinciple → ComparedListCore) :
    RawListsStatement := by
  intro hfield α _ N K d κ ℓ S U e₀ ν μ ρ π b P T n j A B c F
  let p : Parent α := {
    N := N, K := K, d := d, κ := κ, ℓ := ℓ, S := S, U := U, e₀ := e₀,
    ν := ν, μ := μ, ρ := ρ, π := π, b := b, P := P, T := T, n := n,
    j := j, A := A, B := B, c := c, F := F }
  change Unpacked.Validity p →
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ r u v m : ℝ, p.ComparedExponents r u v m → Λ * m ≤ p.U →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop,
        ∀ H : ℝ, 2 ≤ H → p.K k ≤ H → H ≤ p.N k ^ δ →
          Unpacked.Samples p k r u v m H → Unpacked.Frames p k r v m ε
  intro hp
  obtain ⟨Λ, hΛ, prepare⟩ := h hfield α p (Unpacked.valid_of_validity p hp)
  refine ⟨Λ, hΛ, ?_⟩
  intro r u v m hexp hroom ε hε
  obtain ⟨δ, hδ, hprepare⟩ := prepare r u v m hexp hroom ε hε
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hprepare] with k hk
  intro H hH hKH hHN sample
  obtain ⟨frame⟩ := hk H hH hKH hHN (Unpacked.sample_of_samples p sample)
  exact Unpacked.frames_of_frame p frame

end
end Submission.Obl.k4_general_compared_layers_velocity_lists.Split
