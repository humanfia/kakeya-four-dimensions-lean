/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WeightedResidual.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Residual
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TypicalOperations

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory Filter
open Submission.Obl.k4_native_calibrated_homogeneous_remainder

/-- The residual criterion in the precise original finite mixture weights. -/
theorem weighted_vanishing_failure_ratio_of_residual_discovery
    {α : Type*} [MeasurableSpace α] (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (μ : (k : ℕ) → Fin (W k) → Measure α)
    (B Q : (k : ℕ) → Fin (W k) → Set α)
    (hdisj : ∀ k g, Disjoint (B k g) (Q k g))
    (hdiscover : ∀ δ : ℝ, 0 < δ → ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
      (∀ k, δ ≤ (∑ g, ENNReal.ofReal (ω (φ k) g) * μ (φ k) g (B (φ k) g)).toReal /
        (∑ g, ENNReal.ofReal (ω (φ k) g) * μ (φ k) g univ).toReal) →
      ∃ k, 0 < ∑ g, ENNReal.ofReal (ω (φ k) g) *
        μ (φ k) g (B (φ k) g ∩ Q (φ k) g)) :
    Tendsto (fun k => (∑ g, ENNReal.ofReal (ω k g) * μ k g (B k g)).toReal /
      (∑ g, ENNReal.ofReal (ω k g) * μ k g univ).toReal) atTop (nhds 0) := by
  let σ : (k : ℕ) → Measure (Fin (W k) × α) :=
    fun k => worldLaw (fun g => ENNReal.ofReal (ω k g)) (μ k)
  let B' : (k : ℕ) → Set (Fin (W k) × α) := fun k => {z | z.2 ∈ B k z.1}
  let Q' : (k : ℕ) → Set (Fin (W k) × α) := fun k => {z | z.2 ∈ Q k z.1}
  have hd (k : ℕ) : Disjoint (B' k) (Q' k) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    exact Set.disjoint_left.mp (hdisj k z.1) hz hz'
  have h := vanishing_failure_ratio_of_residual_discovery σ B' Q' hd
    (by
      intro δ hδ φ hφ hbad
      have hb : ∀ k, δ ≤
          (∑ g, ENNReal.ofReal (ω (φ k) g) * μ (φ k) g (B (φ k) g)).toReal /
          (∑ g, ENNReal.ofReal (ω (φ k) g) * μ (φ k) g univ).toReal := by
        simpa [σ, worldLaw_univ, worldLaw_apply, B'] using hbad
      obtain ⟨k, hk⟩ := hdiscover δ hδ φ hφ hb
      refine ⟨k, ?_⟩
      simpa [σ, worldLaw_apply, B', Q'] using hk)
  simpa [σ, worldLaw_univ, worldLaw_apply, B'] using h

end Submission.Obl.k4_scalar_graph_residual_discovery
