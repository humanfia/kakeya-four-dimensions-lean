/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarOriginalFirstJet.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarOriginalFirstJet.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDesignatedFirstJet
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarOriginalNormalData

/-! The first-jet certificate starts from the original measurable scalar data. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem original_scalar_first_jet {d : ℝ} (hd0 : 0 ≤ d) (hd : d < 1)
    (r : ℕ) (γ : Fin r → ℝ) (γ₀ : ℝ) (hγ : ∀ i, 0 < γ i) (hγ₀ : ∀ i, γ i ≤ γ₀) :
    ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
        ∀ (Λ : Type*) [MeasurableSpace Λ], ∀ (D : ScalarMotion Λ) (ν : Measure Λ)
          (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (S : ℝ → Set ℝ)
          (K ζ : ℝ) (Tl : Fin r → ℕ) (T₀ : ℕ),
          K ≤ N ^ α → ScalarOriginalNormalData D ν E F S K ζ d → ζ ≤ N ^ (-cζ) →
          (∀ i, N ^ (-γ i) / K ≤ ((2 : ℝ) ^ Tl i)⁻¹) →
          (∀ i, ((2 : ℝ) ^ Tl i)⁻¹ ≤ K * N ^ (-γ i)) →
          N ^ (-γ₀) / K ≤ ((2 : ℝ) ^ T₀)⁻¹ → ((2 : ℝ) ^ T₀)⁻¹ ≤ K * N ^ (-γ₀) →
          ScalarFirstJetOutput D ν E F (Fin.cases T₀ Tl) 0 d (N ^ ε) := by
  obtain ⟨cζ, hcζ, hdesignated⟩ :=
    finite_original_first_jet_at_designated_exponents hd0 hd r γ γ₀ hγ hγ₀
  refine ⟨cζ, hcζ, ?_⟩
  intro ε hε
  obtain ⟨α, hα, N₀, hN₀, hfinite⟩ := hdesignated ε hε
  refine ⟨α, hα, N₀, hN₀, ?_⟩
  intro N hN Λ _ D ν E F S K ζ Tl T₀ hKN hdata hζN hlow hhigh hlow₀ hhigh₀
  let : IsProbabilityMeasure ν := hdata.probability
  have hlength (T : ℕ) : scalarDyadicLength T = ((2 : ℝ) ^ T)⁻¹ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, one_div] using! scalarDyadicLength_eq T
  exact hfinite N hN Λ D ν E F S K ζ Tl T₀ hdata.one_le hKN hdata.row_bounded
    (hdata.clipped_hyp hd0) hdata.floor_pos hdata.dense_real hζN
    (fun i => by simpa only [hlength] using! hlow i)
    (fun i => by simpa only [hlength] using! hhigh i)
    (by simpa only [hlength] using! hlow₀)
    (by simpa only [hlength] using! hhigh₀)

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
