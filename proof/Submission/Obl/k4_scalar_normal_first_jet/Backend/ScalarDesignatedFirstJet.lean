/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarDesignatedFirstJet.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarDesignatedFirstJet.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPositiveFirstJet
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFiniteCoarseFirstJet

/-! Original first jets for an arbitrary designated hierarchy and its separate fine reading. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter

/-- The fine level need not be deeper than every designated level.
The output even supplies its own Taylor bound as an extra designated row. -/
theorem finite_original_first_jet_at_designated_exponents {d : ℝ} (hd0 : 0 ≤ d) (hd : d < 1)
    (r : ℕ) (γ : Fin r → ℝ) (γ₀ : ℝ)
    (hγ : ∀ i, 0 < γ i) (hγ₀ : ∀ i, γ i ≤ γ₀) :
    ∃ cζ : ℝ, 0 < cζ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
        ∀ (Λ : Type*) [MeasurableSpace Λ], ∀ (D : ScalarMotion Λ) (ν : Measure Λ)
          [IsProbabilityMeasure ν] (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (S : ℝ → Set ℝ)
          (K ζ : ℝ) (Tl : Fin r → ℕ) (T₀ : ℕ),
          1 ≤ K → K ≤ N ^ α → (∀ p ∈ E, |F p.2| ≤ K) →
          ScalarNormalHyp D ν E (scalarClippedRow K F) S (4 * K) ζ d → 0 < ζ →
          K⁻¹ ≤ (ν.prod volume).real E → ζ ≤ N ^ (-cζ) →
          (∀ i, N ^ (-γ i) / K ≤ scalarDyadicLength (Tl i)) →
          (∀ i, scalarDyadicLength (Tl i) ≤ K * N ^ (-γ i)) →
          N ^ (-γ₀) / K ≤ scalarDyadicLength T₀ → scalarDyadicLength T₀ ≤ K * N ^ (-γ₀) →
          ScalarFirstJetOutput D ν E F (Fin.cases T₀ Tl) 0 d (N ^ ε) := by
  by_cases hγ₀pos : 0 < γ₀
  · refine ⟨8 * γ₀, by positivity, ?_⟩
    intro ε hε
    let Γ : Fin (r + 1) → ℝ := Fin.cases γ₀ γ
    have hΓ : ∀ i, 0 < Γ i := by
      intro i
      exact Fin.cases hγ₀pos (fun j => hγ j) i
    have hΓupper : ∀ i, Γ i ≤ γ₀ := by
      intro i
      exact Fin.cases le_rfl (fun j => hγ₀ j) i
    obtain ⟨α, hα, N₀, hN₀, hpositive⟩ :=
      finite_first_jet_at_positive_exponents hd0 hd Γ γ₀ 0 hΓ hΓupper hε
    refine ⟨α, hα, N₀, hN₀, ?_⟩
    intro N hN Λ _ D ν _ E F S K ζ Tl T₀ hK hKN hrow hnormal hζ hmass hζN
      hlow hhigh hlow₀ hhigh₀
    have hlowΓ : ∀ i : Fin (r + 1),
        N ^ (-Γ i) / K ≤ scalarDyadicLength (Fin.cases T₀ Tl i) := by
      intro i
      exact Fin.cases hlow₀ (fun j => hlow j) i
    have hhighΓ : ∀ i : Fin (r + 1),
        scalarDyadicLength (Fin.cases T₀ Tl i) ≤ K * N ^ (-Γ i) := by
      intro i
      exact Fin.cases hhigh₀ (fun j => hhigh j) i
    let start : Fin (r + 1) → ℕ := Fin.cases T₀ Tl
    have hout : ScalarFirstJetOutput D ν E F start 0 d (N ^ ε) :=
      hpositive N hN Λ D ν E F S K ζ start
        hK hKN hrow hnormal hζ hmass hζN hlowΓ hhighΓ
    exact hout
  · refine ⟨1, by norm_num, ?_⟩
    intro ε hε
    obtain ⟨αc, hαc, Nc, hNc, hcoarse⟩ := finite_coarse_first_jet_output hd0 hε (r + 1)
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
        4 (a := αc / 2) (b := αc) (by linarith))
    refine ⟨αc / 2, by positivity, max Nc M, hNc.trans (le_max_left _ _), ?_⟩
    intro N hN Λ _ D ν _ E F S K ζ Tl T₀ hK hKN hrow hnormal hζ hmass hζN
      hlow hhigh hlow₀ hhigh₀
    have hNNc : Nc ≤ N := (le_max_left Nc M).trans hN
    have hNM : M ≤ N := (le_max_right Nc M).trans hN
    have hNtwo : 2 ≤ N := hNc.trans hNNc
    have hN1 : 1 ≤ N := by linarith
    have hKpos : 0 < K := zero_lt_one.trans_le hK
    have hKK : K ≤ 4 * K := by linarith
    have hKprepared : 4 * K ≤ N ^ αc :=
      (mul_le_mul_of_nonneg_left hKN (by norm_num : (0 : ℝ) ≤ 4)).trans (hM N hNM)
    have hmassPrepared : (4 * K)⁻¹ ≤ (ν.prod volume).real E :=
      (inv_anti₀ hKpos hKK).trans hmass
    let Γ : Fin (r + 1) → ℝ := Fin.cases γ₀ γ
    let start : Fin (r + 1) → ℕ := Fin.cases T₀ Tl
    have hlowΓ (i : Fin (r + 1)) :
        N ^ (-Γ i) / K ≤ scalarDyadicLength (start i) :=
      Fin.cases hlow₀ (fun j => hlow j) i
    have hΓnonpos (i : Fin (r + 1)) : Γ i ≤ 0 :=
      Fin.cases (le_of_not_gt hγ₀pos) (fun j => (hγ₀ j).trans (le_of_not_gt hγ₀pos)) i
    have hscale (i : Fin (r + 1)) : 1 / (4 * K) ≤ scalarDyadicLength (start i) := by
      have hpower : 1 ≤ N ^ (-Γ i) :=
        Real.one_le_rpow hN1 (neg_nonneg.mpr (hΓnonpos i))
      have hraw : 1 / K ≤ scalarDyadicLength (start i) :=
        (div_le_div_of_nonneg_right hpower hKpos.le).trans (hlowΓ i)
      have hinv : 1 / (4 * K) ≤ 1 / K := by
        simpa only [one_div] using! inv_anti₀ hKpos hKK
      exact hinv.trans hraw
    exact hcoarse N hNNc Λ D ν E F (4 * K) start 0
      (by linarith : 1 ≤ 4 * K) hKprepared hnormal.event_measurable hnormal.unit_time
      hnormal.coefficients (fun p hp => (hrow p hp).trans hKK) hmassPrepared hscale

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
