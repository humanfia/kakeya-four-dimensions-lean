/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarPositiveFirstJet.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarPositiveFirstJet.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFiniteFirstJet
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarNormalInterface
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

/-! Original first jets at arbitrary positive designated exponents and factor-K dyadic choices. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter

theorem finite_first_jet_at_positive_exponents {d ε : ℝ} (hd0 : 0 ≤ d) (hd : d < 1)
    {m : ℕ} (γ : Fin m → ℝ) (b : ℝ) (read : Fin m)
    (hγ : ∀ i, 0 < γ i) (hγb : ∀ i, γ i ≤ b) (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type*) [MeasurableSpace Λ], ∀ (D : ScalarMotion Λ) (ν : Measure Λ)
        [IsProbabilityMeasure ν] (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (S : ℝ → Set ℝ)
        (K ζ : ℝ) (start : Fin m → ℕ),
        1 ≤ K → K ≤ N ^ α → (∀ p ∈ E, |F p.2| ≤ K) →
        ScalarNormalHyp D ν E (scalarClippedRow K F) S (4 * K) ζ d → 0 < ζ →
        K⁻¹ ≤ (ν.prod volume).real E → ζ ≤ N ^ (-(8 * b)) →
        (∀ i, N ^ (-γ i) / K ≤ scalarDyadicLength (start i)) →
        (∀ i, scalarDyadicLength (start i) ≤ K * N ^ (-γ i)) →
        ScalarFirstJetOutput D ν E F start read d (N ^ ε) := by
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ γ ⟨read, Finset.mem_univ _⟩
  let a := γ imin
  have ha : 0 < a := hγ imin
  have hab : a ≤ b := hγb imin
  have hamin : ∀ i, a ≤ γ i := fun i => hmin i (Finset.mem_univ _)
  obtain ⟨αf, hαf, Nf, hNf, hfinite⟩ :=
    finite_original_scalar_first_jet_between_powers_all_labels
      (a := a / 2) (b := 2 * b) (by positivity) (by linarith) hd0 hd m hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le
      4 (a := αf / 2) (b := αf) (by linarith))
  let α := min (αf / 2) (a / 4)
  have hα : 0 < α := lt_min (by positivity) (by positivity)
  refine ⟨α, hα, max Nf M, hNf.trans (le_max_left _ _), ?_⟩
  intro N hN Λ _ D ν _ E F S K ζ start hK hKN hrow hnormal hζ hmass hζN hlow hhigh
  have hNNf : Nf ≤ N := (le_max_left Nf M).trans hN
  have hNM : M ≤ N := (le_max_right Nf M).trans hN
  have hNtwo : 2 ≤ N := hNf.trans hNNf
  have hN1 : 1 ≤ N := by linarith
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hKhalf : K ≤ N ^ (αf / 2) :=
    hKN.trans (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _))
  have hKprepared : 4 * K ≤ N ^ αf :=
    (mul_le_mul_of_nonneg_left hKhalf (by norm_num : (0 : ℝ) ≤ 4)).trans (hM N hNM)
  have hKsmall : K ≤ N ^ (a / 4) :=
    hKN.trans (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _))
  have hrange (i : Fin m) : N ^ (-(2 * b)) ≤ scalarDyadicLength (start i) ∧
      scalarDyadicLength (start i) ≤ N ^ (-(a / 2)) :=
    scalar_factor_power_range hN1 hK ha hab (hamin i) (hγb i) hKsmall (hlow i) (hhigh i)
  have hmassPrepared : (4 * K)⁻¹ ≤ (ν.prod volume).real E :=
    (inv_anti₀ hKpos (by linarith : K ≤ 4 * K)).trans hmass
  have hfloor : ζ ≤ N ^ (-(4 * (2 * b))) := by
    simpa only [show (4 * (2 * b) : ℝ) = 8 * b by ring] using! hζN
  have houtput := hfinite N hNNf Λ D ν E (scalarClippedRow K F) S (4 * K) ζ start read
    (by linarith : 1 ≤ 4 * K) hKprepared hnormal hζ hmassPrepared hfloor
    (fun i => (hrange i).1) (fun i => (hrange i).2)
  exact houtput.congr_input_row (fun p hp => scalarClippedRow_eq hKpos (hrow p hp))

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
