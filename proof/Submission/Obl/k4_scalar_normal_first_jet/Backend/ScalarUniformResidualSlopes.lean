/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarUniformResidualSlopes.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarUniformResidualSlopes.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPreparedResidualSlopes
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarSlopeAsymptotics

/-! Uniform residual-slope concentration for normalized original data. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter
open WangZahlLot.Obl.wz_slab_local_linearity
open Submission.Obl.k4_discrete_of_terminal_charts

theorem uniform_original_residual_slopes {Λ ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (N K : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k) (hsub : SubpowerBound N K)
    {a d ε : ℝ} (ha : 0 < a) (hd0 : 0 ≤ d) (hd : d < 1) (hε : 0 < ε) (j : ℝ) :
    ∀ᶠ k in atTop,
      let p := N k ^ (-a)
      ∀ (ν : Measure Λ) [IsFiniteMeasure ν] (E : Set (Λ × ℝ)) (A : Set Λ)
        (F : ℝ × Λ → ℝ) (b slope : Λ → ℝ) (code : Λ → ι) (J : Finset ι) (S : ℝ → Set ℝ),
        MeasurableSet E → E ⊆ A ×ˢ Icc (0 : ℝ) 1 → Measurable F → Measurable slope → Measurable code →
        ν.real univ ≤ K k → (K k)⁻¹ ≤ (ν.prod volume).real E →
        (J.card : ℝ) ≤ K k * p ^ (-j) →
        (∀ l t, (l, t) ∈ E → code l ∈ J) →
        (∀ t, IntervalAD p d (K k) (S t)) →
        (∀ l t, (l, t) ∈ E → F (t, l) ∈ S t ∩ Icc (-K k) (K k)) →
        (∀ l t, (l, t) ∈ E → |F (t, l) - (b l + slope l * t)| ≤ K k * p) →
        (∀ l ∈ A, ∀ l' ∈ A, code l = code l' → |slope l - slope l'| ≤ K k * p) →
        (∀ t c, c ∈ J → ∀ z : ℤ,
          ν.real {l | (l, t) ∈ E ∧ code l = c ∧ (⌊F (t, l) / p⌋ : ℤ) = z} ≤ K k * p ^ (j + d)) →
        ∃ c : ℝ, N k ^ (-ε) < (ν.prod volume).real
          (E ∩ ({l | |slope l - c| ≤ p ^ ((1 - d) / 4) + K k * p} ×ˢ univ)) := by
  filter_upwards [residual_slope_budgets_eventually N K hN hNt hK hsub ha hd hε j] with k hk
  dsimp only at hk ⊢
  intro ν _ E A F b slope code J S hE hEsub hF hslope hcode hν hmass hJ hcover hS hsupport hfit hspread hjoint
  let p := N k ^ (-a)
  let τ := N k ^ (-ε / 4)
  let η := N k ^ (-ε)
  let γ := (1 - d) / 4
  have hNpos : 0 < N k := zero_lt_one.trans_le (hN k)
  have hKpos : 0 < K k := zero_lt_one.trans_le (hK k)
  have hp : 0 < p := Real.rpow_pos_of_pos hNpos _
  have hτ : 0 < τ := Real.rpow_pos_of_pos hNpos _
  have hη : 0 ≤ η := (Real.rpow_pos_of_pos hNpos _).le
  have hp1 : p ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le (hN k) (show -a ≤ 0 by linarith)
  have hpR : p ≤ 2 * K k := by linarith [hK k]
  have hm : 0 < p ^ j * τ := mul_pos (Real.rpow_pos_of_pos hp _) hτ
  have hC : 0 ≤ K k * p ^ (j + d) := mul_nonneg hKpos.le (Real.rpow_nonneg hp.le _)
  have hΔ : 0 < p ^ γ := Real.rpow_pos_of_pos hp _
  have hbudget : τ * ν.real univ + (p ^ j * τ) * (J.card : ℝ) ≤ (K k)⁻¹ / 2 := by
    apply le_trans ?_ hk.1
    gcongr
  have hgap : (3 * (K k * ((2 * K k) / p) ^ d)) *
      (((η / τ) / (p ^ j * τ) * (K k * p ^ (j + d))) * ν.real univ +
        (2 * (p + 2 * (K k * p)) / (p ^ γ)) * (ν.real univ) ^ 2) < ((K k)⁻¹ / 2) ^ 2 := by
    apply lt_of_le_of_lt ?_ hk.2
    have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
    gcongr
  apply exists_heavy_residual_slope_of_original_data ν hE hEsub hF b slope hslope hcode J hcover
    hp hpR hKpos.le hC hΔ hm hτ hη (mul_nonneg hKpos.le hp.le) (inv_pos.mpr hKpos) S hS
  · intro l t ht
    obtain ⟨hs, hlo, hhi⟩ := hsupport l t ht
    exact ⟨hs, hlo, by linarith⟩
  · exact hfit
  · exact hspread
  · exact hjoint
  · exact hmass
  · exact hbudget
  · exact hgap

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
