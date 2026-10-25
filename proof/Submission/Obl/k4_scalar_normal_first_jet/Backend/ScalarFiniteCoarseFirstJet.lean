/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFiniteCoarseFirstJet.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFiniteCoarseFirstJet.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCoarseFirstJet
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics

/-! A uniform finite threshold for the original coarse first-jet certificate. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Filter

theorem finite_coarse_first_jet_output {d ε : ℝ} (hd : 0 ≤ d) (hε : 0 < ε) (m : ℕ) :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (Λ : Type*) [MeasurableSpace Λ], ∀ (D : ScalarMotion Λ) (ν : Measure Λ)
        (E : Set (Λ × ℝ)) (F : ℝ → ℝ) (K : ℝ) (start : Fin m → ℕ) (read : Fin m),
        1 ≤ K → K ≤ N ^ α → MeasurableSet E → E ⊆ univ ×ˢ Icc (0 : ℝ) 1 →
        (∀ p ∈ E, D.Bounded K p.1) → (∀ p ∈ E, |F p.2| ≤ K) →
        K⁻¹ ≤ (ν.prod volume).real E → (∀ i, 1 / K ≤ scalarDyadicLength (start i)) →
        ScalarFirstJetOutput D ν E F start read d (N ^ ε) := by
  let α := ε / 8
  have hα : 0 < α := by dsimp [α]; positivity
  have hgap : 3 * α < ε := by dsimp [α]; linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (Submission.Obl.k4_fixed_budget_quadratic_recovery.eventually_const_mul_rpow_le 4 hgap)
  refine ⟨α, hα, max 2 M, le_max_left _ _, ?_⟩
  intro N hN Λ _ D ν E F K start read hK hKN hE hunit hcoeff hrow hmass hscale
  have hNtwo : 2 ≤ N := (le_max_left 2 M).trans hN
  have hNpos : 0 < N := by linarith
  have hbudget : 4 * K ^ 3 ≤ N ^ ε := by
    calc
      _ ≤ 4 * (N ^ α) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hK) hKN 3) (by norm_num)
      _ = 4 * N ^ (3 * α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        congr 1 <;> ring
      _ ≤ _ := hM N ((le_max_right 2 M).trans hN)
  exact scalar_first_jet_coarse_output D ν start read hK hd hE hunit hcoeff hrow hmass hscale hbudget

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
