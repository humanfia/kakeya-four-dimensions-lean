/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarVectorFirstJetOutput.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarVectorFirstJetOutput.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetOutput
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarVectorInterface

/-! The original first-jet certificate in normalized coefficient coordinates. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

theorem ScalarFirstJetOutput.to_coefficient_vector
    {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ}
    (c : Λ → Fin 5 → ℝ) (hc : Measurable c)
    {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {r : ℕ} {Tl : Fin r → ℕ} {T₀ : ℕ}
    {d N ε : ℝ} (hN : 0 < N)
    (h : ScalarFirstJetOutput (ScalarMotion.ofCoefficientVector c hc)
      ν E F (Fin.cases T₀ Tl) 0 d (N ^ ε)) :
    ∃ E₁ : Set (Λ × ℝ), E₁ ⊆ E ∧ MeasurableSet E₁ ∧
      ENNReal.ofReal (N ^ (-ε)) ≤ (ν.prod volume) E₁ ∧
      ∃ A : ℝ → ℝ, Measurable A ∧ (∀ p ∈ E₁, |A p.2| ≤ N ^ ε) ∧
        (∀ (i : Fin r) (j : ℤ), ∀ p ∈ E₁, ∀ q ∈ E₁,
          p.2 ∈ Ico ((j : ℝ) / (2 : ℝ) ^ Tl i) (((j : ℝ) + 1) / (2 : ℝ) ^ Tl i) →
          q.2 ∈ Ico ((j : ℝ) / (2 : ℝ) ^ Tl i) (((j : ℝ) + 1) / (2 : ℝ) ^ Tl i) →
          |F q.2 - F p.2 - (q.2 - p.2) * A p.2| ≤
            N ^ ε * (((2 : ℝ) ^ Tl i)⁻¹) ^ (11 / 10 : ℝ)) ∧
        ∀ t : ℝ, ∃ L : ℤ → Finset ℝ, (∀ z, (L z).card ≤ ⌊N ^ ε⌋₊) ∧
          ∀ l : Λ, (l, t) ∈ E₁ →
            ∃ v ∈ L ⌊(c l 0 + c l 1 * t + c l 2 * t ^ 2 -
                F t * (c l 3 + c l 4 * t)) / ((2 : ℝ) ^ T₀)⁻¹⌋,
              |c l 1 + 2 * c l 2 * t - F t * c l 4 - A t * (c l 3 + c l 4 * t) - v| ≤
                N ^ ε * (((2 : ℝ) ^ T₀)⁻¹) ^ ((1 - d) / 32) := by
  have hlength (T : ℕ) : scalarDyadicLength T = ((2 : ℝ) ^ T)⁻¹ := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, one_div] using scalarDyadicLength_eq T
  obtain ⟨E₁, hE₁E, hE₁m, hmass, A, hAm, hAb, hTaylor, L, hL, hcover⟩ := h
  refine ⟨E₁, hE₁E, hE₁m, ?_, A, hAm, hAb, ?_, ?_⟩
  · simpa only [Real.rpow_neg hN.le] using hmass
  · intro i j p hp q hq hpi hqi
    simpa only [Fin.cases_succ, hlength] using hTaylor i.succ j p hp q hq hpi hqi
  · intro t
    refine ⟨L t, fun z => Nat.le_floor (hL t z), ?_⟩
    intro l hl
    simpa only [Fin.cases_zero, hlength, ScalarMotion.scalar, ScalarMotion.x, ScalarMotion.y,
      scalarFirstJet, ScalarMotion.residual, ScalarMotion.ofCoefficientVector] using hcover (l, t) hl

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
