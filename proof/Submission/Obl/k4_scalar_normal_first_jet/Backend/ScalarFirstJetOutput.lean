/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFirstJetOutput.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFirstJetOutput.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetValue
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicBridge
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Original-law first-jet certificates and monotone output tolerances. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

def ScalarFirstJetOutput {Λ : Type*} [MeasurableSpace Λ] {m : ℕ}
    (D : ScalarMotion Λ) (ν : Measure Λ) (E : Set (Λ × ℝ)) (F : ℝ → ℝ)
    (start : Fin m → ℕ) (read : Fin m) (d H : ℝ) : Prop :=
  ∃ E₁ : Set (Λ × ℝ), E₁ ⊆ E ∧ MeasurableSet E₁ ∧
    ENNReal.ofReal H⁻¹ ≤ (ν.prod volume) E₁ ∧
    ∃ A : ℝ → ℝ, Measurable A ∧ (∀ p ∈ E₁, |A p.2| ≤ H) ∧
      (∀ (i : Fin m) (j : ℤ), ∀ p ∈ E₁, ∀ q ∈ E₁,
        p.2 ∈ Ico ((j : ℝ) / (2 : ℝ) ^ start i) (((j : ℝ) + 1) / (2 : ℝ) ^ start i) →
        q.2 ∈ Ico ((j : ℝ) / (2 : ℝ) ^ start i) (((j : ℝ) + 1) / (2 : ℝ) ^ start i) →
        |F q.2 - F p.2 - (q.2 - p.2) * A p.2| ≤
          H * scalarDyadicLength (start i) ^ (11 / 10 : ℝ)) ∧
      ∃ L : ℝ → ℤ → Finset ℝ, (∀ t z, ((L t z).card : ℝ) ≤ H) ∧
        ∀ p ∈ E₁, ∃ v ∈ L p.2 ⌊D.scalar F p.1 p.2 / scalarDyadicLength (start read)⌋,
          |scalarFirstJet D F A p.1 p.2 - v| ≤
            H * scalarDyadicLength (start read) ^ ((1 - d) / 32)

namespace ScalarFirstJetOutput

theorem mono {Λ : Type*} [MeasurableSpace Λ] {m : ℕ}
    {D : ScalarMotion Λ} {ν : Measure Λ} {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {start : Fin m → ℕ} {read : Fin m} {d H H' : ℝ}
    (h : ScalarFirstJetOutput D ν E F start read d H) (hH : 0 < H) (hHH' : H ≤ H') :
    ScalarFirstJetOutput D ν E F start read d H' := by
  obtain ⟨E₁, hE₁E, hE₁m, hmass, A, hAm, hAb, hTaylor, L, hL, hcover⟩ := h
  refine ⟨E₁, hE₁E, hE₁m,
    (ENNReal.ofReal_le_ofReal (inv_anti₀ hH hHH')).trans hmass,
    A, hAm, fun p hp => (hAb p hp).trans hHH', ?_, L,
    fun t z => (hL t z).trans hHH', ?_⟩
  · intro i j p hp q hq hpi hqi
    exact (hTaylor i j p hp q hq hpi hqi).trans
      (mul_le_mul_of_nonneg_right hHH' (Real.rpow_nonneg (scalarDyadicLength_pos _).le _))
  · intro p hp
    obtain ⟨v, hv, hdist⟩ := hcover p hp
    exact ⟨v, hv, hdist.trans
      (mul_le_mul_of_nonneg_right hHH' (Real.rpow_nonneg (scalarDyadicLength_pos _).le _))⟩

/-- The stored row may change away from the original active event:
the same selected set, Taylor row, and reading lists still work. -/
theorem congr_input_row {Λ : Type*} [MeasurableSpace Λ] {m : ℕ}
    {D : ScalarMotion Λ} {ν : Measure Λ} {E : Set (Λ × ℝ)} {F F' : ℝ → ℝ}
    {start : Fin m → ℕ} {read : Fin m} {d H : ℝ}
    (h : ScalarFirstJetOutput D ν E F start read d H)
    (hF : ∀ p ∈ E, F p.2 = F' p.2) : ScalarFirstJetOutput D ν E F' start read d H := by
  obtain ⟨E₁, hE₁E, hE₁m, hmass, A, hAm, hAb, hTaylor, L, hL, hcover⟩ := h
  refine ⟨E₁, hE₁E, hE₁m, hmass, A, hAm, hAb, ?_, L, hL, ?_⟩
  · intro i j p hp q hq hpi hqi
    rw [← hF p (hE₁E hp), ← hF q (hE₁E hq)]
    exact hTaylor i j p hp q hq hpi hqi
  · intro p hp
    obtain ⟨v, hv, hdist⟩ := hcover p hp
    have hscalar : D.scalar F p.1 p.2 = D.scalar F' p.1 p.2 := by
      dsimp only [ScalarMotion.scalar]
      rw [hF p (hE₁E hp)]
    have hjet : scalarFirstJet D F A p.1 p.2 = scalarFirstJet D F' A p.1 p.2 := by
      dsimp only [scalarFirstJet, ScalarMotion.residual]
      rw [hF p (hE₁E hp)]
    exact ⟨v, by simpa only [hscalar] using hv, by simpa only [hjet] using hdist⟩

end ScalarFirstJetOutput

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
