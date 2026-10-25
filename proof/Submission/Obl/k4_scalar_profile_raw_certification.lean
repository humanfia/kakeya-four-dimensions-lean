import Mathlib
import ChallengeDeps
import Submission.Obl.k4_scalar_profile_raw_certification.Extraction
import Submission.Obl.k4_scalar_profile_raw_certification.Subsequence
set_option linter.unusedVariables false

open Submission.Obl.k4_scalar_profile_raw_certification

/-!
# `Submission.k4_scalar_profile_raw_certification`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_scalar_profile_raw_certification`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_scalar_profile_raw_certification/`
belong to this obligation.
-/

theorem Submission.k4_scalar_profile_raw_certification : ((fun (Subpower : ∀ (N K : ℕ → ℝ), Prop) => ((fun (y : ∀ (l : (ℕ × (Fin 5 → ℝ))) (t : ℝ), ℝ) => ((fun (x : ∀ (l : (ℕ × (Fin 5 → ℝ))) (t : ℝ), ℝ) => ((fun (obs : ∀ (N r : ℝ) (p : ((ℕ × (Fin 5 → ℝ)) × ℝ)), ((Fin 2 → ℝ) × ℤ)) => ((fun (aug : ∀ (N r u : ℝ) (p : ((ℕ × (Fin 5 → ℝ)) × ℝ)), (((Fin 2 → ℝ) × ℤ) × ℤ)) => ((fun (reference : MeasureTheory.Measure ((Fin 2 → ℝ) × ℤ)) => ((fun (jointReference : MeasureTheory.Measure (((Fin 2 → ℝ) × ℤ) × ℤ)) => ((fun (raw : ∀ (N K d s m S U c : ℝ) (angular : Bool) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)), Prop) => ((fun (homogeneous : ∀ (N : ℕ → ℝ) (s V : ℝ) (μ : ℕ → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (F : ℝ → ℝ → ℝ), Prop) => ((fun (numerical : ∀ (d s m S U C₀ : ℝ) (angular : Bool) (F : ℝ → ℝ → ℝ), Prop) => ∀ (N K L : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → Subpower N K → Subpower N L → ∀ d s m C S U : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → 0 < C → 0 < S → 0 < U → U < m → ∀ (c : ℕ → ℝ) (angular : ℕ → Bool) (μ ν : ℕ → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)), (∀ k, N k ^ (-C) ≤ c k ∧ c k ≤ N k ^ C) → (∀ k, ν k ≤ μ k) → (∀ k, ENNReal.ofReal ((L k)⁻¹) ≤ ν k Set.univ) → (∀ k, raw (N k) (K k) d s m S U (c k) (angular k) (μ k)) → ∀ F : ℝ → ℝ → ℝ, homogeneous N s (4 * (m + s + 1)) ν F → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (angular₀ : Bool) (C₀ : ℝ), (∀ k, angular (φ k) = angular₀) ∧ (∀ τ : ℝ, 0 < τ → ∀ᶠ k in Filter.atTop, N (φ k) ^ (C₀ - τ) ≤ c (φ k) ∧ c (φ k) ≤ N (φ k) ^ (C₀ + τ)) ∧ numerical d s m S U C₀ angular₀ F) (fun (d s m S U C₀ : ℝ) (angular : Bool) (F : ℝ → ℝ → ℝ) => F s 0 = d * s - C₀ ∧ (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) → d * r - C₀ + max 0 (u - m) ≤ F r u) ∧ (angular = true → ∀ u : ℝ, 0 ≤ u → u ≤ U → F s 0 + S * u ≤ F s u)))) (fun (N : ℕ → ℝ) (s V : ℝ) (μ : ℕ → MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (F : ℝ → ℝ → ℝ) => ∃ (g : ℕ → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal) (G : ℕ → ℝ → ℝ → (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal), (∀ k r, 0 ≤ r → r ≤ s → Measurable (g k r) ∧ (μ k).map (obs (N k) r) = reference.withDensity (g k r)) ∧ (∀ k r u, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V → Measurable (G k r u) ∧ (μ k).map (aug (N k) r u) = jointReference.withDensity (G k r u)) ∧ (∀ r τ : ℝ, 0 ≤ r → r ≤ s → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, μ k {p | g k r (obs (N k) r p) < ENNReal.ofReal (N k ^ (-F r 0 - τ)) ∨ ENNReal.ofReal (N k ^ (-F r 0 + τ)) < g k r (obs (N k) r p)} ≤ ENNReal.ofReal (N k ^ (-c))) ∧ (∀ r u τ : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ V → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop, μ k {p | G k r u (aug (N k) r u p) < ENNReal.ofReal (N k ^ (-F r u - τ)) ∨ ENNReal.ofReal (N k ^ (-F r u + τ)) < G k r u (aug (N k) r u p)} ≤ ENNReal.ofReal (N k ^ (-c)))))) (fun (N K d s m S U c : ℝ) (angular : Bool) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) => (∀ r : ℝ, 0 ≤ r → r ≤ s → ∃ g : ((Fin 2 → ℝ) × ℤ) → ENNReal, Measurable g ∧ μ.map (obs N r) = reference.withDensity g ∧ ∀ᵐ z ∂reference, g z ≤ ENNReal.ofReal (K * c * N ^ (-d * r))) ∧ (∀ r u : ℝ, 0 ≤ r → r ≤ s → 0 ≤ u → u ≤ 4 * (m + s + 1) → ∃ G : (((Fin 2 → ℝ) × ℤ) × ℤ) → ENNReal, Measurable G ∧ μ.map (aug N r u) = jointReference.withDensity G ∧ (∀ᵐ z ∂jointReference, G z ≤ ENNReal.ofReal (K * c * N ^ (-d * r) * min 1 (N ^ (m - u)))) ∧ (r = s → angular = true → 0 < u → u ≤ U → ∀ᵐ z ∂jointReference, G z ≤ ENNReal.ofReal (K * c * N ^ (-d * s - S * u)))) ∧ (∃ B : Set ((Fin 2 → ℝ) × ℤ), MeasurableSet B ∧ reference B ≤ ENNReal.ofReal (K * c⁻¹ * N ^ (d * s)) ∧ ∀ᵐ p ∂μ, obs N s p ∈ B)))) (reference.prod (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)))) (MeasureTheory.volume.prod (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)))) (fun (N r u : ℝ) (p : ((ℕ × (Fin 5 → ℝ)) × ℝ)) => (obs N r p, ⌊p.1.2 1 / N ^ (-u)⌋)))) (fun (N r : ℝ) (p : ((ℕ × (Fin 5 → ℝ)) × ℝ)) => (![p.2, y p.1 p.2], ⌊x p.1 p.2 / N ^ (-r)⌋)))) (fun (l : (ℕ × (Fin 5 → ℝ))) (t : ℝ) => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4))) (fun (l : (ℕ × (Fin 5 → ℝ))) (t : ℝ) => l.2 0 + t * l.2 1))) (fun (N K : ℕ → ℝ) => (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε)) := by
  intro N K L hN hNt hK hL d s m C S U hd hd1 hs hsm hC hS hU hUm
    c angular μ ν hc hdom hmass hraw F hhom
  change (∀ k, Raw (N k) (K k) d s m S U (c k) (angular k) (μ k)) at hraw
  change Homogeneous N s (4 * (m + s + 1)) ν F at hhom
  obtain ⟨φ, hφ, angular₀, C₀, hangular, hexponent⟩ :=
    exists_subseq_flag_exponent N c C hN hc angular
  exact ⟨φ, hφ, angular₀, C₀, hangular, hexponent,
    numerical_on_subsequence hN hNt hK hL hs hsm hUm hφ hangular hdom hmass
      hraw hexponent hhom⟩
