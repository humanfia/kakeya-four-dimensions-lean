/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/ListMultiplicity.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Generic original-law list multiplicity: accepted here:o167,
Submission/Obl/k4_scalar_true_terminal_lifting/ListMultiplicity.lean. No obligation module is imported.
-/

import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open MeasureTheory Set
open scoped ENNReal

theorem sum_restrict_le_smul_of_list
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (C : I → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (L : Ω → Finset I) (hknown : ∀ i, ∀ᵐ z ∂μ.restrict (C i), i ∈ L z)
    (D : ℝ≥0∞) (hcard : ∀ z, ((L z).card : ℝ≥0∞) ≤ D) :
    (∑ i, μ.restrict (C i)) ≤ D • μ := by
  classical
  let f : I → Ω → ℝ≥0∞ := fun i => (C i).indicator 1
  have hrep (i : I) : μ.restrict (C i) = μ.withDensity (f i) :=
    (withDensity_indicator_one (hC i)).symm
  have hf (i : I) : Measurable (f i) :=
    (measurable_const : Measurable (fun _ : Ω => (1 : ℝ≥0∞))).indicator (hC i)
  have hsum : (∑ i, μ.restrict (C i)) = μ.withDensity (fun z => ∑ i, f i z) := by
    simp_rw [hrep]
    rw [← Measure.sum_fintype, ← withDensity_tsum hf]
    congr 1
    ext z
    simp [tsum_fintype]
  have hae : ∀ᵐ z ∂μ, ∀ i, z ∈ C i → i ∈ L z :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hC i)).mp (hknown i))
  have hden : (fun z => ∑ i, f i z) ≤ᵐ[μ] fun _ => D := by
    filter_upwards [hae] with z hz
    have hi (i : I) : f i z ≤ if i ∈ L z then (1 : ℝ≥0∞) else 0 := by
      by_cases hc : z ∈ C i
      · simp [f, hc, hz i hc]
      · simp [f, hc]
    calc
      _ ≤ ∑ i, if i ∈ L z then (1 : ℝ≥0∞) else 0 := Finset.sum_le_sum fun i _ => hi i
      _ = ((L z).card : ℝ≥0∞) := by rw [← Finset.sum_filter]; simp
      _ ≤ D := hcard z
  rw [hsum, ← withDensity_const]
  exact withDensity_mono hden

end Submission.Lib.K4ScalarCoreTools.Finalization
