/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/Kernels.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.AtomTable
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.PureAtomRecords
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.MixtureBands

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

abbrev weightedAtom {H J : ℕ} (σ : ℝ) (b : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ)
    (a : AtomIndex H J) : Measure Incidence := ENNReal.ofReal (w a.1) • atom σ J b a.1 a.2

abbrev jointNodeWeight {H J : ℕ} (σ ρ : ℝ) (w : Fin H → ℝ) (a : AtomIndex H J) : ℝ≥0∞ :=
  ENNReal.ofReal (w a.1) * ENNReal.ofReal (σ⁻¹ * min 1 (ρ / σ))

abbrev pureNodeWeight {H J : ℕ} (σ : ℝ) (w : Fin H → ℝ) (a : AtomIndex H J) : ℝ≥0∞ :=
  ENNReal.ofReal (w a.1) * ENNReal.ofReal σ⁻¹

/-- Densities of individual weighted atoms, with the deterministic support and
pointwise cap needed by the whole-atom band argument. -/
theorem weighted_joint_kernel {H J : ℕ} (hJ : 0 < J) {σ a ρ q K R : ℝ}
    (hσ : 0 < σ) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hρ : 0 < ρ) (hqσ : σ ≤ q) (hqρ : ρ ≤ q)
    (hK : 0 ≤ K) (hR : 10 * (K + 1) ≤ R)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K) (w : Fin H → ℝ)
    (i : AtomIndex H J) :
    ∃ f : Canonical → ℝ≥0∞, Measurable f ∧
      (weightedAtom σ b w i).map (widthObservation a ρ) = canonicalReference.withDensity f ∧
      ∀ p, f p ≤ (recordSupport σ ρ q R (atomRecord σ a q b i.1 i.2)).indicator
        (fun _ => jointNodeWeight σ ρ w i) p := by
  letI : IsFiniteMeasure (atom σ J b i.1 i.2) :=
    ⟨by rw [atom_mass hσ hJ]; exact ENNReal.ofReal_lt_top⟩
  let Q := widthObservation a ρ
  have hQ : Measurable Q := measurable_widthObservation _ _
  let S := recordSupport σ ρ q R (atomRecord σ a q b i.1 i.2)
  have hS : MeasurableSet S := measurable_recordSupport _ _ _ _ _
  have hs : ∀ᵐ p ∂(atom σ J b i.1 i.2).map Q, p ∈ S :=
    (ae_map_iff hQ.aemeasurable hS).mpr
      (atom_supported_on_record hJ hσ hmesh ha hρ hqσ hqρ hK hR b hb i.1 i.2)
  obtain ⟨f, hf, hflaw, hcap⟩ := bounded_supported_density
    ((atom σ J b i.1 i.2).map Q) canonicalReference _
    (atom_joint_density_bound hσ hρ a b i.1 i.2) S hS hs
  refine ⟨ENNReal.ofReal (w i.1) • f, measurable_const.mul hf, ?_, ?_⟩
  · rw [weightedAtom, Measure.map_smul _ hQ.aemeasurable, hflaw, ← withDensity_smul _ hf]
  · intro p
    have h := mul_le_mul' (le_refl (ENNReal.ofReal (w i.1))) (hcap p)
    simpa only [S, jointNodeWeight, pureNodeWeight, Pi.smul_apply, smul_eq_mul, Set.indicator_mul_right] using h

/-- Pure densities use the joint unit-slope record and its original weights. -/
theorem weighted_pure_kernel {H J : ℕ} (hJ : 0 < J) {σ a K R : ℝ}
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hK : 0 ≤ K) (hR : 10 * (K + 1) ≤ R)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K) (w : Fin H → ℝ)
    (i : AtomIndex H J) :
    ∃ f : ObsSpace → ℝ≥0∞, Measurable f ∧
      (weightedAtom σ b w i).map (pureWidthObservation a) = reference.withDensity f ∧
      ∀ p, f p ≤ (pureRecordSupport σ K R (atomRecord σ a 1 b i.1 i.2)).indicator
        (fun _ => pureNodeWeight σ w i) p := by
  letI : IsFiniteMeasure (atom σ J b i.1 i.2) :=
    ⟨by rw [atom_mass hσ hJ]; exact ENNReal.ofReal_lt_top⟩
  let Q := pureWidthObservation a
  have hQ : Measurable Q := by fun_prop
  let S := pureRecordSupport σ K R (atomRecord σ a 1 b i.1 i.2)
  have hS : MeasurableSet S := measurable_pureRecordSupport _ _ _ _
  have hs : ∀ᵐ p ∂(atom σ J b i.1 i.2).map Q, p ∈ S :=
    (ae_map_iff hQ.aemeasurable hS).mpr
      (atom_supported_on_pure_record hJ hσ hσ₁ hmesh ha hK hR b hb i.1 i.2)
  obtain ⟨f, hf, hflaw, hcap⟩ := bounded_supported_density
    ((atom σ J b i.1 i.2).map Q) reference _ (atom_pure_density_bound hσ a b i.1 i.2) S hS hs
  refine ⟨ENNReal.ofReal (w i.1) • f, measurable_const.mul hf, ?_, ?_⟩
  · rw [weightedAtom, Measure.map_smul _ hQ.aemeasurable, hflaw, ← withDensity_smul _ hf]
  · intro p
    have h := mul_le_mul' (le_refl (ENNReal.ofReal (w i.1))) (hcap p)
    simpa only [S, jointNodeWeight, pureNodeWeight, Pi.smul_apply, smul_eq_mul, Set.indicator_mul_right] using h

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
