/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/SubmeasurePaths.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SelectedPaths

/-! Arbitrary dominated final laws, including residual laws with fractional
densities, return through the same original frames with unchanged priors and
weights. Their total original mass is calibrated exactly. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

def submeasureLaw {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    (η : Measure (Fin (W z k) × State)) : Measure (Fin (W p (chain.sample k)) × State) :=
  (chain.originalLaw k univ) • η.map (chain.pullback k)

theorem submeasureLaw_mono {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    {η ζ : Measure (Fin (W z k) × State)} (hη : η ≤ ζ) :
    chain.submeasureLaw k η ≤ chain.submeasureLaw k ζ := by
  apply Measure.le_iff.mpr
  intro S _
  simp only [submeasureLaw, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl ((Measure.map_mono hη (chain.measurable_pullback k)) S)

theorem submeasureLaw_le_originalLaw {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) {η : Measure (Fin (W z k) × State)}
    (hη : η ≤ normalizedWorldMixture z k) : chain.submeasureLaw k η ≤ chain.originalLaw k := by
  apply (chain.submeasureLaw_mono k hη).trans
  have h : chain.submeasureLaw k (normalizedWorldMixture z k) = chain.originalLaw k := by
    rw [submeasureLaw, ← chain.probability_eq_map_finalMixture k, probability, smul_smul,
      ENNReal.mul_inv_cancel (chain.originalLaw_mass_pos hz k).ne'
        ((chain.originalLaw_mass_le_one hz k).trans_lt (by simp)).ne, one_smul]
  exact h.le

theorem submeasureLaw_le_originalReference {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) {η : Measure (Fin (W z k) × State)}
    (hη : η ≤ normalizedWorldMixture z k) :
    chain.submeasureLaw k η ≤ worldMixture p (chain.sample k) :=
  (chain.submeasureLaw_le_originalLaw hz k hη).trans (chain.originalLaw_le k)

def submeasureWorldLaw {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    (η : Measure (Fin (W z k) × State)) (g : Fin (W p (chain.sample k))) : Measure State :=
  originalFibers p (chain.sample k) (chain.submeasureLaw k η) g

theorem submeasureWorldLaw_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) {η : Measure (Fin (W z k) × State)}
    (hη : η ≤ normalizedWorldMixture z k) (g : Fin (W p (chain.sample k))) :
    chain.submeasureWorldLaw k η g ≤ mu p (chain.sample k) g :=
  originalFibers_le (chain.submeasureLaw_le_originalReference hz k hη) g

theorem submeasureWorldLaw_weighted_apply {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) {η : Measure (Fin (W z k) × State)}
    (hη : η ≤ normalizedWorldMixture z k) (g : Fin (W p (chain.sample k)))
    {B : Set State} (hB : MeasurableSet B) :
    ENNReal.ofReal (ω p (chain.sample k) g) * chain.submeasureWorldLaw k η g B =
      chain.originalLaw k univ * η (chain.pullback k ⁻¹' ({g} ×ˢ B)) := by
  have h := congrArg (fun μ : Measure State => μ B)
    (weighted_originalFibers (chain.submeasureLaw_le_originalReference hz k hη) g)
  simp only [Measure.smul_apply, smul_eq_mul] at h
  change ENNReal.ofReal (ω p (chain.sample k) g) * _ = _ at h
  rw [worldFiber_apply _ _ hB, submeasureLaw, Measure.smul_apply,
    Measure.map_apply (chain.measurable_pullback k) ((measurableSet_singleton g).prod hB)] at h
  exact h

theorem submeasureWorldLaw_mass {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) {η : Measure (Fin (W z k) × State)}
    (hη : η ≤ normalizedWorldMixture z k) :
    ∑ g, ENNReal.ofReal (ω p (chain.sample k) g) * chain.submeasureWorldLaw k η g univ =
      chain.originalLaw k univ * η univ := by
  rw [show (∑ g, ENNReal.ofReal (ω p (chain.sample k) g) *
      chain.submeasureWorldLaw k η g univ) = chain.submeasureLaw k η univ from
    originalFibers_mass (chain.submeasureLaw_le_originalReference hz k hη)]
  rw [submeasureLaw, Measure.smul_apply,
    Measure.map_apply (chain.measurable_pullback k) MeasurableSet.univ, preimage_univ]
  rfl

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain
