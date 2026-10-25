/-
Adapted from this LOT tree, o075, session x0249, commit c9860862e62947c5fb8b3bc42c0a4ebc874a7eee,
Submission/Obl/k4_joint_homogenization/NativeRefinement.lean. Earlier source attributions are retained below.
-/

import Submission.Obl.k4_native_grid_profile_extension.CountedRefinement
import Submission.Obl.k4_native_grid_profile_extension.DensityEquiv
import Submission.Obl.k4_native_grid_profile_extension.Dyadic
import Submission.Obl.k4_native_grid_profile_extension.Labels
import Submission.Obl.k4_native_grid_profile_extension.Observation

/-!
# Refinement of the native joint observation
-/

namespace Submission.Obl.k4_native_grid_profile_extension

open Set MeasureTheory
open scoped ENNReal

abbrev BaseSpace := EuclideanSpace ℝ (Fin 3)

noncomputable def nativeObservation (N r u : ℝ) (p : Coefficients × ℝ) :
    AngularObservationSpace :=
  angularObservation 1 (dyadicWidth N r) (dyadicWidth N u) p

noncomputable def jointCanonical : AngularObservationSpace ≃ᵐ (BaseSpace × JointLabel) :=
  MeasurableEquiv.prodAssoc

noncomputable def canonicalObservation (N r u : ℝ) (p : Coefficients × ℝ) :
    BaseSpace × JointLabel := jointCanonical (nativeObservation N r u p)

def canonicalDensity (G : AngularObservationSpace → ℝ≥0∞) (p : BaseSpace × JointLabel) :
    ℝ≥0∞ := G ((p.1, p.2.1), p.2.2)

noncomputable def nativeReference : Measure AngularObservationSpace :=
  ((volume.prod Measure.count).prod Measure.count)

noncomputable def refinementDenominator (N r s : ℝ) : ℕ :=
  2 ^ (depthIndex N s - depthIndex N r)

theorem refinementDenominator_pos (N r s : ℝ) : 0 < refinementDenominator N r s := by
  unfold refinementDenominator
  positivity

theorem measurable_nativeObservation (N r u : ℝ) : Measurable (nativeObservation N r u) :=
  measurable_angularObservation 1 _ _

theorem measurable_canonicalObservation (N r u : ℝ) :
    Measurable (canonicalObservation N r u) :=
  jointCanonical.measurable.comp (measurable_nativeObservation N r u)

theorem measurable_canonicalDensity (G : AngularObservationSpace → ℝ≥0∞)
    (hG : Measurable G) : Measurable (canonicalDensity G) :=
  hG.comp jointCanonical.symm.measurable

theorem measurePreserving_jointCanonical :
    MeasurePreserving jointCanonical nativeReference (volume.prod Measure.count) := by
  simpa only [nativeReference, jointCanonical, count_prod_eq] using
    (measurePreserving_prodAssoc (volume : Measure BaseSpace)
      (Measure.count : Measure ℤ) (Measure.count : Measure (Fin 2 → ℤ)))

/-- Reassociate the continuous base and the three counting labels. -/
theorem canonical_density_law (μ : Measure (Coefficients × ℝ)) (N r u : ℝ)
    (G : AngularObservationSpace → ℝ≥0∞) (hG : Measurable G)
    (hmap : μ.map (nativeObservation N r u) = nativeReference.withDensity G) :
    μ.map (canonicalObservation N r u) =
      (volume.prod Measure.count).withDensity (canonicalDensity G) := by
  have h := congrArg (fun ξ : Measure AngularObservationSpace => ξ.map jointCanonical) hmap
  rw [Measure.map_map jointCanonical.measurable (measurable_nativeObservation N r u),
    map_withDensity_equiv nativeReference (volume.prod Measure.count) jointCanonical
      measurePreserving_jointCanonical G hG] at h
  exact h

/-- Every deeper joint observation determines its coarser observation exactly. -/
theorem canonicalObservation_refinement {N r s u v : ℝ} (hN : 1 ≤ N)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hu : 0 ≤ u) (huv : u ≤ v)
    (p : Coefficients × ℝ) :
    canonicalObservation N r u p =
      ((canonicalObservation N s v p).1,
        labelQuotient (refinementDenominator N r s) (refinementDenominator N u v)
          (canonicalObservation N s v p).2) := by
  refine Prod.ext rfl (Prod.ext ?_ (funext fun j => ?_))
  · change ⌊1 * trajectoryPoint p.1 p.2 3 / dyadicWidth N r⌋ =
      ⌊1 * trajectoryPoint p.1 p.2 3 / dyadicWidth N s⌋ /
        (refinementDenominator N r s : ℤ)
    simpa only [one_mul, refinementDenominator, Nat.cast_pow, Nat.cast_ofNat] using
      floor_dyadicWidth_refinement hN hr hrs (trajectoryPoint p.1 p.2 3)
  · change ⌊planarVelocity p.1 j / dyadicWidth N u⌋ =
      ⌊planarVelocity p.1 j / dyadicWidth N v⌋ /
        (refinementDenominator N u v : ℤ)
    simpa only [refinementDenominator, Nat.cast_pow, Nat.cast_ofNat] using
      floor_dyadicWidth_refinement hN hu huv (planarVelocity p.1 j)

/-- The refinement multiplicity has exactly the expected hidden-plus-angular
power, up to the fixed factor eight from dyadic rounding. -/
theorem joint_refinement_count_le {N r s u v : ℝ} (hN : 1 ≤ N)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hu : 0 ≤ u) (huv : u ≤ v) :
    ((refinementDenominator N r s * (refinementDenominator N u v) ^ 2 : ℕ) : ℝ) ≤
      8 * N ^ ((s - r) + 2 * (v - u)) := by
  have hw := dyadic_refinement_count_le hN hr hrs
  have hv := dyadic_refinement_count_le hN hu huv
  have hNpos : 0 < N := by linarith
  calc
    _ = (2 : ℝ) ^ (depthIndex N s - depthIndex N r) *
        ((2 : ℝ) ^ (depthIndex N v - depthIndex N u)) ^ 2 := by
      simp only [refinementDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 * N ^ (s - r)) * (2 * N ^ (v - u)) ^ 2 := by gcongr
    _ = 8 * N ^ ((s - r) + 2 * (v - u)) := by
      rw [show (s - r) + 2 * (v - u) = (s - r) + ((v - u) + (v - u)) by ring,
        Real.rpow_add hNpos, Real.rpow_add hNpos]
      ring

/-- The fine density is at most the coarse density on the native state space. -/
theorem native_refinement_density_le (μ : Measure (Coefficients × ℝ))
    {N r s u v : ℝ} (hN : 1 ≤ N)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hu : 0 ≤ u) (huv : u ≤ v)
    (f g : AngularObservationSpace → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfmap : μ.map (nativeObservation N r u) = nativeReference.withDensity f)
    (hgmap : μ.map (nativeObservation N s v) = nativeReference.withDensity g) :
    ∀ᵐ p ∂μ, g (nativeObservation N s v p) ≤ f (nativeObservation N r u p) := by
  let q := labelQuotient (refinementDenominator N r s) (refinementDenominator N u v)
  have hcoarse : μ.map (fun p => ((canonicalObservation N s v p).1,
      q (canonicalObservation N s v p).2)) =
      (volume.prod Measure.count).withDensity (canonicalDensity f) := by
    have heq : (fun p => ((canonicalObservation N s v p).1,
        q (canonicalObservation N s v p).2)) = canonicalObservation N r u :=
      funext fun p => (canonicalObservation_refinement hN hr hrs hu huv p).symm
    rw [heq]
    exact canonical_density_law μ N r u f hf hfmap
  have hle := observation_refinement_density_le μ volume
    (canonicalObservation N s v) (measurable_canonicalObservation N s v) q
    (canonicalDensity f) (canonicalDensity g)
    (measurable_canonicalDensity f hf) (measurable_canonicalDensity g hg)
    hcoarse (canonical_density_law μ N s v g hg hgmap)
  filter_upwards [hle] with p hp
  change canonicalDensity g (canonicalObservation N s v p) ≤
    canonicalDensity f (canonicalObservation N r u p)
  rw [canonicalObservation_refinement hN hr hrs hu huv p]
  exact hp

/-- The exact native low-tail bound for a simultaneous hidden and angular refinement. -/
theorem native_refinement_low_density_mass (μ : Measure (Coefficients × ℝ))
    {N r s u v : ℝ} (hN : 1 ≤ N)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hu : 0 ≤ u) (huv : u ≤ v)
    (f g : AngularObservationSpace → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hfmap : μ.map (nativeObservation N r u) = nativeReference.withDensity f)
    (hgmap : μ.map (nativeObservation N s v) = nativeReference.withDensity g)
    (ε : ℝ≥0∞) :
    μ {p | g (nativeObservation N s v p) < ε * f (nativeObservation N r u p)} ≤
      ε * ((refinementDenominator N r s * (refinementDenominator N u v) ^ 2 : ℕ) : ℝ≥0∞) *
        μ Set.univ := by
  let q := labelQuotient (refinementDenominator N r s) (refinementDenominator N u v)
  have heq : (fun p => ((canonicalObservation N s v p).1,
      q (canonicalObservation N s v p).2)) = canonicalObservation N r u :=
    funext fun p => (canonicalObservation_refinement hN hr hrs hu huv p).symm
  have hcoarse : μ.map (fun p => ((canonicalObservation N s v p).1,
      q (canonicalObservation N s v p).2)) =
      (volume.prod Measure.count).withDensity (canonicalDensity f) := by
    rw [heq]
    exact canonical_density_law μ N r u f hf hfmap
  have hbound := observation_refinement_low_density_mass μ volume
    (canonicalObservation N s v) (measurable_canonicalObservation N s v) q ε
    (((refinementDenominator N r s * (refinementDenominator N u v) ^ 2 : ℕ) : ℝ≥0∞))
    (fun c => (count_labelQuotient_fiber (refinementDenominator_pos N r s)
      (refinementDenominator_pos N u v) c).le)
    (canonicalDensity f) (canonicalDensity g)
    (measurable_canonicalDensity f hf) (measurable_canonicalDensity g hg)
    hcoarse (canonical_density_law μ N s v g hg hgmap)
  convert hbound using 1
  congr 1
  ext p
  have hp := congrFun heq p
  change (canonicalDensity g (canonicalObservation N s v p) <
      ε * canonicalDensity f (canonicalObservation N r u p)) ↔ _
  rw [← hp]
  rfl

end Submission.Obl.k4_native_grid_profile_extension
