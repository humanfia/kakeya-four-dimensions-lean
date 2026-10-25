/- Adapted from this LOT tree, obligation o100, session x0340, commit 3ee9f41,
   Submission/Obl/k4_scalar_marked_profile_selection/CanonicalTransport.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.RealBands
import Submission.Obl.k4_native_grid_profile_extension.Labels

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

/-- The label pairing used in the kernel calculations agrees with the frozen
joint observation after reassociating the product. -/
abbrev canonicalEquiv : Canonical ≃ᵐ JointSpace := MeasurableEquiv.prodAssoc.symm

theorem canonicalEquiv_preserving :
    MeasurePreserving canonicalEquiv canonicalReference jointReference := by
  have h := measurePreserving_prodAssoc (volume : Measure Base)
    (Measure.count : Measure ℤ) (Measure.count : Measure ℤ)
  rw [Submission.Obl.k4_native_grid_profile_extension.count_prod_eq] at h
  exact MeasurePreserving.symm MeasurableEquiv.prodAssoc h

/-- Transport any version of the joint density to canonical label pairing. -/
theorem canonical_density_of_aug (μ : Measure Incidence) (N r u : ℝ)
    (g : JointSpace → ℝ≥0∞) (hg : Measurable g)
    (hglaw : μ.map (aug N r u) = jointReference.withDensity g) :
    μ.map (widthObservation (N ^ (-r)) (N ^ (-u))) =
      canonicalReference.withDensity (g ∘ canonicalEquiv) := by
  have h := congrArg (Measure.map canonicalEquiv.symm) hglaw
  rw [Measure.map_map canonicalEquiv.symm.measurable (measurable_aug _ _ _),
    Submission.Obl.k4_native_grid_profile_extension.map_withDensity_equiv
      jointReference canonicalReference canonicalEquiv.symm
      (MeasurePreserving.symm canonicalEquiv canonicalEquiv_preserving) g hg] at h
  exact h

/-- Exact canonical densities give exact densities for the frozen observation. -/
theorem aug_density_of_canonical (μ : Measure Incidence) (N r u : ℝ)
    (f : Canonical → ℝ≥0∞) (hf : Measurable f)
    (hflaw : μ.map (widthObservation (N ^ (-r)) (N ^ (-u))) =
      canonicalReference.withDensity f) :
    μ.map (aug N r u) = jointReference.withDensity (f ∘ canonicalEquiv.symm) := by
  have h := congrArg (Measure.map canonicalEquiv) hflaw
  rw [Measure.map_map canonicalEquiv.measurable (measurable_widthObservation _ _),
    Submission.Obl.k4_native_grid_profile_extension.map_withDensity_equiv
      canonicalReference jointReference canonicalEquiv canonicalEquiv_preserving f hf] at h
  exact h

/-- The real record-band interface in the exact frozen observation vocabulary. -/
theorem selected_aug_real_band {H J : ℕ} (hJ : 0 < J) {N m r u K : ℝ}
    (hσ : 0 < N ^ (-m)) (hmesh : 1 ≤ (J : ℝ) * N ^ (-m))
    (ha : N ^ (-m) ≤ N ^ (-r)) (hρ : 0 < N ^ (-u)) (hK : 1 ≤ K)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j e, |b j e| ≤ K)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (I T : Finset (AtomIndex H J)) (hT : T ⊆ I)
    {lower upper ε : ℝ} (hε : 0 ≤ ε)
    (hfit : ∀ i ∈ T, lower ≤ realNodeMass I (N ^ (-m)) (N ^ (-u)) w
      (fun i => atomRecord (N ^ (-m)) (N ^ (-r)) (max (N ^ (-m)) (N ^ (-u))) b i.1 i.2)
      (atomRecord (N ^ (-m)) (N ^ (-r)) (max (N ^ (-m)) (N ^ (-u))) b i.1 i.2) ∧
      realNodeMass I (N ^ (-m)) (N ^ (-u)) w
        (fun i => atomRecord (N ^ (-m)) (N ^ (-r)) (max (N ^ (-m)) (N ^ (-u))) b i.1 i.2)
        (atomRecord (N ^ (-m)) (N ^ (-r)) (max (N ^ (-m)) (N ^ (-u))) b i.1 i.2) ≤ upper)
    (g : JointSpace → ℝ≥0∞) (hg : Measurable g)
    (hglaw : (law (N ^ (-m)) H J b w (markOf T)).map (aug N r u) =
      jointReference.withDensity g) :
    law (N ^ (-m)) H J b w (markOf T)
      {p | g (aug N r u p) < ENNReal.ofReal (ε * lower) ∨
        ENNReal.ofReal (geometryLoss K * upper) < g (aug N r u p)} ≤
      ENNReal.ofReal (ε * geometryLoss K) := by
  exact selected_joint_real_band hJ hσ hmesh ha hρ hK b hb w hw hw1 I T hT hε hfit
    (g ∘ canonicalEquiv) (hg.comp canonicalEquiv.measurable)
    (canonical_density_of_aug _ _ _ _ g hg hglaw)

/-- Every whole-atom subtable has an exact density at every admissible pair of
real depths, before any logarithmic selection has been carried out. -/
theorem selected_density_exists {H J : ℕ} (hJ : 0 < J) {σ a ρ K : ℝ}
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hρ : 0 < ρ) (hK : 0 ≤ K)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j e, |b j e| ≤ K) (w : Fin H → ℝ)
    (T : Finset (AtomIndex H J)) :
    (∃ f : ObsSpace → ℝ≥0∞, Measurable f ∧
      (law σ H J b w (markOf T)).map (pureWidthObservation a) = reference.withDensity f) ∧
    (∃ g : Canonical → ℝ≥0∞, Measurable g ∧
      (law σ H J b w (markOf T)).map (widthObservation a ρ) = canonicalReference.withDensity g) := by
  classical
  constructor
  · obtain ⟨f, hf, hflaw, _⟩ := selected_pure_band hJ hσ hσ₁ hmesh ha hK (le_refl _) b hb w
      T T (fun _ h => h) 0 ⊤ 0 (fun _ _ => bot_le) (fun _ _ => le_top)
    exact ⟨f, hf, hflaw⟩
  · obtain ⟨f, hf, hflaw, _⟩ := selected_joint_band hJ hσ hmesh ha hρ
      (le_max_left _ _) (le_max_right _ _) hK (le_refl _) b hb w
      T T (fun _ h => h) 0 ⊤ 0 (fun _ _ => bot_le) (fun _ _ => le_top)
    exact ⟨f, hf, hflaw⟩

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
