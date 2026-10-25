import Submission.Obl.k4_marked_scalar_grid_selection.FrozenDensities
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.FiniteBands

/-!
# Finite bands for the frozen observations

The finite whole-atom bands of `Scalar.FiniteBands` (adapted from x0340's o100 work) are
stated for `widthObservation`, which lands in `Base × (ℤ × ℤ)`. The frozen joint observation
`aug` lands in `(Base × ℤ) × ℤ`; the pure observation `obs` is `pureWidthObservation`.
This file restates both bands for the frozen observations, for every density version,
in particular for the Radon-Nikodym derivatives, and gives the exact densities used in
`densityData` at every depth. All code was written in this workspace by x0424.
-/

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection

open MeasureTheory Set
open scoped ENNReal
open Scalar

/-- The frozen joint observation is the canonical one, reassociated. -/
theorem prodAssoc_aug (N r u : ℝ) (p : Incidence) :
    MeasurableEquiv.prodAssoc (aug N r u p) = widthObservation (N ^ (-r)) (N ^ (-u)) p := rfl

theorem measurePreserving_jointReference :
    MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((Fin 2 → ℝ) × ℤ) × ℤ ≃ᵐ (Fin 2 → ℝ) × (ℤ × ℤ))
      jointReference canonicalReference :=
  measurePreserving_jointAssoc

/-- Exact joint density and joint band for the frozen joint observation, valid for
every density version. -/
theorem frozen_joint_band {H J : ℕ} (hJ : 0 < J) {σ N r u q K R : ℝ}
    (hσ : 0 < σ) (hmesh : 1 ≤ (J : ℝ) * σ) (hN : 0 < N) (ha : σ ≤ N ^ (-r))
    (hqσ : σ ≤ q) (hqρ : N ^ (-u) ≤ q)
    (hK : 0 ≤ K) (hR : 10 * (K + 1) ≤ R)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K) (w : Fin H → ℝ)
    (I T : Finset (AtomIndex H J)) (hT : T ⊆ I) (lower upper ε : ℝ≥0∞)
    (hlower : ∀ c ∈ T.image (fun i => atomRecord σ (N ^ (-r)) q b i.1 i.2),
      lower ≤ recordMass I (jointNodeWeight σ (N ^ (-u)) w)
        (fun i => atomRecord σ (N ^ (-r)) q b i.1 i.2) c)
    (hupper : ∀ c ∈ T.image (fun i => atomRecord σ (N ^ (-r)) q b i.1 i.2),
      recordMass I (jointNodeWeight σ (N ^ (-u)) w)
        (fun i => atomRecord σ (N ^ (-r)) q b i.1 i.2) c ≤ upper) :
    (∃ G : JointSpace → ℝ≥0∞, Measurable G ∧
      (law σ H J b w (markOf T)).map (aug N r u) = jointReference.withDensity G) ∧
    ∀ G : JointSpace → ℝ≥0∞, Measurable G →
      (law σ H J b w (markOf T)).map (aug N r u) = jointReference.withDensity G →
      law σ H J b w (markOf T)
        {p | G (aug N r u p) < ε * lower ∨
          ENNReal.ofReal (jointOverlapLoss R) * upper < G (aug N r u p)} ≤
        ε * ENNReal.ofReal (jointVolumeLoss J σ (N ^ (-u)) q R) *
          ∑ i ∈ I, jointNodeWeight σ (N ^ (-u)) w i := by
  obtain ⟨f, hf, hflaw, hband⟩ := selected_joint_band hJ hσ hmesh ha
    (Real.rpow_pos_of_pos hN _) hqσ hqρ hK hR b hb w I T hT lower upper ε hlower hupper
  have he := measurePreserving_jointReference
  have hQ : Measurable (aug N r u) := measurable_aug N r u
  refine ⟨⟨f ∘ MeasurableEquiv.prodAssoc, hf.comp MeasurableEquiv.prodAssoc.measurable,
    density_transfer_symm _ he _ (aug N r u) hQ f hflaw⟩, ?_⟩
  exact bad_mass_transfer _ he _ (aug N r u) hQ
    (fun v => v < ε * lower ∨ ENNReal.ofReal (jointOverlapLoss R) * upper < v) _
    (fun g hg hglaw => hband g hg hglaw)

/-- Exact pure density and pure band for the frozen pure observation, valid for every
density version. The records are the joint records at unit velocity width. -/
theorem frozen_pure_band {H J : ℕ} (hJ : 0 < J) {σ N r K R : ℝ}
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ N ^ (-r))
    (hK : 0 ≤ K) (hR : 10 * (K + 1) ≤ R)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K) (w : Fin H → ℝ)
    (I T : Finset (AtomIndex H J)) (hT : T ⊆ I) (lower upper ε : ℝ≥0∞)
    (hlower : ∀ c ∈ T.image (fun i => atomRecord σ (N ^ (-r)) 1 b i.1 i.2),
      lower ≤ recordMass I (pureNodeWeight σ w)
        (fun i => atomRecord σ (N ^ (-r)) 1 b i.1 i.2) c)
    (hupper : ∀ c ∈ T.image (fun i => atomRecord σ (N ^ (-r)) 1 b i.1 i.2),
      recordMass I (pureNodeWeight σ w)
        (fun i => atomRecord σ (N ^ (-r)) 1 b i.1 i.2) c ≤ upper) :
    (∃ g : ObsSpace → ℝ≥0∞, Measurable g ∧
      (law σ H J b w (markOf T)).map (obs N r) = reference.withDensity g) ∧
    ∀ g : ObsSpace → ℝ≥0∞, Measurable g →
      (law σ H J b w (markOf T)).map (obs N r) = reference.withDensity g →
      law σ H J b w (markOf T)
        {p | g (obs N r p) < ε * lower ∨
          ENNReal.ofReal (pureOverlapLoss K R) * upper < g (obs N r p)} ≤
        ε * ENNReal.ofReal (pureVolumeLoss J σ R) * ∑ i ∈ I, pureNodeWeight σ w i := by
  obtain ⟨f, hf, hflaw, hband⟩ := selected_pure_band hJ hσ hσ₁ hmesh ha hK hR b hb w
    I T hT lower upper ε hlower hupper
  exact ⟨⟨f, hf, hflaw⟩, fun g hg hglaw => hband g hg hglaw⟩

/-- The Radon-Nikodym derivative is an exact density for the frozen joint observation of
any selected table, at every depth with `σ ≤ N ^ (-r)`. -/
theorem frozen_joint_rnDeriv {H J : ℕ} (hJ : 0 < J) {σ N r u K : ℝ}
    (hσ : 0 < σ) (hmesh : 1 ≤ (J : ℝ) * σ) (hN : 0 < N) (ha : σ ≤ N ^ (-r))
    (hK : 0 ≤ K) (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K) (w : Fin H → ℝ)
    (T : Finset (AtomIndex H J)) :
    Measurable (((law σ H J b w (markOf T)).map (aug N r u)).rnDeriv jointReference) ∧
      (law σ H J b w (markOf T)).map (aug N r u) = jointReference.withDensity
        (((law σ H J b w (markOf T)).map (aug N r u)).rnDeriv jointReference) := by
  obtain ⟨⟨G, hGm, hG⟩, _⟩ := frozen_joint_band hJ hσ hmesh hN ha (le_max_left σ (N ^ (-u)))
    (le_max_right σ (N ^ (-u))) hK le_rfl b hb w T T subset_rfl 0 ⊤ 0
    (fun _ _ => zero_le) (fun _ _ => le_top)
  exact rnDeriv_density_of_density _ _ G hGm hG

/-- The Radon-Nikodym derivative is an exact density for the frozen pure observation of any
selected table, at every depth with `σ ≤ N ^ (-r)`. -/
theorem frozen_pure_rnDeriv {H J : ℕ} (hJ : 0 < J) {σ N r K : ℝ}
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ N ^ (-r))
    (hK : 0 ≤ K) (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K) (w : Fin H → ℝ)
    (T : Finset (AtomIndex H J)) :
    Measurable (((law σ H J b w (markOf T)).map (obs N r)).rnDeriv reference) ∧
      (law σ H J b w (markOf T)).map (obs N r) = reference.withDensity
        (((law σ H J b w (markOf T)).map (obs N r)).rnDeriv reference) := by
  obtain ⟨⟨g, hgm, hg⟩, _⟩ := frozen_pure_band hJ hσ hσ₁ hmesh ha hK le_rfl b hb w T T
    subset_rfl 0 ⊤ 0 (fun _ _ => zero_le) (fun _ _ => le_top)
  exact rnDeriv_density_of_density _ _ g hgm hg

end Submission.Obl.k4_marked_scalar_grid_selection
