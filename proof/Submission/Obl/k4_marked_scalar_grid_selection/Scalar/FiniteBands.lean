/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/FiniteBands.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Kernels

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

local instance finiteBandsPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance finiteBandsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

abbrev jointVolumeLoss (J : ℕ) (σ ρ q R : ℝ) : ℝ :=
  52 * (R + 1) * (8 * R + 18) * σ / (J : ℝ) * (q / ρ)
abbrev jointOverlapLoss (R : ℝ) : ℝ := 26 * (8 * R + 10) * (8 * R + 18)
abbrev pureVolumeLoss (J : ℕ) (σ R : ℝ) : ℝ :=
  2 * (R + 1) * (8 * R + 18) * σ / (J : ℝ)
abbrev pureOverlapLoss (K R : ℝ) : ℝ := (8 * R + 10) * (8 * R + 18) * (8 * K + 10)

/-- Joint exact-density windows obtained by selecting only whole marked atoms.
The fiber masses are those in the old table `I`, before the selection `T`. -/
theorem selected_joint_band {H J : ℕ} (hJ : 0 < J) {σ a ρ q K R : ℝ}
    (hσ : 0 < σ) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hρ : 0 < ρ) (hqσ : σ ≤ q) (hqρ : ρ ≤ q)
    (hK : 0 ≤ K) (hR : 10 * (K + 1) ≤ R)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K) (w : Fin H → ℝ)
    (I T : Finset (AtomIndex H J)) (hT : T ⊆ I) (lower upper ε : ℝ≥0∞)
    (hlower : ∀ c ∈ T.image (fun i => atomRecord σ a q b i.1 i.2),
      lower ≤ recordMass I (jointNodeWeight σ ρ w) (fun i => atomRecord σ a q b i.1 i.2) c)
    (hupper : ∀ c ∈ T.image (fun i => atomRecord σ a q b i.1 i.2),
      recordMass I (jointNodeWeight σ ρ w) (fun i => atomRecord σ a q b i.1 i.2) c ≤ upper) :
    ∃ f : Canonical → ℝ≥0∞, Measurable f ∧
      (law σ H J b w (markOf T)).map (widthObservation a ρ) = canonicalReference.withDensity f ∧
      ∀ g : Canonical → ℝ≥0∞, Measurable g →
        (law σ H J b w (markOf T)).map (widthObservation a ρ) = canonicalReference.withDensity g →
        law σ H J b w (markOf T)
          {p | g (widthObservation a ρ p) < ε * lower ∨
            ENNReal.ofReal (jointOverlapLoss R) * upper < g (widthObservation a ρ p)} ≤
          ε * ENNReal.ofReal (jointVolumeLoss J σ ρ q R) * ∑ i ∈ I, jointNodeWeight σ ρ w i := by
  classical
  have hR0 : 0 ≤ R := by linarith
  have hq0 : 0 < q := hσ.trans_le hqσ
  have h := finite_mixture_band canonicalReference (weightedAtom σ b w) I T hT
    (jointNodeWeight σ ρ w) (fun i => atomRecord σ a q b i.1 i.2)
    (recordSupport σ ρ q R) (widthObservation a ρ) (measurable_widthObservation _ _)
    (measurable_recordSupport _ _ _ _)
    (weighted_joint_kernel hJ hσ hmesh ha hρ hqσ hqρ hK hR b hb w)
    (ENNReal.ofReal (jointVolumeLoss J σ ρ q R)) (ENNReal.ofReal (jointOverlapLoss R))
    lower upper ε (fun c _ => recordSupport_volume hJ hσ hρ hqρ hR0 c) (by
      intro p
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      exact recordSupport_overlap hJ hσ hρ hq0 hR0 _ p
        (by
          intro c hc
          simp only [Finset.mem_filter] at hc
          exact hc.2))
    (by
      intro c hc
      apply hlower c
      simpa only [Finset.mem_image] using hc)
    (by
      intro c hc
      apply hupper c
      simpa only [Finset.mem_image] using hc)
  have hsum : (∑ i ∈ T, weightedAtom σ b w i) = law σ H J b w (markOf T) :=
    (law_eq_selected_atoms hσ hJ b w T).symm
  rw [hsum] at h
  exact h

/-- The same density-band mechanism gives the pure profile using the unit-slope
records and thus the same grid exponent as the joint observation at depth zero. -/
theorem selected_pure_band {H J : ℕ} (hJ : 0 < J) {σ a K R : ℝ}
    (hσ : 0 < σ) (hσ₁ : σ ≤ 1) (hmesh : 1 ≤ (J : ℝ) * σ) (ha : σ ≤ a)
    (hK : 0 ≤ K) (hR : 10 * (K + 1) ≤ R)
    (b : Fin H → Fin 5 → ℝ) (hb : ∀ j i, |b j i| ≤ K) (w : Fin H → ℝ)
    (I T : Finset (AtomIndex H J)) (hT : T ⊆ I) (lower upper ε : ℝ≥0∞)
    (hlower : ∀ c ∈ T.image (fun i => atomRecord σ a 1 b i.1 i.2),
      lower ≤ recordMass I (pureNodeWeight σ w) (fun i => atomRecord σ a 1 b i.1 i.2) c)
    (hupper : ∀ c ∈ T.image (fun i => atomRecord σ a 1 b i.1 i.2),
      recordMass I (pureNodeWeight σ w) (fun i => atomRecord σ a 1 b i.1 i.2) c ≤ upper) :
    ∃ f : ObsSpace → ℝ≥0∞, Measurable f ∧
      (law σ H J b w (markOf T)).map (pureWidthObservation a) = reference.withDensity f ∧
      ∀ g : ObsSpace → ℝ≥0∞, Measurable g →
        (law σ H J b w (markOf T)).map (pureWidthObservation a) = reference.withDensity g →
        law σ H J b w (markOf T)
          {p | g (pureWidthObservation a p) < ε * lower ∨
            ENNReal.ofReal (pureOverlapLoss K R) * upper < g (pureWidthObservation a p)} ≤
          ε * ENNReal.ofReal (pureVolumeLoss J σ R) * ∑ i ∈ I, pureNodeWeight σ w i := by
  classical
  have hR0 : 0 ≤ R := by linarith
  have h := finite_mixture_band reference (weightedAtom σ b w) I T hT
    (pureNodeWeight σ w) (fun i => atomRecord σ a 1 b i.1 i.2)
    (pureRecordSupport σ K R) (pureWidthObservation a) (by fun_prop)
    (measurable_pureRecordSupport _ _ _)
    (weighted_pure_kernel hJ hσ hσ₁ hmesh ha hK hR b hb w)
    (ENNReal.ofReal (pureVolumeLoss J σ R)) (ENNReal.ofReal (pureOverlapLoss K R))
    lower upper ε (fun c _ => pureRecordSupport_volume hJ hσ hR0 c) (by
      intro p
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      exact pureRecordSupport_overlap hJ hσ hK hR0 _ p
        (by
          intro c hc
          simp only [Finset.mem_filter] at hc
          exact hc.2))
    (by
      intro c hc
      apply hlower c
      simpa only [Finset.mem_image] using hc)
    (by
      intro c hc
      apply hupper c
      simpa only [Finset.mem_image] using hc)
  have hsum : (∑ i ∈ T, weightedAtom σ b w i) = law σ H J b w (markOf T) :=
    (law_eq_selected_atoms hσ hJ b w T).symm
  rw [hsum] at h
  exact h

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
