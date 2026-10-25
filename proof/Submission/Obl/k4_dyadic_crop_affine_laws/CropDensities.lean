/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

import Submission.Obl.k4_dyadic_crop_affine_laws.CropSlope
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.IncidenceTransport

namespace Submission.Obl.k4_dyadic_crop_affine_laws

open MeasureTheory Set
open scoped ENNReal

lemma measurable_Obs (N : ℕ → ℝ) (k : ℕ) (r : ℝ) : Measurable (Obs N k r) := by
  unfold Obs Point
  fun_prop

lemma measurable_JointObs (N : ℕ → ℝ) (k : ℕ) (r u : ℝ) : Measurable (JointObs N k r u) := by
  unfold JointObs Obs Point
  fun_prop

lemma measurableSet_Cell (a : ℝ) (q : Fin 4 → ℤ) : MeasurableSet (Cell a q) := by
  have h (j : Fin 6) (z : ℤ) : MeasurableSet {l : Line | ⌊l.2 j / a⌋ = z} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  exact (h 0 (q 0)).inter ((h 1 (q 1)).inter ((h 3 (q 2)).inter (h 4 (q 3))))

lemma selected_base_ac (N : ℕ → ℝ) (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set Inc)
    (hden : JointDensities N ν₀ E₀) (k : ℕ) :
    (Selected (ν₀ k) (E₀ k)).map Framework.baseObservation ≪ volume := by
  obtain ⟨g, hg, hmap⟩ := hden k 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hac : (Selected (ν₀ k) (E₀ k)).map (JointObs N k 0 0) ≪ JointRef := by
    rw [hmap]
    exact withDensity_absolutelyContinuous _ _
  exact Framework.base_marginal_ac_of_joint _ volume _ (measurable_JointObs N k 0 0) hac

/-- Existence of the cropped density laws only uses base absolute continuity;
the countable labels may be adjoined after the coordinate change. -/
theorem cropDensities_of_relations
    (N : ℕ → ℝ) (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set Inc) (L u₀ β : ℝ)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure Line) (E : (k : ℕ) → Fin (W k) → Set Inc)
    (p : (k : ℕ) → Fin (W k) → ℝ) (q : (k : ℕ) → Fin (W k) → (Fin 4 → ℤ))
    (ρ : ℕ → ℝ) (hsource : FiniteSource ν₀ E₀)
    (hcrop : CropRelations N ν₀ E₀ u₀ β W ω ν E p q ρ)
    (hden : JointDensities N ν₀ E₀) :
    ∃ (g : (k : ℕ) → Fin (W k) → ℝ → Base → ENNReal)
      (G : (k : ℕ) → Fin (W k) → ℝ → Joint → ENNReal),
      CropDensities N L u₀ W ν E g G := by
  classical
  have hbase (k : ℕ) (γ : Fin (W k)) :
      IsFiniteMeasure (Selected (ν k γ) (E k γ)) ∧
        (Selected (ν k γ) (E k γ)).map Framework.baseObservation ≪ volume := by
    letI : IsProbabilityMeasure (ν₀ k) := (hsource k).1
    obtain ⟨hp, hpeq, hν, hE⟩ := hcrop.2.1 k γ
    let a := Scale N k u₀
    have ha : 0 < a := scale_pos N k u₀
    let A := Cell a (q k γ)
    let c : Fin 2 → ℝ := ![a * (q k γ 0 : ℝ), a * (q k γ 1 : ℝ)]
    let v : Fin 2 → ℝ := ![a * (q k γ 2 : ℝ), a * (q k γ 3 : ℝ)]
    let e := (Framework.cropTrajectoryEquiv a ha.ne' c v).symm
    let eT := e.prodCongr (MeasurableEquiv.refl ℝ)
    have hAmeas : MeasurableSet A := measurableSet_Cell _ _
    have hAfin : ν₀ k A ≠ ∞ := measure_ne_top _ _
    have hp_eq : ENNReal.ofReal (p k γ) = ν₀ k A := by
      rw [hpeq, ENNReal.ofReal_toReal hAfin]
    have hApos : ν₀ k A ≠ 0 := by
      rw [← hp_eq]
      exact ENNReal.ofReal_ne_zero_iff.mpr hp
    have hprior : ν k γ = Framework.conditionedPrior (ν₀ k) A e := by
      change ν k γ = (ENNReal.ofReal (p k γ))⁻¹ •
        ((ν₀ k).restrict A).map (Crop a (q k γ)) at hν
      rw [Crop_eq_cropTrajectoryEquiv_symm ha, hp_eq] at hν
      exact hν
    have hInc : CropInc a (q k γ) = eT := by
      funext z
      change (Crop a (q k γ) z.1, z.2) = (e z.1, z.2)
      rw [Crop_eq_cropTrajectoryEquiv_symm ha]
    have hevent : E k γ = eT '' (E₀ k ∩ (A ×ˢ univ)) := by
      change E k γ = CropInc a (q k γ) '' (E₀ k ∩ (A ×ˢ univ)) at hE
      rw [hInc] at hE
      exact hE
    have htime : E k γ ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
      rw [hevent]
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨mem_univ _, ((hsource k).2.2 hz.1).2⟩
    have hprob : IsProbabilityMeasure (ν k γ) := by
      rw [hprior]
      exact Framework.conditionedPrior_probability _ _ _ hApos hAfin
    letI : IsProbabilityMeasure (ν k γ) := hprob
    refine ⟨Framework.finite_selected_incidence _ _ htime, ?_⟩
    let h := (Framework.cropBaseEquiv a ha.ne' c v).symm
    have hcomm (z : Inc) : Framework.baseObservation (eT z) = h (Framework.baseObservation z) := by
      apply (Framework.cropBaseEquiv a ha.ne' c v).injective
      rw [MeasurableEquiv.apply_symm_apply]
      have hf := congrArg Prod.fst (Framework.crop_pureObservation a ha.ne' c v 1 1
        (e z.1, z.2))
      change Framework.baseObservation
        (Framework.cropTrajectoryEquiv a ha.ne' c v (e z.1), z.2) =
          Framework.cropBaseEquiv a ha.ne' c v (Framework.baseObservation (e z.1, z.2)) at hf
      change Framework.cropBaseEquiv a ha.ne' c v
        (Framework.baseObservation (e z.1, z.2)) = Framework.baseObservation z
      simpa only [e, MeasurableEquiv.apply_symm_apply] using hf.symm
    have hJac : (volume : Measure (EuclideanSpace ℝ (Fin 3))).map h ≪ volume := by
      rw [show h = (Framework.cropBaseEquiv a ha.ne' c v).symm from rfl,
        Framework.map_cropBaseEquiv_symm a ha]
      exact Measure.smul_absolutelyContinuous
    change (((ν k γ).prod (volume : Measure ℝ)).restrict (E k γ)).map Framework.baseObservation ≪ volume
    rw [hprior, hevent]
    exact Framework.conditioned_base_absolutelyContinuous (ν₀ k) A (E₀ k)
      hAmeas (hsource k).2.1 e Framework.baseObservation Framework.baseObservation
      Framework.continuous_baseObservation.measurable Framework.continuous_baseObservation.measurable
      h hcomm volume (selected_base_ac N ν₀ E₀ hden k) hJac
  have hpure (k : ℕ) (γ : Fin (W k)) (r : ℝ) :
      ∃ g : Base → ENNReal, Measurable g ∧
        (Selected (ν k γ) (E k γ)).map (Obs N k r) = BaseRef.withDensity g := by
    letI := (hbase k γ).1
    exact Framework.exists_counted_observation_density _ volume _ (measurable_Obs N k r) (hbase k γ).2
  choose g hg using hpure
  have hjoint (k : ℕ) (γ : Fin (W k)) (u : ℝ) :
      ∃ G : Joint → ENNReal, Measurable G ∧
        (Selected (ν k γ) (E k γ)).map (JointObs N k L u) = JointRef.withDensity G := by
    letI := (hbase k γ).1
    letI : SigmaFinite BaseRef := by unfold BaseRef; infer_instance
    apply Framework.exists_counted_observation_density _ BaseRef _ (measurable_JointObs N k L u)
    change (Selected (ν k γ) (E k γ)).map (Obs N k L) ≪ BaseRef
    rw [(hg k γ L).2]
    exact withDensity_absolutelyContinuous _ _
  choose G hG using hjoint
  exact ⟨g, G, (fun k γ r _ _ => hg k γ r), (fun k γ u _ _ => hG k γ u)⟩

/-- The complete affine-law and slope-ceiling interface for the endpoint crop. -/
theorem cropAffineStatement : CropAffineStatement := by
  intro N Λ₀ ν₀ E₀ L u₀ β W ω ν E p q ρ hN₂ hN hsource hL hL₁ hu hu₄
    hcrop hden hceil hΛ
  obtain ⟨g, G, hlaws⟩ := cropDensities_of_relations N ν₀ E₀ L u₀ β W ω ν E p q ρ
    hsource hcrop hden
  obtain ⟨Λ, hceiling, hgrowth⟩ := slopeCeiling_of_cropRelations N Λ₀ ν₀ E₀ u₀ β W ω ν E p q ρ
    hN₂ hN (fun k => (hsource k).1) hcrop hceil hΛ
  exact ⟨g, G, Λ, hlaws, hceiling, hgrowth⟩

end Submission.Obl.k4_dyadic_crop_affine_laws
