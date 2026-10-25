-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeNarrowFamilies, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeNarrowFamilies.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeNarrowFamilies.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeNarrowFamilies.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeNarrowFamilies.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFamilyMass
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.CoarseEventTransfer
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripStateMass

/-! Actual narrow fine states retain their stated fraction of original bad
state mass. This produces the native residual used by the two-scale atlas;
all posterior denominators and original priors remain fixed. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators

/-- Null countable state fibers form one null exceptional set, fixed before
all later selections. No atomicity of the original source law is assumed. -/
theorem ae_countable_state_mass_ne_zero {Ω Z : Type*} [MeasurableSpace Ω] [Countable Z]
    (μ : Measure Ω) (f : Ω → Z) : ∀ᵐ x ∂μ, μ {y | f y = f x} ≠ 0 := by
  have havoid : ∀ z, ∀ᵐ x ∂μ, μ {y | f y = z} = 0 → f x ≠ z := by
    intro z
    by_cases hz : μ {y | f y = z} = 0
    · have ha : ∀ᵐ x ∂μ, f x ≠ z := ae_iff.mpr (by simpa only [not_not] using hz)
      exact ha.mono (fun _ hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hz h))
  have hall := ae_all_iff.mpr havoid
  filter_upwards [hall] with x hx
  intro hz
  exact hx (f x) hz rfl

theorem ae_countable_state_real_mass_pos {Ω Z : Type*} [MeasurableSpace Ω] [Countable Z]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → Z) :
    ∀ᵐ x ∂μ, 0 < μ.real {y | f y = f x} := by
  filter_upwards [ae_countable_state_mass_ne_zero μ f] with x hx
  exact ENNReal.toReal_pos hx (measure_ne_top _ _)

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

noncomputable def PreparedAngularPath.badHistoryFamily (active : Fin p.C → Prop)
    (code : Fin p.C → ℕ) (stop : ℕ) (Bad : Fin p.C → Set ℕ) (b : Fin p.C) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := by
  classical
  exact if active b then Prod.mk (p.γ b) ⁻¹'
    (Q.coarseSupport (p.lev b) (code b) ∩ finitePacketHistory p.lev p.γ p.F stop ⁻¹' Bad b) else ∅

noncomputable def PreparedAngularPath.narrowHistoryFamily (_Q : PreparedAngularPath d k p m H u τ)
    (active : Fin p.C → Prop) (stop : ℕ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (n : Fin p.C → ℕ → StripSpace) (β : Fin p.C → ℕ → ℝ)
    (r : ℝ) (Bad : Fin p.C → Set ℕ) (b : Fin p.C) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := by
  classical
  exact if active b then Prod.mk (p.γ b) ⁻¹'
    narrowStateUnion (finitePacketHistory p.lev p.γ p.F stop) (U b)
      (fun z => p.normalizedVelocity b z.2) (n b) (β b) r (Bad b) else ∅

theorem PreparedAngularPath.narrow_history_family_mass (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (i stop : ℕ) (active : Fin p.C → Prop)
    (code : Fin p.C → ℕ)
    (hcode : ∀ b, active b →
      (∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
      (Q.coarseLaw (p.lev b) (code b)).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (hU : ∀ b, active b → MeasurableSet (U b))
    (hUC : ∀ b, active b → U b ⊆ Q.coarseSupport (p.lev b) (code b))
    (n : Fin p.C → ℕ → StripSpace) (β : Fin p.C → ℕ → ℝ)
    (r : ℝ) (Bad : Fin p.C → Set ℕ) (θ : ENNReal)
    (hfloor : ∀ b, active b → ∀ e ∈ Bad b,
      θ * Q.coarseLaw (p.lev b) (code b) {z | finitePacketHistory p.lev p.γ p.F stop z = e} ≤
        Q.coarseLaw (p.lev b) (code b) {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧
          z ∈ U b ∧ p.normalizedVelocity b z.2 ∈ affineStrip (n b e) (β b e) r}) :
    (∀ b, MeasurableSet (Q.badHistoryFamily active code stop Bad b)) ∧
      (∀ b, MeasurableSet (Q.narrowHistoryFamily active stop U n β r Bad b)) ∧
      (∀ b, Q.badHistoryFamily active code stop Bad b ⊆ Q.residual (p.γ b) ∩ p.F b) ∧
      (∀ b, Q.narrowHistoryFamily active stop U n β r Bad b ⊆ Q.residual (p.γ b) ∩ p.F b) ∧
      θ * Q.law (labelledSupport (Q.packetFamilyResidual i (Q.badHistoryFamily active code stop Bad))) ≤
        Q.law (labelledSupport (Q.packetFamilyResidual i (Q.narrowHistoryFamily active stop U n β r Bad))) := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hS := measurableSet_labelledSupport Q.residual Q.residual_measurable
  have hhist := measurable_finitePacketHistory p.lev p.γ p.F hF stop
  have hdata (b : Fin p.C) (hb : active b) :
      MeasurableSet (Q.badHistoryFamily active code stop Bad b) ∧
      MeasurableSet (Q.narrowHistoryFamily active stop U n β r Bad b) ∧
      Q.badHistoryFamily active code stop Bad b ⊆ Q.residual (p.γ b) ∩ p.F b ∧
      Q.narrowHistoryFamily active stop U n β r Bad b ⊆ Q.residual (p.γ b) ∩ p.F b ∧
      θ * ProbabilityTheory.cond (Q.currentParentLaw b) univ (Q.badHistoryFamily active code stop Bad b) ≤
        ProbabilityTheory.cond (Q.currentParentLaw b) univ (Q.narrowHistoryFamily active stop U n β r Bad b) := by
    obtain ⟨hPacket, hmap⟩ := hcode b hb
    have hC : MeasurableSet (Q.coarseSupport (p.lev b) (code b)) :=
      hS.inter (measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF _) measurable_const)
    let A := Q.coarseSupport (p.lev b) (code b) ∩ finitePacketHistory p.lev p.γ p.F stop ⁻¹' Bad b
    let J := narrowStateUnion (finitePacketHistory p.lev p.γ p.F stop) (U b)
      (fun z => p.normalizedVelocity b z.2) (n b) (β b) r (Bad b)
    have hA : MeasurableSet A := hC.inter (hhist ((Set.to_countable (Bad b)).measurableSet))
    have hJ : MeasurableSet J := measurableSet_narrowStateUnion _ hhist _ (hU b hb) _
      ((p.measurable_normalizedVelocity b).comp measurable_snd) _ _ _ _
    have hAC : A ⊆ Q.coarseSupport (p.lev b) (code b) := inter_subset_left
    have hJC : J ⊆ Q.coarseSupport (p.lev b) (code b) :=
      (narrowStateUnion_subset _ _ _ _ _ _ _).trans (hUC b hb)
    have hpa := Q.coarse_event_to_native b (code b) hC hPacket hmap A hA hAC
    have hpj := Q.coarse_event_to_native b (code b) hC hPacket hmap J hJ hJC
    have hAmass : Q.coarseLaw (p.lev b) (code b) A = Q.coarseLaw (p.lev b) (code b)
        (finitePacketHistory p.lev p.γ p.F stop ⁻¹' Bad b) :=
      ProbabilityTheory.cond_inter_self hC _ Q.law
    have hrel : θ * ProbabilityTheory.cond (Q.currentParentLaw b) univ (Prod.mk (p.γ b) ⁻¹' A) ≤
        ProbabilityTheory.cond (Q.currentParentLaw b) univ (Prod.mk (p.γ b) ⁻¹' J) := by
      rw [hpa.2.2, hpj.2.2, hAmass]
      exact narrowStateUnion_mass _ _ hhist _ (hU b hb) _
        ((p.measurable_normalizedVelocity b).comp measurable_snd) _ _ _ _ θ (hfloor b hb)
    simpa only [badHistoryFamily, narrowHistoryFamily, ite_eq_left hb] using
      (show MeasurableSet (Prod.mk (p.γ b) ⁻¹' A) ∧ MeasurableSet (Prod.mk (p.γ b) ⁻¹' J) ∧
        Prod.mk (p.γ b) ⁻¹' A ⊆ Q.residual (p.γ b) ∩ p.F b ∧
        Prod.mk (p.γ b) ⁻¹' J ⊆ Q.residual (p.γ b) ∩ p.F b ∧
        θ * ProbabilityTheory.cond (Q.currentParentLaw b) univ (Prod.mk (p.γ b) ⁻¹' A) ≤
          ProbabilityTheory.cond (Q.currentParentLaw b) univ (Prod.mk (p.γ b) ⁻¹' J) from
          ⟨hpa.1, hpj.1, hpa.2.1, hpj.2.1, hrel⟩)
  have hAm (b : Fin p.C) : MeasurableSet (Q.badHistoryFamily active code stop Bad b) := by
    by_cases hb : active b
    · exact (hdata b hb).1
    · simp only [badHistoryFamily, ite_eq_right hb]
      exact MeasurableSet.empty
  have hJm (b : Fin p.C) : MeasurableSet (Q.narrowHistoryFamily active stop U n β r Bad b) := by
    by_cases hb : active b
    · exact (hdata b hb).2.1
    · simp only [narrowHistoryFamily, ite_eq_right hb]
      exact MeasurableSet.empty
  have hAs (b : Fin p.C) : Q.badHistoryFamily active code stop Bad b ⊆ Q.residual (p.γ b) ∩ p.F b := by
    by_cases hb : active b
    · exact (hdata b hb).2.2.1
    · simp only [badHistoryFamily, ite_eq_right hb]
      exact empty_subset _
  have hJs (b : Fin p.C) : Q.narrowHistoryFamily active stop U n β r Bad b ⊆ Q.residual (p.γ b) ∩ p.F b := by
    by_cases hb : active b
    · exact (hdata b hb).2.2.2.1
    · simp only [narrowHistoryFamily, ite_eq_right hb]
      exact empty_subset _
  have hrel (b : Fin p.C) (_ : p.lev b = i) :
      θ * ProbabilityTheory.cond (Q.currentParentLaw b) univ (Q.badHistoryFamily active code stop Bad b) ≤
        ProbabilityTheory.cond (Q.currentParentLaw b) univ (Q.narrowHistoryFamily active stop U n β r Bad b) := by
    by_cases hb : active b
    · exact (hdata b hb).2.2.2.2
    · simp only [badHistoryFamily, narrowHistoryFamily, ite_eq_right hb, measure_empty, mul_zero]
      exact le_rfl
  exact ⟨hAm, hJm, hAs, hJs, Q.relative_family_prepared_mass_le hd hp hHE i _ _ hAm hJm hAs hJs θ hrel⟩

/-- A substantial original bad-state family supplies an actual original-law
residual covered pointwise by the predicted strips. Analytic selections are
used only to recover its mass, not to define the eventual chart predicates. -/
theorem PreparedAngularPath.narrow_residual_original_floor (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (i stop : ℕ) (active : Fin p.C → Prop)
    (code : Fin p.C → ℕ)
    (hcode : ∀ b, active b →
      (∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
      (Q.coarseLaw (p.lev b) (code b)).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (hU : ∀ b, active b → MeasurableSet (U b))
    (hUC : ∀ b, active b → U b ⊆ Q.coarseSupport (p.lev b) (code b))
    (n : Fin p.C → ℕ → StripSpace) (β : Fin p.C → ℕ → ℝ)
    (r : ℝ) (Bad : Fin p.C → Set ℕ) {fraction mass : ℝ} (hfraction : 0 ≤ fraction)
    (hfloor : ∀ b, active b → ∀ e ∈ Bad b,
      ENNReal.ofReal fraction * Q.coarseLaw (p.lev b) (code b) {z | finitePacketHistory p.lev p.γ p.F stop z = e} ≤
        Q.coarseLaw (p.lev b) (code b) {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧
          z ∈ U b ∧ p.normalizedVelocity b z.2 ∈ affineStrip (n b e) (β b e) r})
    (hmass : ENNReal.ofReal mass ≤
      Q.law (labelledSupport (Q.packetFamilyResidual i (Q.badHistoryFamily active code stop Bad)))) :
    let J := Q.packetFamilyResidual i (Q.narrowHistoryFamily active stop U n β r Bad)
    (∀ w, MeasurableSet (J w)) ∧ (∀ w, J w ⊆ H w) ∧
      ENNReal.ofReal ((p.κ⁻¹ / 8) * (fraction * mass)) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (J w) ∧
      ∀ w x, x ∈ J w → ∃ b, p.lev b = i ∧ p.γ b = w ∧ x ∈ p.F b ∧
        ∃ e ∈ Bad b, active b ∧ p.normalizedVelocity b x ∈ affineStrip (n b e) (β b e) r := by
  classical
  obtain ⟨_, hJm, _, hJs, hrel⟩ := Q.narrow_history_family_mass hd hp hHE i stop active code hcode
    U hU hUC n β r Bad (ENNReal.ofReal fraction) hfloor
  have hkeep : ENNReal.ofReal (fraction * mass) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.narrowHistoryFamily active stop U n β r Bad))) := by
    calc
      _ = ENNReal.ofReal fraction * ENNReal.ofReal mass := ENNReal.ofReal_mul hfraction
      _ ≤ ENNReal.ofReal fraction * Q.law
          (labelledSupport (Q.packetFamilyResidual i (Q.badHistoryFamily active code stop Bad))) :=
        mul_le_mul le_rfl hmass zero_le zero_le
      _ ≤ _ := hrel
  refine ⟨Q.measurableSet_packetFamilyResidual i _ hJm, ?_,
    Q.original_floor_of_prepared_family hd hp hHE i _ hJm hJs hkeep, ?_⟩
  · intro w
    exact (Q.packetFamilyResidual_subset i _ hJs w).trans
      ((Q.residual_subset w).trans (Q.base_subset w))
  · intro w x hx
    obtain ⟨b, hbi, hbw, hxb⟩ := hx
    have hFb : x ∈ p.F b := (hJs b hxb).2
    by_cases hb : active b
    · have hxLabel : (p.γ b, x) ∈ narrowStateUnion
          (finitePacketHistory p.lev p.γ p.F stop) (U b)
          (fun z => p.normalizedVelocity b z.2) (n b) (β b) r (Bad b) := by
        simpa only [narrowHistoryFamily, ite_eq_left hb, mem_preimage] using hxb
      obtain ⟨e, he⟩ := mem_iUnion.mp hxLabel
      exact ⟨b, hbi, hbw, hFb, e.val, e.property, hb, he.2.2⟩
    · simp only [narrowHistoryFamily, ite_eq_right hb, mem_empty_iff_false] at hxb

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
