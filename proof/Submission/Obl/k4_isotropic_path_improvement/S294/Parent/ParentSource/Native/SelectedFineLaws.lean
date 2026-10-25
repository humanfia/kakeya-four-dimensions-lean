-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.SelectedFineLaws, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/SelectedFineLaws.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/SelectedFineLaws.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/SelectedFineLaws.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeDichotomy

/-! Actual retained fine-state probability laws, their strip breadth, and
palette domination by the unchanged original coarse velocity posterior. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
  (F : PaletteFamily Q i stop a A θ)

noncomputable def PaletteFamily.fineLaw (b : Fin p.C) (e : ℕ) :
    Measure (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)) :=
  ProbabilityTheory.cond (Q.coarseLaw (p.lev b) (F.code b))
    {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U b}

noncomputable def PaletteFamily.fineVelocityLaw (b : Fin p.C) (e : ℕ) :
    Measure (EuclideanSpace ℝ (Fin 2)) :=
  (F.fineLaw b e).map (fun z => p.normalizedVelocity b z.2)

theorem PaletteFamily.broad_fine_law (hF : ∀ b, MeasurableSet (p.F b))
    (r fraction : ℝ) (hfraction : 0 ≤ fraction) (b : Fin p.C) (hb : F.active b) (e : ℕ)
    (he : e ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b)
    (hretained : e ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ))) :
    IsProbabilityMeasure (F.fineLaw b e) ∧
      ∀ (n : StripSpace) (β : ℝ), ‖n‖ = 1 →
        (F.fineLaw b e).real {z | p.normalizedVelocity b z.2 ∈ affineStrip n β r} <
          8 * fraction := by
  let : IsFiniteMeasure (Q.coarseLaw (p.lev b) (F.code b)) := by
    change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
    infer_instance
  have h := broad_selected_state_of_retention (Q.coarseLaw (p.lev b) (F.code b))
    (finitePacketHistory p.lev p.γ p.F stop) (F.U b)
    (fun e => measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF stop) measurable_const)
    (F.measurable_U b hb) (fun z => p.normalizedVelocity b z.2) r fraction (1 / 8)
    (by norm_num) hfraction e he hretained
  have heq : fraction / (1 / 8 : ℝ) = 8 * fraction := by ring
  simpa only [fineLaw, heq] using h

theorem PaletteFamily.broad_fine_velocity_law (hF : ∀ b, MeasurableSet (p.F b))
    (r fraction : ℝ) (hfraction : 0 ≤ fraction) (b : Fin p.C) (hb : F.active b) (e : ℕ)
    (he : e ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b)
    (hretained : e ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ))) :
    IsProbabilityMeasure (F.fineVelocityLaw b e) ∧
      ∀ (n : StripSpace) (β : ℝ), ‖n‖ = 1 →
        (F.fineVelocityLaw b e).real (affineStrip n β r) < 8 * fraction := by
  obtain ⟨hprob, hstrip⟩ := F.broad_fine_law hF r fraction hfraction b hb e he hretained
  let := hprob
  have hVm : Measurable (fun z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) =>
      p.normalizedVelocity b z.2) := (p.measurable_normalizedVelocity b).comp measurable_snd
  have hpmap := (Measure.isProbabilityMeasure_map_iff (μ := F.fineLaw b e) hVm.aemeasurable).mpr hprob
  refine ⟨hpmap, ?_⟩
  intro n β hn
  rw [fineVelocityLaw, map_measureReal_apply hVm (measurableSet_affineStrip n β r)]
  exact hstrip n β hn

theorem PaletteFamily.coarse_palette_eq_native (b : Fin p.C) (hb : F.active b) :
    (Q.coarseLaw (p.lev b) (F.code b)).map (p.labelledNormalizedPalette b a) =
      (Q.velocityPosterior b).map (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) := by
  have hpalm : Measurable (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) :=
    measurable_euclidean_velocityPalette id measurable_id a
  have hVm : Measurable (fun z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) =>
      p.normalizedVelocity b z.2) := (p.measurable_normalizedVelocity b).comp measurable_snd
  rw [← Q.coarse_velocity_posterior_eq b (F.code b) (F.posterior b hb)]
  exact (Measure.map_map hpalm hVm).symm

theorem PaletteFamily.fine_palette_domination (hF : ∀ b, MeasurableSet (p.F b))
    (hA : 0 ≤ A) (b : Fin p.C) (hb : F.active b) (e : ℕ)
    (hretained : e ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ))) :
    (F.fineVelocityLaw b e).map (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) ≤
      ENNReal.ofReal (8 * A) • (Q.velocityPosterior b).map (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) := by
  let : IsFiniteMeasure (Q.coarseLaw (p.lev b) (F.code b)) := by
    change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
    infer_instance
  have hVm : Measurable (fun z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) =>
      p.normalizedVelocity b z.2) := (p.measurable_normalizedVelocity b).comp measurable_snd
  have hpalm : Measurable (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) :=
    measurable_euclidean_velocityPalette id measurable_id a
  have h := retained_fine_palette_domination (Q.coarseLaw (p.lev b) (F.code b))
    (finitePacketHistory p.lev p.γ p.F stop) (F.U b)
    (fun e => measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF stop) measurable_const)
    (F.measurable_U b hb) (p.labelledNormalizedPalette b a)
    (measurable_euclidean_velocityPalette _ hVm a) hA (by norm_num : 0 < (1 / 8 : ℝ))
    e hretained (F.joint_cap b hb e)
  have hleft : (F.fineVelocityLaw b e).map (fun v : EuclideanSpace ℝ (Fin 2) => velocityPalette a v) =
      (F.fineLaw b e).map (p.labelledNormalizedPalette b a) := Measure.map_map hpalm hVm
  rw [hleft, ← F.coarse_palette_eq_native b hb]
  have heq : A / (1 / 8 : ℝ) = 8 * A := by ring
  simpa only [fineLaw, heq] using h

variable {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteFamily.fine_law_original_packet
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (b : Fin p.C) (hb : F.active b) (f : Fin p.C) (hf : p.lev f = stop)
    (hfγ : p.γ f = p.γ b) :
    ∀ᵐ z ∂F.fineLaw b (F.coding.code f), z.2 ∈ p.packetWitness m stop (p.γ f) f := by
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hcore : ∀ᵐ z ∂Q.law, z.2 ∈ F.coding.core z.1 :=
    preparedResidualLaw_original_ae (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
      F.coding.core (F.coding.measurableSet_core hF) F.coding.ae_core
  have hunique : ∀ᵐ z ∂Q.law, packetUnique p.lev p.γ p.F z.1 z.2 :=
    preparedResidualLaw_original_ae (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual
      (fun w => {z | packetUnique p.lev p.γ p.F w z})
      (measurableSet_packetUnique p.lev p.γ p.F hF) hp.ae_packet_unique
  have hac : F.fineLaw b (F.coding.code f) ≪ Q.law :=
    ProbabilityTheory.cond_absolutelyContinuous.trans ProbabilityTheory.cond_absolutelyContinuous
  have hcell : ∀ᵐ z ∂F.fineLaw b (F.coding.code f),
      finitePacketHistory p.lev p.γ p.F stop z = F.coding.code f ∧ z ∈ F.U b :=
    ProbabilityTheory.ae_cond_mem ((measurableSet_eq_fun
      (measurable_finitePacketHistory p.lev p.γ p.F hF stop) measurable_const).inter (F.measurable_U b hb))
  filter_upwards [hac.ae_le hcore, hac.ae_le hunique, hcell] with z hzcore hzunique hzcell
  have hzC := F.subset_coarse b hb hzcell.2
  have hzb := F.packet b hb z hzC
  have hfz : p.γ f = z.1 := hfγ.trans hzb.1.symm
  have hxf : z.2 ∈ p.F f := (hzcore f hfz).mp (by simpa only [hf] using hzcell.1)
  have hterminal : z.2 ∈ p.terminalCoverage m z.1 := by
    obtain ⟨t, ht, htγ, hzt⟩ := hH z.1 (Q.base_subset _ (Q.residual_subset _ hzC.1))
    exact ⟨t, ⟨ht, htγ⟩, hzt⟩
  rw [PathData.packetWitness, ite_eq_left (show p.lev f = stop ∧ p.γ f = p.γ f from ⟨hf, rfl⟩)]
  exact ⟨⟨hxf, by simpa only [hfz, mem_ofPred_eq] using hzunique⟩, by simpa only [hfz] using hterminal⟩

theorem PaletteFamily.fine_velocity_envelope
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (hb : F.active b) (e : ℕ) :
    ∀ᵐ v ∂F.fineVelocityLaw b e, ‖v‖ ≤ 2 * p.κ := by
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hVm : Measurable (fun z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) =>
      p.normalizedVelocity b z.2) := (p.measurable_normalizedVelocity b).comp measurable_snd
  apply (ae_map_iff hVm.aemeasurable (measurableSet_le measurable_norm measurable_const)).mpr
  apply ProbabilityTheory.ae_cond_of_forall_mem
    ((measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF stop) measurable_const).inter
      (F.measurable_U b hb))
  intro z hz
  have hzb := (F.packet b hb z (F.subset_coarse b hb hz.2)).2
  have hAz := (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.2.2.2.1 z.2 hzb
  exact hp.normalized_velocity_bound b z.2.1 hAz.2.1

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
