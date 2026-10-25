-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.CoarsePacketWitness, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/CoarsePacketWitness.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/CoarsePacketWitness.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/CoarsePacketWitness.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/CoarsePacketWitness.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePaletteTransfer

/-! The actual coarse support used by palette transfer identifies one old
packet pointwise and recovers its unchanged native velocity posterior. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PreparedAngularPath.original_total_le_one (hd : d.Valid) (hHE : ∀ w, H w ⊆ d.E k w) :
    labelledResidual (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual univ ≤ 1 := by
  rw [labelledResidual_univ]
  calc
    _ = ∑ w, ENNReal.ofReal (d.ω k w) * d.μ k w (Q.residual w) := by
      apply Finset.sum_congr rfl
      intro w _
      have heq : d.μ k w (Q.residual w) = ((d.ν k w).prod volume) (Q.residual w) :=
        d.μ_apply_eq k w (Q.residual_measurable w)
          ((Q.residual_subset w).trans ((Q.base_subset w).trans (hHE w)))
      rw [heq]
    _ ≤ ∑ w, ENNReal.ofReal (d.ω k w) * d.μ k w univ :=
      Finset.sum_le_sum (fun w _ => mul_le_mul le_rfl (measure_mono (subset_univ _)) zero_le zero_le)
    _ ≤ 1 := hd.selected_mixture_budget k

/-- A positive current old packet has one coarse code, fixed by the original
path. Its coarse law has positive source mass and is the ORIGINAL packet law. -/
theorem PreparedAngularPath.exists_packet_coarse_law (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (b : Fin p.C)
    (hω : 0 < d.ω k (p.γ b)) (hcurrent : Q.currentParentLaw b univ ≠ 0) :
    ∃ c : ℕ,
      (∀ z ∈ Q.coarseSupport (p.lev b) c, z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
      Q.law (Q.coarseSupport (p.lev b) c) ≠ 0 ∧
      (Q.coarseLaw (p.lev b) c).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ := by
  have hN : 0 < d.N k := lt_of_lt_of_le (by norm_num) (hd.1 k)
  obtain ⟨c, hc, hpost⟩ := hp.prepared_history_packet_posterior_strong hN b hω
  have htotal : labelledResidual (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual univ ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) (Q.original_total_le_one hd hHE)
  have hSupport : Q.law (labelledSupport Q.residual)ᶜ = 0 :=
    preparedResidualLaw_support (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual Q.residual_measurable
  have hSae : ∀ᵐ z ∂Q.law, z ∈ labelledSupport Q.residual := ae_iff.mpr hSupport
  have heq : Q.coarseSupport (p.lev b) c =ᵐ[Q.law]
      {z | finitePacketHistory p.lev p.γ p.F (p.lev b) z = c} := by
    filter_upwards [hSae] with z hz
    simp only [coarseSupport, mem_inter_iff, mem_ofPred_eq, hz, true_and]
  have hcond : Q.coarseLaw (p.lev b) c = ProbabilityTheory.cond Q.law
      {z | finitePacketHistory p.lev p.γ p.F (p.lev b) z = c} := by
    simp only [coarseLaw, ProbabilityTheory.cond, measure_congr heq, Measure.restrict_congr_set heq]
  have hF (a : Fin p.C) : MeasurableSet (p.F a) :=
    (hp.2.2.2.2.2.2.2 a).2.2.2.2.2.2.2.2.2.1
  have hmap : (Q.coarseLaw (p.lev b) c).map Prod.snd =
      ProbabilityTheory.cond (Q.currentParentLaw b) univ := by
    rw [hcond]
    change (ProbabilityTheory.cond
      (preparedResidualLaw (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual)
        {z | finitePacketHistory p.lev p.γ p.F (p.lev b) z = c}).map Prod.snd = _
    rw [hpost Q.residual htotal]
    exact (Q.current_parent_cond_eq_original hHE hF b).symm
  have hcurtop : Q.currentParentLaw b univ ≠ ∞ := by
    apply ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞)
    rw [currentParentLaw, Measure.restrict_apply_univ]
    exact (measure_mono (subset_univ _)).trans (hd.selected_incidence_mass_le_one k _)
  let := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hcurrent hcurtop
  have hCpos : Q.law (Q.coarseSupport (p.lev b) c) ≠ 0 := by
    intro hz
    have hzero : Q.coarseLaw (p.lev b) c = 0 := ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hz
    have hh := congrArg (fun μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) => μ univ) hmap
    rw [hzero, Measure.map_zero] at hh
    simpa using hh
  exact ⟨c, fun z hz => hc z hz.2, hCpos, hmap⟩

theorem PreparedAngularPath.coarse_velocity_posterior_eq (b : Fin p.C) (c : ℕ)
    (hmap : (Q.coarseLaw (p.lev b) c).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ) :
    (Q.coarseLaw (p.lev b) c).map (fun z => p.normalizedVelocity b z.2) = Q.velocityPosterior b := by
  change (Q.coarseLaw (p.lev b) c).map (p.normalizedVelocity b ∘ Prod.snd) = Q.velocityPosterior b
  rw [← Measure.map_map (p.measurable_normalizedVelocity b) measurable_snd, hmap]
  rfl

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
