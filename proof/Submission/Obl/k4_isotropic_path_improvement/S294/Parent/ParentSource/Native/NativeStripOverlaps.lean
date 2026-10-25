-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeStripOverlaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeStripOverlaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeStripOverlaps.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeStripOverlaps.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeStripOverlaps.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeConditionalOmissions
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NormalizedPosteriors
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripFarOverlaps

/-! The two-scale strip-overlap deletion is charged to the same fixed native
parent posterior and then to the single original prepared law. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

noncomputable def PreparedAngularPath.stripOverlapOmissions {ι : Fin p.C → Type*}
    (active : Fin p.C → Prop) (n : (b : Fin p.C) → ι b → StripSpace)
    (β : (b : Fin p.C) → ι b → ℝ) (w ρ T₀ : ℝ) (b : Fin p.C) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := by
  classical
  exact if active b then (Q.residual (p.γ b) ∩ p.F b) ∩
    p.normalizedVelocity b ⁻¹' stripFarOverlap (n b) (β b) w ρ T₀ else ∅

/-- Exact fixed-native-posterior overlap cost, before summing parents. -/
theorem PreparedAngularPath.strip_overlap_conditional_mass_le {ι : Fin p.C → Type*}
    [∀ b, Fintype (ι b)]
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (active : Fin p.C → Prop)
    (n : (b : Fin p.C) → ι b → StripSpace) (β : (b : Fin p.C) → ι b → ℝ)
    {w ρ T₀ ε : ℝ} (hT : 0 ≤ T₀) (hρ : 0 < ρ) (hsmall : 4 * w ≤ ρ)
    (hn : ∀ b, active b → ∀ j, ‖n b j‖ = 1)
    (hcap : ∀ b, active b → ∀ x : StripSpace,
      Q.velocityPosterior b (Metric.closedBall x (32 * (1 + T₀) * w / ρ)) ≤ ENNReal.ofReal ε)
    (M : ℕ) (hM : ∀ b, active b → Fintype.card (ι b) ≤ M) (b : Fin p.C) :
    ProbabilityTheory.cond (Q.currentParentLaw b) univ
      (Q.stripOverlapOmissions active n β w ρ T₀ b) ≤ (M : ENNReal) ^ 2 * ENNReal.ofReal ε := by
  classical
  by_cases hb : active b
  · let O := stripFarOverlap (n b) (β b) w ρ T₀
    have hO : MeasurableSet O := measurableSet_stripFarOverlap _ _ _ _ _
    have hF : MeasurableSet (p.F b) := (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
    have hidentity : ProbabilityTheory.cond (Q.currentParentLaw b) univ
        (Q.stripOverlapOmissions active n β w ρ T₀ b) = Q.velocityPosterior b O := by
      change _ = ((ProbabilityTheory.cond (Q.currentParentLaw b) univ).map (p.normalizedVelocity b)) O
      rw [Measure.map_apply (p.measurable_normalizedVelocity b) hO]
      rw [stripOverlapOmissions, ite_eq_left hb, Q.current_parent_cond_eq_original hHE (fun b =>
        (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1) b]
      exact ProbabilityTheory.cond_inter_self
        ((Q.residual_measurable _).inter hF) _ ((d.ν k (p.γ b)).prod volume)
    rw [hidentity]
    calc
      _ ≤ (Fintype.card (ι b) : ENNReal) ^ 2 * ENNReal.ofReal ε :=
        stripFarOverlap_mass_le (Q.velocityPosterior b) (n b) (β b)
          (hn b hb) hT hρ hsmall (hcap b hb)
      _ ≤ _ := by
        gcongr
        exact_mod_cast hM b hb
  · simp only [stripOverlapOmissions, ite_eq_right hb, measure_empty]
    exact zero_le

theorem PreparedAngularPath.strip_overlap_prepared_mass_le {ι : Fin p.C → Type*}
    [∀ b, Fintype (ι b)] (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m) (active : Fin p.C → Prop)
    (n : (b : Fin p.C) → ι b → StripSpace) (β : (b : Fin p.C) → ι b → ℝ)
    {w ρ T₀ ε : ℝ} (hT : 0 ≤ T₀) (hρ : 0 < ρ) (hsmall : 4 * w ≤ ρ)
    (hn : ∀ b, active b → ∀ j, ‖n b j‖ = 1)
    (hcap : ∀ b, active b → ∀ x : StripSpace,
      Q.velocityPosterior b (Metric.closedBall x (32 * (1 + T₀) * w / ρ)) ≤ ENNReal.ofReal ε)
    (M : ℕ) (hM : ∀ b, active b → Fintype.card (ι b) ≤ M) :
    (∀ b, MeasurableSet (Q.stripOverlapOmissions active n β w ρ T₀ b)) ∧
      (∀ b, Q.stripOverlapOmissions active n β w ρ T₀ b ⊆ Q.residual (p.γ b) ∩ p.F b) ∧
      Q.law (labelledSupport (Q.packetFamilyResidual i (Q.stripOverlapOmissions active n β w ρ T₀))) ≤
        (M : ENNReal) ^ 2 * ENNReal.ofReal ε := by
  classical
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  let D := Q.stripOverlapOmissions active n β w ρ T₀
  have hmeas (b : Fin p.C) : MeasurableSet (D b) := by
    dsimp only [D, stripOverlapOmissions]
    split
    · exact ((Q.residual_measurable _).inter (hF b)).inter
        ((measurableSet_stripFarOverlap _ _ _ _ _).preimage (p.measurable_normalizedVelocity b))
    · exact MeasurableSet.empty
  have hsub (b : Fin p.C) : D b ⊆ Q.residual (p.γ b) ∩ p.F b := by
    dsimp only [D, stripOverlapOmissions]
    split
    · exact inter_subset_left
    · exact empty_subset _
  have hlocal (b : Fin p.C) (_ : p.lev b = i) :
      ProbabilityTheory.cond (Q.currentParentLaw b) univ (D b) ≤
        (M : ENNReal) ^ 2 * ENNReal.ofReal ε :=
    Q.strip_overlap_conditional_mass_le hp hHE active n β hT hρ hsmall hn hcap M hM b
  exact ⟨hmeas, hsub, Q.conditional_omission_prepared_mass_le hd hp hHE hH i hi D hmeas hsub
    ((M : ENNReal) ^ 2 * ENNReal.ofReal ε) hlocal⟩

/-- The same overlap cost is valid under the ORIGINAL weighted source law.
The single prepared total is bounded by one; no new denominator is used. -/
theorem PreparedAngularPath.strip_overlap_original_mass_le {ι : Fin p.C → Type*}
    [∀ b, Fintype (ι b)] (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m) (active : Fin p.C → Prop)
    (n : (b : Fin p.C) → ι b → StripSpace) (β : (b : Fin p.C) → ι b → ℝ)
    {w ρ T₀ ε : ℝ} (hT : 0 ≤ T₀) (hρ : 0 < ρ) (hsmall : 4 * w ≤ ρ)
    (hn : ∀ b, active b → ∀ j, ‖n b j‖ = 1)
    (hcap : ∀ b, active b → ∀ x : StripSpace,
      Q.velocityPosterior b (Metric.closedBall x (32 * (1 + T₀) * w / ρ)) ≤ ENNReal.ofReal ε)
    (M : ℕ) (hM : ∀ b, active b → Fintype.card (ι b) ≤ M) :
    (∑ γ, ENNReal.ofReal (d.ω k γ) * ((d.ν k γ).prod volume)
      (Q.packetFamilyResidual i (Q.stripOverlapOmissions active n β w ρ T₀) γ)) ≤
        (M : ENNReal) ^ 2 * ENNReal.ofReal ε := by
  obtain ⟨hD, hsub, _⟩ := Q.strip_overlap_prepared_mass_le hd hp hHE hH i hi
    active n β hT hρ hsmall hn hcap M hM
  have hlocal (b : Fin p.C) (_ : p.lev b = i) :=
    Q.strip_overlap_conditional_mass_le hp hHE active n β hT hρ hsmall hn hcap M hM b
  have hbound := Q.conditional_omission_original_mass_le hd hp hHE hH i hi _ hD hsub _ hlocal
  exact hbound.trans (by
    simpa only [mul_one] using
      mul_le_mul le_rfl (Q.original_total_le_one hd hHE) zero_le zero_le)

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
