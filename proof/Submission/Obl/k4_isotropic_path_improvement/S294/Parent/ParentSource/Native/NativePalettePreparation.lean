-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativePalettePreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativePalettePreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativePalettePreparation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativePalettePreparation.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativePalettePreparation.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.CoarseEventTransfer
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeConditionalOmissions

/-! Simultaneous actual normalized-palette omissions at one level. All
conditional costs refer to the same original current-parent posteriors,
and their uniform fraction sums under the single prepared law. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

def PreparedAngularPath.normalizedPaletteOmission (b : Fin p.C) (stop c : ℕ)
    (a₀ a₁ R ε : ℝ) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  Prod.mk (p.γ b) ⁻¹'
    ((likelihoodGood Q.law (labelledSupport Q.residual) (finitePacketHistory p.lev p.γ p.F)
      (labelledVelocityPalette a₀) (p.lev b) stop R ∩ Q.coarseSupport (p.lev b) c) \
        Q.normalizedPaletteCut b (p.lev b) stop c a₀ a₁ R ε)

noncomputable def PreparedAngularPath.paletteOmissionFamily (code : Fin p.C → ℕ)
    (i stop : ℕ) (a₀ a₁ R ε : ℝ) (b : Fin p.C) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := by
  classical
  exact if p.lev b = i ∧ 0 < d.ω k (p.γ b) ∧ Q.currentParentLaw b univ ≠ 0 then
    Q.normalizedPaletteOmission b stop (code b) a₀ a₁ R ε else ∅

theorem PreparedAngularPath.prepare_normalized_palette_level (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m) (stop : ℕ) (hst : i ≤ stop)
    {a₀ a₁ ε R : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hε : 0 < ε) (hR : 0 ≤ R)
    (hmesh : a₀ * d.N k ^ (2 * δ₀ * d.L) ≤ a₁) (K : ℕ) (hK : (4 * p.κ + 6) ^ 2 ≤ (K : ℝ)) :
    ∃ code : Fin p.C → ℕ,
      (∀ b, p.lev b = i → 0 < d.ω k (p.γ b) → Q.currentParentLaw b univ ≠ 0 →
        (∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
        Q.law (Q.coarseSupport (p.lev b) (code b)) ≠ 0 ∧
        (Q.coarseLaw (p.lev b) (code b)).map Prod.snd =
          ProbabilityTheory.cond (Q.currentParentLaw b) univ) ∧
      (∀ b, MeasurableSet (Q.paletteOmissionFamily code i stop a₀ a₁ R ε b)) ∧
      (∀ b, Q.paletteOmissionFamily code i stop a₀ a₁ R ε b ⊆ Q.residual (p.γ b) ∩ p.F b) ∧
      (∀ b, p.lev b = i → ProbabilityTheory.cond (Q.currentParentLaw b) univ
        (Q.paletteOmissionFamily code i stop a₀ a₁ R ε b) ≤ ENNReal.ofReal (ε * K)) ∧
      Q.law (labelledSupport (Q.packetFamilyResidual i (Q.paletteOmissionFamily code i stop a₀ a₁ R ε))) ≤
        ENNReal.ofReal (ε * K) := by
  classical
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  let := Q.probability hd hHE hκ
  let Active : Fin p.C → Prop := fun b =>
    p.lev b = i ∧ 0 < d.ω k (p.γ b) ∧ Q.currentParentLaw b univ ≠ 0
  have hex (b : Fin p.C) : ∃ c, Active b →
      (∀ z ∈ Q.coarseSupport (p.lev b) c, z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
      Q.law (Q.coarseSupport (p.lev b) c) ≠ 0 ∧
      (Q.coarseLaw (p.lev b) c).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ := by
    by_cases hb : Active b <;> dsimp only [Active] at hb
    · obtain ⟨c, hc⟩ := Q.exists_packet_coarse_law hd hp hHE b hb.2.1 hb.2.2
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => False.elim (hb h)⟩
  choose code hcode using hex
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hS := measurableSet_labelledSupport Q.residual Q.residual_measurable
  have hZ : Measurable (labelledVelocityPalette (W := d.W k) a₀) :=
    measurable_euclidean_velocityPalette _
      (Submission.Obl.k4_dk4_smoothed_problem.Framework.continuous_planarVelocity.measurable.comp
        (measurable_fst.comp measurable_snd)) a₀
  have hdata (b : Fin p.C) (hb : Active b) :
      MeasurableSet (Q.normalizedPaletteOmission b stop (code b) a₀ a₁ R ε) ∧
      Q.normalizedPaletteOmission b stop (code b) a₀ a₁ R ε ⊆ Q.residual (p.γ b) ∩ p.F b ∧
      ProbabilityTheory.cond (Q.currentParentLaw b) univ
        (Q.normalizedPaletteOmission b stop (code b) a₀ a₁ R ε) ≤ ENNReal.ofReal (ε * K) := by
    obtain ⟨hPacket, hCpos, hmap⟩ := hcode b hb
    obtain ⟨hCut, _, hreal, _⟩ := Q.normalized_palette_transfer hd hp hHE b (p.lev b) stop (code b)
      (by simpa only [hb.1] using hst) hCpos ha₀ ha₁ hε hR hmesh K hK
    have hC : MeasurableSet (Q.coarseSupport (p.lev b) (code b)) :=
      hS.inter (measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF _) measurable_const)
    have hG := measurableSet_likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) (p.lev b) stop R hS
      (measurable_finitePacketHistory p.lev p.γ p.F hF _)
      (measurable_finitePacketHistory p.lev p.γ p.F hF _) hZ
    let D := (likelihoodGood Q.law (labelledSupport Q.residual) (finitePacketHistory p.lev p.γ p.F)
      (labelledVelocityPalette a₀) (p.lev b) stop R ∩ Q.coarseSupport (p.lev b) (code b)) \
        Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε
    have hD : MeasurableSet D := (hG.inter hC).diff hCut
    have hDC : D ⊆ Q.coarseSupport (p.lev b) (code b) := sdiff_subset.trans inter_subset_right
    have ht := Q.coarse_event_to_native b (code b) hC hPacket hmap D hD hDC
    let : IsProbabilityMeasure (Q.coarseLaw (p.lev b) (code b)) :=
      ProbabilityTheory.cond_isProbabilityMeasure (μ := Q.law) hCpos
    have hmass : Q.coarseLaw (p.lev b) (code b) D ≤ ENNReal.ofReal (ε * K) := by
      calc
        _ = ENNReal.ofReal ((Q.coarseLaw (p.lev b) (code b)).real D) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
    exact ⟨ht.1, ht.2.1, ht.2.2.trans_le hmass⟩
  let D := Q.paletteOmissionFamily code i stop a₀ a₁ R ε
  have hmeas (b : Fin p.C) : MeasurableSet (D b) := by
    by_cases hb : Active b <;> dsimp only [Active] at hb
    · simpa only [D, paletteOmissionFamily, ite_eq_left hb] using (hdata b hb).1
    · simpa only [D, paletteOmissionFamily, ite_eq_right hb] using MeasurableSet.empty
  have hsub (b : Fin p.C) : D b ⊆ Q.residual (p.γ b) ∩ p.F b := by
    by_cases hb : Active b <;> dsimp only [Active] at hb
    · simpa only [D, paletteOmissionFamily, ite_eq_left hb] using (hdata b hb).2.1
    · simp only [D, paletteOmissionFamily, ite_eq_right hb]
      exact empty_subset _
  have hcap (b : Fin p.C) (_ : p.lev b = i) :
      ProbabilityTheory.cond (Q.currentParentLaw b) univ (D b) ≤ ENNReal.ofReal (ε * K) := by
    by_cases hb : Active b <;> dsimp only [Active] at hb
    · simpa only [D, paletteOmissionFamily, ite_eq_left hb] using (hdata b hb).2.2
    · simp only [D, paletteOmissionFamily, ite_eq_right hb, measure_empty]
      exact zero_le
  refine ⟨code, (fun b hbi hω hcur => hcode b ⟨hbi, hω, hcur⟩), hmeas, hsub, hcap, ?_⟩
  exact Q.conditional_omission_prepared_mass_le hd hp hHE hH i hi D hmeas hsub
    (ENNReal.ofReal (ε * K)) hcap

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
