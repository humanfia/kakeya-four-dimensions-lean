-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.SelectedPaletteFamily, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/SelectedPaletteFamily.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/SelectedPaletteFamily.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/SelectedPaletteFamily.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PacketCoverage
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.OriginalDeletion
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePalettePreparation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeLightParents
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeBroadResidual

/-! The actual normalized-palette cuts form a substantial family under the
single prepared law. No positive selected-family mass is assumed. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

def PreparedAngularPath.paletteActive (i : ℕ) (θ : ENNReal) (b : Fin p.C) : Prop :=
  p.lev b = i ∧ 0 < d.ω k (p.γ b) ∧ Q.currentParentLaw b univ ≠ 0 ∧
    b ∉ Q.lightParents i θ

/-- Likelihood, light-parent and palette omissions are paid once under the
same law. The retained family has at least half of that law's original mass,
and its caps use the unchanged coarse and fine reference denominators. -/
theorem PreparedAngularPath.exists_selected_palette_family_with_loss (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (q : PacketCoding p (d.ν k)) (i : ℕ) (hi : i < m) (stop : ℕ) (hst : i ≤ stop)
    {a₀ a₁ ε R α : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hε : 0 < ε) (hR : 0 ≤ R)
    (hmesh : a₀ * d.N k ^ (2 * δ₀ * d.L) ≤ a₁) (K : ℕ) (hK : (4 * p.κ + 6) ^ 2 ≤ (K : ℝ))
    (θ : ENNReal)
    (hbad : Q.law (labelledSupport Q.residual \ likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R) ≤ ENNReal.ofReal α)
    (loss : ENNReal)
    (hbudget : ENNReal.ofReal α + (θ * ENNReal.ofReal (8 * p.κ) + ENNReal.ofReal (ε * K)) ≤
      loss) :
    ∃ code : Fin p.C → ℕ,
      (∀ b, Q.paletteActive i θ b →
        (∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
        Q.law (Q.coarseSupport (p.lev b) (code b)) ≠ 0 ∧
        (Q.coarseLaw (p.lev b) (code b)).map Prod.snd =
          ProbabilityTheory.cond (Q.currentParentLaw b) univ) ∧
      (∀ b, Q.paletteActive i θ b →
        MeasurableSet (Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε) ∧
        Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε ⊆
          Q.coarseSupport (p.lev b) (code b) ∧
        θ * d.pathAngularReference k p Q.base Q.mask b univ ≤ Q.currentParentLaw b univ ∧
        ∀ e a, (Q.coarseLaw (p.lev b) (code b)).real
          {z | z ∈ Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε ∧
            finitePacketHistory p.lev p.γ p.F stop z = e ∧ p.labelledNormalizedPalette b a₁ z = a} ≤
          (R / ε) * (Q.coarseLaw (p.lev b) (code b)).real
            {z | finitePacketHistory p.lev p.γ p.F stop z = e} *
            (Q.coarseLaw (p.lev b) (code b)).real {z | p.labelledNormalizedPalette b a₁ z = a}) ∧
      1 - loss ≤ Q.law (labelledSupport (Q.packetFamilyResidual i
        (Q.selectedCoarseFamily (Q.paletteActive i θ)
          (fun b => Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε)))) := by
  classical
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  let := Q.probability hd hHE hκ
  obtain ⟨code, hcode, hOmeas, _, _, hOmit⟩ := Q.prepare_normalized_palette_level hd hp hHE hH
    i hi stop hst ha₀ ha₁ hε hR hmesh K hK
  let U := fun b => Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε
  have hactivecode (b : Fin p.C) (hb : Q.paletteActive i θ b) :=
    hcode b hb.1 hb.2.1 hb.2.2.1
  have hdata (b : Fin p.C) (hb : Q.paletteActive i θ b) :=
    Q.normalized_palette_transfer hd hp hHE b (p.lev b) stop (code b)
      (by simpa only [hb.1] using hst) (hactivecode b hb).2.1 ha₀ ha₁ hε hR hmesh K hK
  refine ⟨code, hactivecode, ?_, ?_⟩
  · intro b hb
    have hbdata := hdata b hb
    exact ⟨hbdata.1, fun z hz => (hbdata.2.1 hz).2,
      Q.nonlight_parent_floor i θ b hb.1 hb.2.2.2, hbdata.2.2.2⟩
  · let S := labelledSupport Q.residual
    let G := likelihoodGood Q.law S (finitePacketHistory p.lev p.γ p.F)
      (labelledVelocityPalette a₀) i stop R
    let Light := labelledSupport (Q.lightParentResidual i θ)
    let Pal := labelledSupport (Q.packetFamilyResidual i (Q.paletteOmissionFamily code i stop a₀ a₁ R ε))
    let Bad := (S \ G) ∪ (Light ∪ Pal)
    let Full := labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily (Q.paletteActive i θ) U))
    have hLight := Q.light_parent_prepared_mass_le hd hp hHE i θ
    have hBad : Q.law Bad ≤ loss := calc
      _ ≤ Q.law (S \ G) + (Q.law Light + Q.law Pal) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ ENNReal.ofReal α + (θ * ENNReal.ofReal (8 * p.κ) + ENNReal.ofReal (ε * K)) :=
        add_le_add hbad (add_le_add hLight hOmit)
      _ ≤ _ := hbudget
    have hSmeas : MeasurableSet S := measurableSet_labelledSupport Q.residual Q.residual_measurable
    have hSnull : Q.law Sᶜ = 0 := preparedResidualLaw_support
      (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual Q.residual_measurable
    have hSmass : Q.law S = 1 := by
      simpa only [hSnull, add_zero, measure_univ] using measure_add_measure_compl (μ := Q.law) hSmeas
    have hkeep : 1 - loss ≤ Q.law (S \ Bad) := by
      apply tsub_le_iff_right.mpr
      calc
        1 = Q.law S := hSmass.symm
        _ ≤ Q.law (S \ Bad) + Q.law Bad := by
          have h := mixture_le_sdiff_add (fun _ : Unit => Q.law) (fun _ => 1)
            (fun _ => S) (fun _ => Bad)
          simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using h
        _ ≤ Q.law (S \ Bad) + loss := add_le_add le_rfl hBad
    have hcover := Q.ae_current_coarse_coverage hd hp hHE hH q i hi code
      (fun b hbi hω hcur => ⟨(hcode b hbi hω hcur).1, (hcode b hbi hω hcur).2.1⟩)
    have hsubset : S \ Bad ≤ᵐ[Q.law] Full := by
      filter_upwards [hcover] with z hz hzkeep
      obtain ⟨b, hbi, hbγ, hzb, hω, hcur, hzcode⟩ := hz
      have hzG : z ∈ G := by
        by_contra hn
        exact hzkeep.2 (Or.inl ⟨hzkeep.1, hn⟩)
      have hnonlight : b ∉ Q.lightParents i θ := by
        intro hb
        apply hzkeep.2
        exact Or.inr (Or.inl ⟨b, hb, hbγ, by simpa only [hbγ] using ⟨hzkeep.1, hzb⟩⟩)
      have hbactive : Q.paletteActive i θ b := ⟨hbi, hω, hcur, hnonlight⟩
      have hzC : z ∈ Q.coarseSupport (p.lev b) (code b) :=
        ⟨hzkeep.1, by simpa only [hbi, mem_ofPred_eq] using hzcode⟩
      have hzU : z ∈ U b := by
        by_contra hn
        apply hzkeep.2
        apply Or.inr
        apply Or.inr
        refine ⟨b, hbi, hbγ, ?_⟩
        have hzG' : z ∈ likelihoodGood Q.law S (finitePacketHistory p.lev p.γ p.F)
            (labelledVelocityPalette a₀) (p.lev b) stop R := by
          simpa only [hbi] using hzG
        rw [paletteOmissionFamily, if_pos (show p.lev b = i ∧
          0 < d.ω k (p.γ b) ∧ Q.currentParentLaw b univ ≠ 0 from ⟨hbi, hω, hcur⟩)]
        change (p.γ b, z.2) ∈ (likelihoodGood Q.law S (finitePacketHistory p.lev p.γ p.F)
          (labelledVelocityPalette a₀) (p.lev b) stop R ∩ Q.coarseSupport (p.lev b) (code b)) \ U b
        have hzpair : (p.γ b, z.2) = z := Prod.ext hbγ rfl
        rw [hzpair]
        exact ⟨⟨hzG', hzC⟩, hn⟩
      refine ⟨b, hbi, hbγ, ?_⟩
      simpa only [selectedCoarseFamily, ite_eq_left hbactive, mem_preimage, hbγ] using hzU
    exact hkeep.trans (measure_mono_ae hsubset)

/-- The half-mass specialization of the exact omission-budget bound. -/
theorem PreparedAngularPath.exists_selected_palette_family (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (q : PacketCoding p (d.ν k)) (i : ℕ) (hi : i < m) (stop : ℕ) (hst : i ≤ stop)
    {a₀ a₁ ε R α : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hε : 0 < ε) (hR : 0 ≤ R)
    (hmesh : a₀ * d.N k ^ (2 * δ₀ * d.L) ≤ a₁) (K : ℕ) (hK : (4 * p.κ + 6) ^ 2 ≤ (K : ℝ))
    (θ : ENNReal)
    (hbad : Q.law (labelledSupport Q.residual \ likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R) ≤ ENNReal.ofReal α)
    (hbudget : ENNReal.ofReal α + (θ * ENNReal.ofReal (8 * p.κ) + ENNReal.ofReal (ε * K)) ≤
      ENNReal.ofReal (1 / 2 : ℝ)) :
    ∃ code : Fin p.C → ℕ,
      (∀ b, Q.paletteActive i θ b →
        (∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
        Q.law (Q.coarseSupport (p.lev b) (code b)) ≠ 0 ∧
        (Q.coarseLaw (p.lev b) (code b)).map Prod.snd =
          ProbabilityTheory.cond (Q.currentParentLaw b) univ) ∧
      (∀ b, Q.paletteActive i θ b →
        MeasurableSet (Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε) ∧
        Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε ⊆
          Q.coarseSupport (p.lev b) (code b) ∧
        θ * d.pathAngularReference k p Q.base Q.mask b univ ≤ Q.currentParentLaw b univ ∧
        ∀ e a, (Q.coarseLaw (p.lev b) (code b)).real
          {z | z ∈ Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε ∧
            finitePacketHistory p.lev p.γ p.F stop z = e ∧ p.labelledNormalizedPalette b a₁ z = a} ≤
          (R / ε) * (Q.coarseLaw (p.lev b) (code b)).real
            {z | finitePacketHistory p.lev p.γ p.F stop z = e} *
            (Q.coarseLaw (p.lev b) (code b)).real {z | p.labelledNormalizedPalette b a₁ z = a}) ∧
      ENNReal.ofReal (1 / 2 : ℝ) ≤ Q.law (labelledSupport (Q.packetFamilyResidual i
        (Q.selectedCoarseFamily (Q.paletteActive i θ)
          (fun b => Q.normalizedPaletteCut b (p.lev b) stop (code b) a₀ a₁ R ε)))) := by
  have h := Q.exists_selected_palette_family_with_loss hd hp hHE hH q i hi stop hst
    ha₀ ha₁ hε hR hmesh K hK θ hbad (ENNReal.ofReal (1 / 2 : ℝ)) hbudget
  have hhalf : 1 - ENNReal.ofReal (1 / 2 : ℝ) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  simpa only [hhalf] using h

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
