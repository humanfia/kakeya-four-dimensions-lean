-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.OriginalVelocityPalette, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/OriginalVelocityPalette.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.StrongPalette
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FinePaletteDomination
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineOriginalCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette

open MeasureTheory Set
open scoped ENNReal
open ParentSource ParentSource.Native

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A a₀ R : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (hst : i ≤ stop) (hR : 0 ≤ R)
    (horiginal : ∀ b, F.active b → F.U b ⊆
      likelihoodGood Q.law (labelledSupport Q.residual)
        (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R)

include hd hp hHE hst hR horiginal

/-- The initial original-velocity likelihood ceiling survives the later
normalized-palette cut and every subsequent subfamily of that cut. Both
marginals are those of the unchanged original coarse posterior. -/
theorem original_bin_joint_cap (b : Fin p.C) (hb : F.active b) (e : ℕ) (β : ℤ × ℤ) :
    (Q.coarseLaw (p.lev b) (F.code b)).real
      {z | z∈F.U b ∧ finitePacketHistory p.lev p.γ p.F stop z=e ∧
        labelledVelocityPalette a₀ z=β} ≤
      R*(Q.coarseLaw (p.lev b) (F.code b)).real
          {z | finitePacketHistory p.lev p.γ p.F stop z=e} *
        (Q.coarseLaw (p.lev b) (F.code b)).real
          {z | labelledVelocityPalette a₀ z=β} := by
  haveI : IsProbabilityMeasure Q.law := Q.probability hd hHE (zero_lt_one.trans_le hp.1)
  haveI : IsFiniteMeasure (Q.coarseLaw (p.lev b) (F.code b)) := by
    change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
    infer_instance
  have hF (c : Fin p.C) : MeasurableSet (p.F c) :=
    (hp.2.2.2.2.2.2.2 c).2.2.2.2.2.2.2.2.2.1
  have hcap := likelihoodGood_conditional_joint_cap Q.law (labelledSupport Q.residual)
    (measurableSet_labelledSupport _ Q.residual_measurable)
    (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R hR
    (measurable_finitePacketHistory p.lev p.γ p.F hF i)
    (fun _ _ _ _ he => finitePacketHistory_nested p.lev p.γ p.F hst he)
    (F.code b) e β
  have hmono : (Q.coarseLaw (p.lev b) (F.code b)).real
      {z | z∈F.U b ∧ finitePacketHistory p.lev p.γ p.F stop z=e ∧ labelledVelocityPalette a₀ z=β} ≤
      (Q.coarseLaw (p.lev b) (F.code b)).real
      {z | z∈likelihoodGood Q.law (labelledSupport Q.residual)
          (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R ∧
        finitePacketHistory p.lev p.γ p.F stop z=e ∧ labelledVelocityPalette a₀ z=β} :=
    measureReal_mono (fun z hz => ⟨horiginal b hb hz.1,hz.2⟩) (measure_ne_top _ _)
  apply hmono.trans
  simpa only [PreparedAngularPath.coarseLaw, PreparedAngularPath.coarseSupport,F.level b hb]
    using hcap

/-- Every retained fine-history law is dominated on ORIGINAL physical
velocity bins by one fixed original coarse-posterior palette. The fine
history's retained mass is not substituted for either original marginal. -/
theorem original_fine_palette_domination (b : Fin p.C) (hb : F.active b) (e : ℕ)
    (he : e∉fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1/8 : ℝ))) :
    (ProbabilityTheory.cond (Q.coarseLaw (p.lev b) (F.code b))
      {z | finitePacketHistory p.lev p.γ p.F stop z=e ∧ z∈F.U b}).map
        (labelledVelocityPalette a₀) ≤
      ENNReal.ofReal (8*R) •
        (Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀) := by
  haveI : IsProbabilityMeasure Q.law := Q.probability hd hHE (zero_lt_one.trans_le hp.1)
  haveI : IsFiniteMeasure (Q.coarseLaw (p.lev b) (F.code b)) := by
    change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
    infer_instance
  have hF (c : Fin p.C) : MeasurableSet (p.F c) :=
    (hp.2.2.2.2.2.2.2 c).2.2.2.2.2.2.2.2.2.1
  have hvel : Measurable (labelledVelocityPalette (W := d.W k) a₀) := by
    apply measurable_euclidean_velocityPalette
    exact (show Measurable (fun z : Fin (d.W k)×Ev => v z.2.1) by unfold v; fun_prop)
  have hh := retained_fine_palette_domination (Q.coarseLaw (p.lev b) (F.code b))
    (finitePacketHistory p.lev p.γ p.F stop) (F.U b)
    (fun q => (measurable_finitePacketHistory p.lev p.γ p.F hF stop) (measurableSet_singleton q))
    (F.measurable_U b hb) (labelledVelocityPalette a₀) hvel hR (by norm_num : (0:ℝ)<1/8)
    e he (original_bin_joint_cap F hd hp hHE hst hR horiginal b hb e)
  convert hh using 1
  congr 2
  ring

/-- Domination in a retained fine history gives the actual original
physical-velocity numerator ceiling in FULL assignment and clock units. -/
theorem fine_original_physical_palette_cap
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (b f : Fin p.C) (hb : F.active b) (hf : p.lev f=stop) (hfγ : p.γ f=p.γ b)
    (he : F.coding.code f∉fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1/8 : ℝ)))
    (D : Set (ℤ×ℤ)) (hD : MeasurableSet D) :
    ((d.ν k (p.γ b)).prod volume)
      (F.fineOriginalEvent b f univ ∩ {z | velocityPalette a₀ (v z.1)∈D}) ≤
      ENNReal.ofReal (8*R) *
        (ENNReal.ofReal (((2 : ℝ)^p.T stop)⁻¹)*d.ν k (p.γ f) (p.A f)) *
        ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D := by
  haveI : IsProbabilityMeasure (d.ν k (p.γ b)) := (hd.weights k).2.2 _
  let src := F.fineOriginalEvent b f univ
  let raw := (d.ν k (p.γ b)).prod (volume : Measure ℝ)
  let control : Ev → ℤ×ℤ := fun z => velocityPalette a₀ (v z.1)
  have hm : Measurable control := by
    apply measurable_euclidean_velocityPalette
    exact (show Measurable (fun z : Ev => v z.1) by unfold v; fun_prop)
  have hsource := F.fine_original_event_measurable hp b f hb univ MeasurableSet.univ
  have hfull := F.fine_original_source_mass_le_full hd hp b f hf hfγ
  have htop : raw src≠∞ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by rw [hfγ]; exact measure_ne_top _ _)) hfull
  have hmap : (F.fineLaw b (F.coding.code f)).map (labelledVelocityPalette a₀) =
      ((F.fineLaw b (F.coding.code f)).map Prod.snd).map control :=
    (Measure.map_map hm measurable_snd).symm
  have hexact : ((F.fineLaw b (F.coding.code f)).map (labelledVelocityPalette a₀)) D * raw src =
      raw (src ∩ control ⁻¹' D) := by
    rw [hmap,F.fine_original_posterior hd hp hHE hH b hb f hf hfγ,Measure.map_apply hm hD]
    exact ProbabilityTheory.cond_mul_eq_inter' hsource htop (control ⁻¹' D)
  have hdom := original_fine_palette_domination F hd hp hHE hst hR horiginal b hb
    (F.coding.code f) he D
  rw [Measure.smul_apply,smul_eq_mul] at hdom
  calc
    _ = raw (src ∩ control ⁻¹' D) := rfl
    _ = ((F.fineLaw b (F.coding.code f)).map (labelledVelocityPalette a₀)) D * raw src := hexact.symm
    _ ≤ (ENNReal.ofReal (8*R) *
        ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D) *
        (ENNReal.ofReal (((2 : ℝ)^p.T stop)⁻¹)*d.ν k (p.γ f) (p.A f)) :=
      mul_le_mul' hdom hfull
    _ = _ := by ring

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
