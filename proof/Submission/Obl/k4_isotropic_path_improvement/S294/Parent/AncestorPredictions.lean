-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.AncestorPredictions, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/AncestorPredictions.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorPackets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.VelocityFrameTransfer
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.SaturationCapture
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.SaturationPredictions

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorPredictions

open MeasureTheory Set
open ParentSource ParentSource.Native AncestorPackets
open Submission.Lib.K4VelocityStrips

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (P : PaletteStripSaturation F r fraction)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The finite strip predictions captured at an early window become a
fixed finite family on each later original packet. Both early packet
labels are its actual ancestors. The full target assignment supplies
the offset bound and only the genuine frame condition number widens
its strips. -/
theorem exists_descendant_capture_strips (hN : 1 ≤ d.N k)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hi : i ≤ stop) (hstop : stop < m) (targetLevel : ℕ)
    (htarget : targetLevel < m) (horder : stop ≤ targetLevel)
    (J : ℕ) (hJ : fraction⁻¹ ≤ (J : ℝ)) (hr : 0 ≤ r)
    {radius : ℝ} (hradius : 0 ≤ radius)
    (hscale : r * (p.κ ^ 2 * d.N k ^ (2 * δ₀ * d.L)) ≤ radius) :
    ∃ (normal : p.StripLevel targetLevel → Fin J → StripSpace)
      (offset : p.StripLevel targetLevel → Fin J → ℝ),
      (∀ b j, ‖normal b j‖ = 1) ∧
      (∀ b j, |offset b j| ≤ 2 * p.κ + radius) ∧
      ∀ w, P.cleanCapture w ⊆ {x | ∃ b : p.StripLevel targetLevel,
        p.γ b = w ∧ x ∈ p.F b ∧ p.normalizedVelocity b x ∈
          ⋃ j, affineStrip (normal b j) (offset b j) radius} := by
  classical
  obtain ⟨params,hparams⟩ := P.exists_prediction_arrays J hJ
  let prediction (b : p.StripLevel targetLevel) (j : Fin J) : UnitStripParameter :=
    params (ancestor p b i) (F.coding.code (ancestor p b stop)) j
  have hex (b : p.StripLevel targetLevel) (j : Fin J) :=
    VelocityFrameTransfer.exists_bounded_strip_transfer hp hN (ancestor p b i) b
      hr hradius hscale (prediction b j).val.1 (prediction b j).val.2 (prediction b j).property
  choose normal offset hn hoff htransfer using hex
  refine ⟨normal,offset,hn,hoff,?_⟩
  intro w x hx
  have hxH : x ∈ H w := P.captureResidual_subset_H w hx.1.1
  have hxbase : x ∈ Q.base w := Q.residual_subset w
    ((Q.packetFamilyResidual_subset i P.captureFamily P.captureFamily_subset w) hx.1.1)
  obtain ⟨b,hbi,hbw,hbactive,hxb,f,hf,hfw,hxf,q,hq,hstrip⟩ :=
    P.cleanCapture_witness hp hH hstop w x hx
  obtain ⟨target,ht,htw,hxt⟩ := hp.covered_at_level H targetLevel htarget hH w hxH
  let btarget : p.StripLevel targetLevel := ⟨target,ht⟩
  have hbancestor : b = ancestor p target i := by
    have hh := eq_ancestor_of_common_incidence Q hp b target (by omega) (hbw.trans htw.symm)
      x (by simpa only [htw] using hxbase) hxb hxt
    simpa only [hbi] using hh
  have hfF : x ∈ p.F f := by
    have hh : x ∈ (p.F f ∩ {z | packetUnique p.lev p.γ p.F w z}) ∩
        p.terminalCoverage m w := by
      simpa only [PathData.packetWitness,ite_eq_left (show p.lev f = stop ∧ p.γ f = w from
        ⟨hf,hfw⟩)] using hxf
    exact hh.1.1
  have hfancestor : f = ancestor p target stop := by
    have hh := eq_ancestor_of_common_incidence Q hp f target (by omega) (hfw.trans htw.symm)
      x (by simpa only [htw] using hxbase) hfF hxt
    simpa only [hf] using hh
  obtain ⟨j,hj⟩ := hparams b hbactive (F.coding.code f) q hq
  have hprediction : prediction btarget j = q := by
    dsimp only [prediction,btarget]
    rw [← hbancestor,← hfancestor]
    exact hj
  have hxA : x.1 ∈ p.A target := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hinc,_⟩ := hp.2.2.2.2.2.2.2 target
    exact (hinc x hxt).2.1
  refine ⟨btarget,htw,hxt,mem_iUnion.mpr ⟨j,?_⟩⟩
  apply htransfer btarget j x hxA
  simpa only [btarget,← hbancestor,hprediction] using hstrip

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorPredictions
