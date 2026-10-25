-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.SaturationCapture, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/SaturationCapture.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/SaturationCapture.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/SaturationCapture.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PaletteStripSaturation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFinePacketBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativePredictionAssembly

/-! Actual captured incidences and their old-fine-packet witnesses. Their
analytic masks recover mass; the finite strip predictions specify the atlas. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
  {F : PaletteFamily Q i stop a A θ} (P : PaletteStripSaturation F r fraction)

noncomputable def PaletteStripSaturation.captured (b : Fin p.C) :
    Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)) :=
  ⋃ e : ℕ, ⋃ q ∈ P.predictions b e,
    {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ F.U b ∧
      p.normalizedVelocity b z.2 ∈ affineStrip q.val.1 q.val.2 r}

def PaletteStripSaturation.remainingU (b : Fin p.C) := F.U b \ P.captured b

noncomputable def PaletteStripSaturation.captureFamily (b : Fin p.C) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := by
  classical
  exact if F.active b then Prod.mk (p.γ b) ⁻¹' P.captured b else ∅

noncomputable def PaletteStripSaturation.captureResidual :=
  Q.packetFamilyResidual i P.captureFamily

noncomputable def PaletteStripSaturation.cleanCapture :=
  F.coding.cleanResidual P.captureResidual

theorem PaletteStripSaturation.captured_subset (b : Fin p.C) : P.captured b ⊆ F.U b := by
  intro z hz
  obtain ⟨e, he⟩ := mem_iUnion.mp hz
  obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp he
  exact hzq.2.1

variable {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteStripSaturation.captured_measurable
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) (hb : F.active b) : MeasurableSet (P.captured b) := by
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  apply MeasurableSet.iUnion
  intro e
  apply Finset.measurableSet_biUnion
  intro q hq
  exact (measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF stop) measurable_const).inter
    ((F.measurable_U b hb).inter ((measurableSet_affineStrip _ _ _).preimage
      ((p.measurable_normalizedVelocity b).comp measurable_snd)))

theorem PaletteStripSaturation.captureFamily_measurable
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (b : Fin p.C) : MeasurableSet (P.captureFamily b) := by
  classical
  by_cases hb : F.active b
  · simpa only [captureFamily, if_pos hb] using (P.captured_measurable hp b hb).preimage measurable_prodMk_left
  · simp only [captureFamily, if_neg hb]
    exact MeasurableSet.empty

theorem PaletteStripSaturation.captureFamily_subset (b : Fin p.C) :
    P.captureFamily b ⊆ Q.residual (p.γ b) ∩ p.F b := by
  classical
  by_cases hb : F.active b
  · intro x hx
    have hz : (p.γ b, x) ∈ F.U b := P.captured_subset b
      (by simpa only [captureFamily, if_pos hb, mem_preimage] using hx)
    have hC := F.subset_coarse b hb hz
    exact ⟨hC.1, (F.packet b hb _ hC).2⟩
  · simp only [captureFamily, if_neg hb]
    exact empty_subset _

theorem PaletteStripSaturation.captureResidual_subset_H (w : Fin (d.W k)) :
    P.captureResidual w ⊆ H w :=
  (Q.packetFamilyResidual_subset i P.captureFamily P.captureFamily_subset w).trans
    ((Q.residual_subset w).trans (Q.base_subset w))

theorem PaletteStripSaturation.cleanCapture_measurable
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ) :
    ∀ w, MeasurableSet (P.cleanCapture w) :=
  F.coding.cleanResidual_measurable
    (fun b => (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1) P.captureResidual
    (Q.measurableSet_packetFamilyResidual i P.captureFamily (P.captureFamily_measurable hp))

theorem PaletteStripSaturation.cleanCapture_original_mass
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ) :
    (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.cleanCapture w)) =
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w) := by
  simp only [cleanCapture, F.coding.cleanResidual_original_mass hp]

/-- Every captured original incidence carries its actual pre-H fine code
and one of that state's uniformly bounded strip predictions. -/
theorem PaletteStripSaturation.cleanCapture_witness
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hstop : stop < m) (w : Fin (d.W k)) (x : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hx : x ∈ P.cleanCapture w) :
    ∃ b, p.lev b = i ∧ p.γ b = w ∧ F.active b ∧ x ∈ p.F b ∧ ∃ f,
      p.lev f = stop ∧ p.γ f = w ∧ x ∈ p.packetWitness m stop w f ∧
      ∃ q ∈ P.predictions b (F.coding.code f), p.normalizedVelocity b x ∈ affineStrip q.val.1 q.val.2 r := by
  classical
  obtain ⟨b, hbi, hbγ, hxb⟩ := hx.1.1
  have hxH := P.captureResidual_subset_H w hx.1.1
  have hb : F.active b := by
    by_contra hn
    simp only [captureFamily, if_neg hn, mem_empty_iff_false] at hxb
  have hz : (p.γ b, x) ∈ P.captured b := by
    simpa only [captureFamily, if_pos hb, mem_preimage] using hxb
  obtain ⟨e, he⟩ := mem_iUnion.mp hz
  obtain ⟨q, hq, hze, hzU, hzstrip⟩ := mem_iUnion₂.mp he
  have hxcoarse : x ∈ p.F b := (P.captureFamily_subset b hxb).2
  obtain ⟨f, hf, hfγ, hxf⟩ := hp.covered_at_level H stop hstop hH w hxH
  have hcode := F.coding.code_eq_of_mem_core w hx.1.2 f hfγ hxf
  rw [hf] at hcode
  have hecode : e = F.coding.code f := by
    have hz' : finitePacketHistory p.lev p.γ p.F stop (w, x) = e := by simpa only [hbγ] using hze
    exact hz'.symm.trans hcode
  have hxterminal : x ∈ p.terminalCoverage m w := by
    obtain ⟨t, ht, htγ, hxt⟩ := hH w hxH
    exact ⟨t, ⟨ht, htγ⟩, hxt⟩
  have hxW : x ∈ p.packetWitness m stop w f := by
    rw [PathData.packetWitness, if_pos (show p.lev f = stop ∧ p.γ f = w from ⟨hf, hfγ⟩)]
    exact ⟨⟨hxf, hx.2⟩, hxterminal⟩
  exact ⟨b, hbi, hbγ, hb, hxcoarse, f, hf, hfγ, hxW, q, by simpa only [hecode] using hq, hzstrip⟩

/-- Saturation bounds every strip outside the captured union, with the
OLD fine-state mass as denominator. -/
theorem PaletteStripSaturation.remaining_strip_cap (b : Fin p.C) (hb : F.active b)
    (e : ℕ) (n : StripSpace) (β : ℝ) (hn : ‖n‖ = 1) :
    (Q.coarseLaw (p.lev b) (F.code b)).real
      {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ P.remainingU b ∧
        p.normalizedVelocity b z.2 ∈ affineStrip n β r} ≤
      fraction * (Q.coarseLaw (p.lev b) (F.code b)).real
        {z | finitePacketHistory p.lev p.γ p.F stop z = e} := by
  let : IsFiniteMeasure (Q.coarseLaw (p.lev b) (F.code b)) := by
    change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
    infer_instance
  apply le_trans (measureReal_mono _) (P.outside_cap b hb e n β hn)
  intro z hz
  refine ⟨hz.1, hz.2.1.1, hz.2.2, ?_⟩
  intro q hq hzq
  exact hz.2.1.2 (mem_iUnion.mpr ⟨e, mem_iUnion₂.mpr ⟨q, hq, hz.1, hz.2.1.1, hzq⟩⟩)

theorem PaletteStripSaturation.remaining_not_narrow (hfraction : 0 < fraction)
    (b : Fin p.C) (hb : F.active b) (e : ℕ) :
    e ∉ Q.intrinsicNarrowStates F.code stop P.remainingU r (2 * fraction) b := by
  intro he
  obtain ⟨n, β, hn, hmass⟩ := he.2
  have hcap := P.remaining_strip_cap b hb e n β hn
  have hpos := mul_pos hfraction he.1
  linarith

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
