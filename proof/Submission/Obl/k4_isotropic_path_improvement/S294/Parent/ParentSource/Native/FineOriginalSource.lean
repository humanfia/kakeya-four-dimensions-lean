-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FineOriginalSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FineOriginalSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FineOriginalSource.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FineOriginalSource.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.SelectedFineLaws

/-! Positive sampled velocity events have positive ORIGINAL product-law
mass in the same old fine packet, with the actual selected incidence cut. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
  (F : PaletteFamily Q i stop a A θ)

def PaletteFamily.fineOriginalEvent (b f : Fin p.C)
    (V : Set (EuclideanSpace ℝ (Fin 2))) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {x | x ∈ p.packetWitness m stop (p.γ b) f ∧ (p.γ b, x) ∈ F.U b ∧
    p.normalizedVelocity b x ∈ V}

theorem PaletteFamily.fine_original_absolutelyContinuous
    (hHE : ∀ w, H w ⊆ d.E k w) (hF : ∀ b, MeasurableSet (p.F b))
    (b : Fin p.C) (hb : F.active b) (e : ℕ) :
    (F.fineLaw b e).map Prod.snd ≪ ((d.ν k (p.γ b)).prod volume) := by
  have hac : F.fineLaw b e ≪ Q.coarseLaw (p.lev b) (F.code b) :=
    ProbabilityTheory.cond_absolutelyContinuous
  have hmap := hac.map measurable_snd
  rw [F.posterior b hb] at hmap
  have hcurrent : Q.currentParentLaw b ≪ ((d.ν k (p.γ b)).prod volume) := by
    rw [Q.current_parent_eq_original hHE hF b]
    exact Measure.restrict_le_self.absolutelyContinuous
  exact hmap.trans (ProbabilityTheory.cond_absolutelyContinuous.trans hcurrent)

variable {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteFamily.fine_original_event_mass_pos
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (b : Fin p.C) (hb : F.active b) (f : Fin p.C) (hf : p.lev f = stop)
    (hfγ : p.γ f = p.γ b) (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : MeasurableSet V)
    (hpos : 0 < F.fineVelocityLaw b (F.coding.code f) V) :
    0 < ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f V) := by
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hVm : Measurable (fun z : Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ) =>
      p.normalizedVelocity b z.2) := (p.measurable_normalizedVelocity b).comp measurable_snd
  have hD : MeasurableSet (F.fineOriginalEvent b f V) :=
    (hp.measurableSet_packetWitness stop (p.γ b) f).inter
      (((F.measurable_U b hb).preimage measurable_prodMk_left).inter
        (hV.preimage (p.measurable_normalizedVelocity b)))
  have hpacket : ∀ᵐ z ∂F.fineLaw b (F.coding.code f), z.2 ∈ p.packetWitness m stop (p.γ b) f := by
    simpa only [hfγ] using F.fine_law_original_packet hp hH b hb f hf hfγ
  have hcell : ∀ᵐ z ∂F.fineLaw b (F.coding.code f),
      finitePacketHistory p.lev p.γ p.F stop z = F.coding.code f ∧ z ∈ F.U b :=
    ProbabilityTheory.ae_cond_mem ((measurableSet_eq_fun
      (measurable_finitePacketHistory p.lev p.γ p.F hF stop) measurable_const).inter (F.measurable_U b hb))
  have hgood : ∀ᵐ z ∂F.fineLaw b (F.coding.code f),
      z.2 ∈ p.packetWitness m stop (p.γ b) f ∧ (p.γ b, z.2) ∈ F.U b := by
    filter_upwards [hpacket, hcell] with z hzpacket hzcell
    have hworld := (F.packet b hb z (F.subset_coarse b hb hzcell.2)).1
    have heq : (p.γ b, z.2) = z := Prod.ext hworld.symm rfl
    exact ⟨hzpacket, by simpa only [heq] using hzcell.2⟩
  have heq : ((F.fineLaw b (F.coding.code f)).map Prod.snd) (F.fineOriginalEvent b f V) =
      F.fineVelocityLaw b (F.coding.code f) V := by
    rw [Measure.map_apply measurable_snd hD, fineVelocityLaw, Measure.map_apply hVm hV]
    apply measure_congr
    filter_upwards [hgood] with z hz
    simp only [mem_preimage, fineOriginalEvent, mem_ofPred_eq, hz.1, hz.2, true_and]
  apply pos_iff_ne_zero.mpr
  intro hz
  have hzero := F.fine_original_absolutelyContinuous hHE hF b hb (F.coding.code f) hz
  rw [heq] at hzero
  exact hpos.ne' hzero

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
