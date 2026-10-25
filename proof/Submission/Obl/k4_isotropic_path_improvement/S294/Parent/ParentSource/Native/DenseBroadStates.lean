-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.DenseBroadStates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/DenseBroadStates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/DenseBroadStates.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/DenseBroadStates.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FullDenseResidual
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.UniquePacketPartition

/-! Dense original fine-state families have intrinsic packet eligibility.
The property is fixed for a whole old packet, not just a chosen incidence. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
  {F : PaletteFamily Q i stop a A θ}

structure DenseBroadResidual (R : BroadResidual F r fraction) where
  residual : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  measurable : ∀ w, MeasurableSet (residual w)
  subset : ∀ w, residual w ⊆ R.residual w
  mass : ENNReal.ofReal (p.κ⁻¹ / 64) ≤
    ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (residual w)
  full_density : ∀ w x, x ∈ residual w → ∀ f, p.lev f = stop → p.γ f = w → x ∈ p.F f →
    ENNReal.ofReal ((p.κ⁻¹ / 64) / (2 : ℝ) ^ p.T stop) * d.ν k (p.γ f) (p.A f) ≤
      ((d.ν k (p.γ f)).prod volume) (Q.residual (p.γ f) ∩ p.F f)

variable (R : BroadResidual F r fraction)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem BroadResidual.packet_unique (w : Fin (d.W k)) (x : (ℕ × (Fin 6 → ℝ)) × ℝ)
    (hx : x ∈ R.residual w) : packetUnique p.lev p.γ p.F w x := by
  obtain ⟨_, _, _, _, _, _, f, hf, hfγ, hxf, _⟩ := R.witness w x hx
  have hdata : (x ∈ p.F f ∧ packetUnique p.lev p.γ p.F w x) ∧ x ∈ p.terminalCoverage m w := by
    simpa only [PathData.packetWitness, ite_eq_left (show p.lev f = stop ∧ p.γ f = w from ⟨hf, hfγ⟩),
      mem_inter_iff, mem_ofPred_eq] using hxf
  exact hdata.1.2

theorem BroadResidual.exists_denseBroadResidual (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hstop : stop < m) : Nonempty (DenseBroadResidual R) := by
  obtain ⟨J, hJ, hsub, hmass, hpoint⟩ := R.exists_full_dense_residual hd hp hH hstop
  refine ⟨⟨J, hJ, hsub, hmass, ?_⟩⟩
  intro w x hx f hf hfγ hxf
  obtain ⟨_, _, _, _, _, _, g, hg, hgγ, hxg, _, _, hfloor⟩ := hpoint w x hx
  have hunique := R.packet_unique w x (hsub w hx)
  have hxFg : x ∈ p.F g := by
    have hdata : (x ∈ p.F g ∧ packetUnique p.lev p.γ p.F w x) ∧ x ∈ p.terminalCoverage m w := by
      simpa only [PathData.packetWitness, ite_eq_left (show p.lev g = stop ∧ p.γ g = w from ⟨hg, hgγ⟩),
        mem_inter_iff, mem_ofPred_eq] using hxg
    exact hdata.1.1
  have hfg : f = g := hunique f g (hf.trans hg.symm) hfγ hgγ hxf hxFg
  simpa only [hfg] using hfloor

theorem BroadResidual.packet_eligibility
    (b f : Fin p.C) (hbi : p.lev b = i) (hfi : p.lev f = stop) (hfγ : p.γ f = p.γ b)
    (x : (ℕ × (Fin 6 → ℝ)) × ℝ) (hx : x ∈ R.residual (p.γ b))
    (hxb : x ∈ p.F b) (hxf : x ∈ p.F f) :
    F.active b ∧ (p.γ b, x) ∈ F.U b ∧
      F.coding.code f ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b ∧
      F.coding.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)) := by
  obtain ⟨b', hb'i, hb'γ, hxb', hb', hxU, f', hf'i, hf'γ, hxf', hbad, hretained⟩ :=
    R.witness (p.γ b) x hx
  have hunique := R.packet_unique (p.γ b) x hx
  have hbEq : b = b' := hunique b b' (hbi.trans hb'i.symm) rfl hb'γ hxb hxb'
  have hxfF : x ∈ p.F f' := by
    have hdata : (x ∈ p.F f' ∧ packetUnique p.lev p.γ p.F (p.γ b) x) ∧
        x ∈ p.terminalCoverage m (p.γ b) := by
      simpa only [PathData.packetWitness,
        ite_eq_left (show p.lev f' = stop ∧ p.γ f' = p.γ b from ⟨hf'i, hf'γ⟩),
        mem_inter_iff, mem_ofPred_eq] using hxf'
    exact hdata.1.1
  have hfEq : f = f' := hunique f f' (hfi.trans hf'i.symm) hfγ hf'γ hxf hxfF
  subst b'
  subst f'
  exact ⟨hb', hxU, hbad, hretained⟩

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
