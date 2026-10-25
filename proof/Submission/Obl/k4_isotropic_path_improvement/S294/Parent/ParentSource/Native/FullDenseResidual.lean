-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FullDenseResidual, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FullDenseResidual.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FullDenseResidual.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FullDenseResidual.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FullDensity
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeDichotomy

/-! Broad selected fine packets retain a floor against their full original
prior and old time block, after a single fixed-factor original-law deletion. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
  {F : PaletteFamily Q i stop a A θ} (R : BroadResidual F r fraction)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem BroadResidual.subset_prepared (w : Fin (d.W k)) : R.residual w ⊆ Q.residual w := by
  intro x hx
  obtain ⟨b, _, hbγ, _, hb, hxU, _⟩ := R.witness w x hx
  simpa only [hbγ, labelledSupport, mem_ofPred_eq] using (F.subset_coarse b hb hxU).1

theorem BroadResidual.exists_full_dense_residual (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hstop : stop < m) :
    ∃ J : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (J w)) ∧ (∀ w, J w ⊆ R.residual w) ∧
      ENNReal.ofReal (p.κ⁻¹ / 64) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (J w) ∧
      ∀ w x, x ∈ J w → ∃ b, p.lev b = i ∧ p.γ b = w ∧ x ∈ p.F b ∧
        F.active b ∧ (p.γ b, x) ∈ F.U b ∧ ∃ f,
          p.lev f = stop ∧ p.γ f = w ∧ x ∈ p.packetWitness m stop w f ∧
          F.coding.code f ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b ∧
          F.coding.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
            (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)) ∧
          ENNReal.ofReal ((p.κ⁻¹ / 64) / (2 : ℝ) ^ p.T stop) * d.ν k (p.γ f) (p.A f) ≤
            ((d.ν k (p.γ f)).prod volume) (Q.residual (p.γ f) ∩ p.F f) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  obtain ⟨hω, hsum, hν⟩ := hd.weights k
  let mass : ℝ := (p.κ⁻¹ / 8) * ((1 / 2) / 2)
  have hhalf : mass / 2 = p.κ⁻¹ / 64 := by dsimp only [mass]; ring
  obtain ⟨J, hJ, hsub, hmass, hwitness⟩ := hp.exists_full_dense_residual hν hω hsum
    R.residual R.measurable (fun w => (R.subset_H w).trans (hH w)) stop hstop
    (α := mass) (by dsimp only [mass]; positivity) R.mass
  rw [hhalf] at hmass
  refine ⟨J, hJ, hsub, hmass, ?_⟩
  intro w x hx
  obtain ⟨g, hg, hgw, hxg, hgfloor⟩ := hwitness w x hx
  obtain ⟨b, hbi, hbw, hxb, hb, hxU, f, hf, hfw, hxf, hbad, hretained⟩ :=
    R.witness w x (hsub w hx)
  have hdata : (x ∈ p.F f ∧ packetUnique p.lev p.γ p.F w x) ∧
      x ∈ p.terminalCoverage m w := by
    simpa only [PathData.packetWitness, ite_eq_left (show p.lev f = stop ∧ p.γ f = w from ⟨hf, hfw⟩),
      mem_inter_iff, mem_ofPred_eq] using hxf
  have hfg : f = g := hdata.1.2 f g (hf.trans hg.symm) hfw hgw hdata.1.1 hxg
  rw [← hfg, hhalf] at hgfloor
  refine ⟨b, hbi, hbw, hxb, hb, hxU, f, hf, hfw, hxf, hbad, hretained, ?_⟩
  exact hgfloor.trans (measure_mono (fun _ hy => ⟨R.subset_prepared _ hy.1, hy.2⟩))

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
