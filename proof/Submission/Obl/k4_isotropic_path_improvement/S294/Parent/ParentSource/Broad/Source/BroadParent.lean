-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.BroadParent, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/BroadParent.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/BroadParent.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentSelection
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.DenseBroadStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineOriginalSource

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Fixing the actual old parent retains the original fine histories and
their intrinsic breadth. The fine-history tag need not enter a later
physical state. -/
theorem BroadResidual.original_parent_fine_cover
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (R : BroadResidual F r fraction)
    (b : Fin p.C) (hbi : p.lev b = i)
    (x : (ℕ × (Fin 6 → ℝ)) × ℝ) (hx : x ∈ R.residual (p.γ b) ∩ p.F b) :
    ∃ f : Fin p.C, p.lev f = stop ∧ p.γ f = p.γ b ∧
      F.coding.code f ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction b ∧
      F.coding.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1 / 8 : ℝ)) ∧
      x ∈ F.fineOriginalEvent b f univ := by
  obtain ⟨b', hb'i, hb'w, hxb', _, hxU, f, hf, hfw, hxf, hbad, hretained⟩ :=
    R.witness (p.γ b) x hx.1
  have hbeq : b = b' := R.packet_unique _ _ hx.1 b b'
    (hbi.trans hb'i.symm) rfl hb'w hx.2 hxb'
  subst b'
  exact ⟨f, hf, hfw, hbad, hretained, hxf, hxU, mem_univ _⟩

/-- The actual broad residual supplies an active old parent, with its
full original prior, a substantial native source, and bounded scalar coefficients. -/
theorem BroadResidual.exists_original_parent_source
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (R : BroadResidual F r fraction)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hi : i < m) :
    ∃ b : Fin p.C, p.lev b = i ∧ F.active b ∧ 0 < d.ω k (p.γ b) ∧
      d.ν k (p.γ b) (p.A b) ≠ 0 ∧
      ENNReal.ofReal (p.κ⁻¹ / 32) ≤
        (hp.frozenPacket b).selectedLaw (d.ν k (p.γ b))
          (R.residual (p.γ b) ∩ p.F b) univ ∧
      (hp.frozenPacket b).selectedLaw (d.ν k (p.γ b))
          (R.residual (p.γ b) ∩ p.F b) ≤
        (hp.frozenPacket b).law (d.ν k (p.γ b)) ∧
      (∀ᵐ z ∂(hp.frozenPacket b).selectedLaw (d.ν k (p.γ b))
          (R.residual (p.γ b) ∩ p.F b),
        ∀ e, |(hp.frozenPacket b).scalarCoefficients z.1 e| ≤ 17 * p.κ) := by
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hα : 0 < p.κ⁻¹ / 32 := by positivity
  obtain ⟨hω, hsum, hν⟩ := hd.weights k
  have hmass : ENNReal.ofReal (p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (R.residual w) := by
    convert R.mass using 1
    congr 1
    ring
  obtain ⟨b, hb, hw, hA, hbmass, hdom, hcoeff⟩ := hp.exists_original_parent_source
    hν hω hsum R.residual R.measurable (fun w => (R.subset_H w).trans (hH w)) hα hmass i hi
  have hnonempty : (R.residual (p.γ b) ∩ p.F b).Nonempty := by
    by_contra hn
    have hempty : R.residual (p.γ b) ∩ p.F b = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hz : (hp.frozenPacket b).selectedLaw (d.ν k (p.γ b))
        (R.residual (p.γ b) ∩ p.F b) univ = 0 := by
      simp [Broad.Source.FrozenPacket.selectedLaw, Broad.Source.FrozenPacket.selectedEvent, hempty]
    rw [hz] at hbmass
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hα)) hbmass
  obtain ⟨z, hzR, hzF⟩ := hnonempty
  obtain ⟨b', hb'i, hb'w, hzb', hb'active, _⟩ := R.witness _ _ hzR
  have hbase : z ∈ Q.base (p.γ b) := Q.residual_subset _ (R.subset_prepared _ hzR)
  have heq : b = b' := Q.base_packet_unique _ _ hbase b b'
    (hb.trans hb'i.symm) rfl hb'w hzF hzb'
  exact ⟨b, hb, heq.symm ▸ hb'active, hw, hA, hbmass, hdom, hcoeff⟩

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
