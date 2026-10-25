-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.AncestorCoefficients, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/AncestorCoefficients.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorSource

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set

noncomputable section

namespace AncestorSource

open ParentSource.ParentSignal

/-- At a shallow ancestor the constant physical height coefficient has
an explicit clock cost; it is included in the budget. -/
theorem scaleSignal_uniform_bound {clock bound : ℝ} (hclock : 1≤clock)
    (c : Fin 7→ℝ) (hc : ∀ i,|c i|≤bound) :
    ∀ i,|scaleSignal clock c i|≤bound*clock := by
  have hb : 0≤bound := (abs_nonneg _).trans (hc 0)
  have hh : 0≤clock := zero_le_one.trans hclock
  have hscaled j : |clock*c j|≤bound*clock := by
    rw [abs_mul,abs_of_nonneg hh]
    exact (mul_le_mul_of_nonneg_left (hc j) hh).trans_eq (mul_comm _ _)
  have hplain j : |c j|≤bound*clock :=
    (hc j).trans (le_mul_of_one_le_right hb hclock)
  intro i
  fin_cases i
  · exact hscaled 0
  · exact hscaled 1
  · exact hscaled 2
  · exact hplain 3
  · exact hplain 4
  · exact hplain 5
  · exact hplain 6

section Selected

variable {p : DensityPreparation.Problem} {S η : ℝ} (hp : p.Valid S η)
    {R A : Finset ℝ} {τ : ℝ} {k : ℕ} {pth : OriginalPath.Data (p.W k)}
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ→ℝ} {H : Fin (p.W k)→Set Ev}
    (hpth : pth.Valid 0 (p.N k) p.L (p.ω k) (p.ν k) (p.E k) (p.B k) p.f
      κ₁ m s δ₀ Mp Dp σ)
    (a : Selection p S R A τ k pth H)

include hp hpth

/-- All seven physical parent coefficients are bounded on the actual
normalized ancestor source, using its original pointwise line bounds. -/
theorem Selection.clock_coefficients_bound {K : ℝ} (hK : 24≤K)
    (hmax : max pth.κ (p.K k)≤K) (z : Ev)
    (hz : z∈(a.packet hpth).selectedEvent a.current) :
    ∀ i,|clockPacketCoefficients (p.P k (pth.world a.node))
      (SourceBridge.path pth) a.node z.1 i|≤K^4*(2:ℝ)^pth.T 0 := by
  let q := AncestorQualification.fromAncestor (a.packet hpth).unitFrame.t₀
    (a.packet hpth).unitFrame.q z
  have hq : q∈a.current := by
    rwa [selectedEvent_eq] at hz
  have hprepared := a.pointwise q hq
  have hvel : ‖v q.1‖≤p.K k := by
    have hh := hprepared.planar 0 (by norm_num)
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans hh
  have hmodel := (SourceBridge.problem_valid_iff p S η).mpr hp
  have hpath := (SourceBridge.path_valid_iff pth (p.N k) p.L (p.ω k) (p.ν k)
    (p.E k) (p.B k) p.f κ₁ m s δ₀ Mp Dp σ).mpr hpth
  have hc := oldPacket_coefficient_bounds hmodel hpath a.node hK hmax
    (a.subset hq).2 hprepared.parent hvel
  have hbound := scaleSignal_uniform_bound
    (one_le_pow₀ (by norm_num : (1:ℝ)≤2) : 1≤(2:ℝ)^pth.T (pth.lev a.node))
    _ hc
  simpa only [clockPacketCoefficients,SourceBridge.path,SourceBridge.problem,a.level,
    q,AncestorQualification.fromAncestor] using hbound

end Selected

end AncestorSource

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
