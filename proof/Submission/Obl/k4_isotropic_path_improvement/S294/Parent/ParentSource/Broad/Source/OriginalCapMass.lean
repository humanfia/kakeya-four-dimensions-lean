-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalCapMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalCapMass.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalCapMass.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentUnshearedBandWidths

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open MeasureTheory Set Native
open scoped ENNReal
noncomputable section

/-- Return a normalized continuous cap to the fixed original reference
units. No restriction is used to redefine that reference. -/
theorem original_mass_of_normalized_base_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → EuclideanSpace ℝ (Fin 3)) (hbase : Measurable base)
    {reference C : ENNReal} (hzero : reference ≠ 0) (htop : reference ≠ ⊤)
    (hcap : reference⁻¹ • μ.map base ≤ C • volume)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    μ {z | base z∈U} ≤ C*reference*volume U := by
  have hh := hcap U
  simp only [Measure.smul_apply,smul_eq_mul] at hh
  rw [Measure.map_apply hbase hU] at hh
  calc
    _ = reference*(reference⁻¹*μ {z | base z∈U}) := by
      rw [←mul_assoc,ENNReal.mul_inv_cancel hzero htop,one_mul]
    _ ≤ reference*(C*volume U) := mul_le_mul' le_rfl hh
    _ = _ := by ring

section Prepared
variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
include hpure hd hp

/-- A physical parent moving-band numerator in exactly the unsheared
packet coordinates and full original assignment units. -/
theorem Native.PreparedAngularPath.parent_unsheared_band_mass_cap
    (old : Fin p.C) (hr : 0 ≤ p.r (p.lev old)) (hrL : p.r (p.lev old) ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z∈p.F old)
    {dimension f₀ error : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r-f₀-dimension*r| ≤ error)
    (center : EuclideanSpace ℝ (Fin 3) → ℝ) (hcenter : Measurable center)
    {width : ℝ} (hwidth : 0 < width)
    (hresolved : d.N k^(-(d.L-p.r (p.lev old))) ≤ 4*width)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    μ {z | unshearedPacketBase p old z∈U ∧
      |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
        center (unshearedPacketBase p old z)| ≤ width} ≤
      ENNReal.ofReal ((64*(max p.κ (d.K k))^2*p.κ*4^dimension*
        d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*width^dimension)*
        (ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹)*d.ν k (p.γ old) (p.A old))*volume U := by
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hmass : d.ν k (p.γ old) (p.A old) ≠ 0 := (hp.assignment_mass_pos hN old).ne'
  have hmassTop : d.ν k (p.γ old) (p.A old) ≠ ⊤ :=
    ne_of_lt ((hp.assignment_mass_bounds hN old).2.trans_lt ENNReal.ofReal_lt_top)
  let band := {z | |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
    center (unshearedPacketBase p old z)| ≤ width}
  have hband : MeasurableSet band := measurableSet_le
    ((measurable_physicalParentSignal _ _ _ _).sub
      (hcenter.comp (measurable_unshearedPacketBase p old))).abs measurable_const
  have hcap := Q.parent_unsheared_moving_band_all_widths hpure hd hp old hr hrL μ hμ
    hbase hF hdim hprofile center hcenter hwidth hresolved
  have hh := original_mass_of_normalized_base_cap (μ.restrict band)
    (unshearedPacketBase p old) (measurable_unshearedPacketBase p old)
    (mul_ne_zero hmass (by positivity)) (ENNReal.mul_ne_top hmassTop ENNReal.ofReal_ne_top)
    hcap U hU
  change (μ.restrict band) ((unshearedPacketBase p old) ⁻¹' U) ≤ _ at hh
  rw [Measure.restrict_apply ((measurable_unshearedPacketBase p old) hU)] at hh
  have hset : ((unshearedPacketBase p old) ⁻¹' U)∩band =
      {z | unshearedPacketBase p old z∈U ∧
        |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
          center (unshearedPacketBase p old z)| ≤ width} := rfl
  rw [hset] at hh
  simpa only [mul_comm (d.ν k (p.γ old) (p.A old))] using hh

end Prepared
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
