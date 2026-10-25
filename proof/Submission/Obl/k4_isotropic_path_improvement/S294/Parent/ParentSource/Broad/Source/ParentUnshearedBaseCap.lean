-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentUnshearedBaseCap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentUnshearedBaseCap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentUnshearedBaseCap.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentUnshearedBandCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedCapNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open MeasureTheory Set Native
open scoped ENNReal
noncomputable section

section Prepared
variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
include hpure hd hp

/-- The whole original old packet has an unsheared continuous base cap.
Its native path test supplies only a whole-base ceiling, independent of
which physical-parent signal band is later selected. -/
theorem Native.PreparedAngularPath.unsheared_old_base_cap
    (old : Fin p.C) (hr : 0 ≤ p.r (p.lev old)) (hrL : p.r (p.lev old) ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z∈p.F old) :
    (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹))⁻¹ •
      μ.map (unshearedPacketBase p old) ≤
      ENNReal.ofReal (64*(max p.κ (d.K k))^2*p.κ*
        d.N k^(τ+(2*δ₀*d.L)+ε)) • volume := by
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hB := (hd.parent_signal_data k (p.γ old)).1
  have hg := hd.2.2.2.2.2.2.2.2.2.1 k (p.γ old) (p.r (p.lev old)) hr hrL
  have hfull := (Measure.quasiMeasurePreserving_fst
    (μ:=d.ν k (p.γ old)) (ν:=(volume:Measure ℝ))).ae (hd.native_bounds k (p.γ old))
  have hμfull : μ ≤ (d.ν k (p.γ old)).prod volume := hμ.trans Measure.restrict_le_self
  have hy : ∀ᵐ z ∂μ, ‖y z.1 z.2‖ ≤ max p.κ (d.K k) := by
    filter_upwards [(ae_mono hμfull) hfull,hF] with z hz hzF
    exact ((le_add_of_nonneg_right (norm_nonneg (v z.1))).trans
      (hz z.2 (path_packet_time_unit hp old hzF))).trans (le_max_right _ _)
  have hraw := path_packet_native_base_cap hp old (le_max_left _ _) hB μ hμ
    (d.g k (p.γ old) (p.r (p.lev old))) hg.1 hg.2 _ hF hy
    (hpure _ μ hμ hbase _ hr hrL)
  have hh := unsheared_base_cap_in_old_packet_units hp (by linarith [hd.1 k]) old μ _ hraw
  rw [unsheared_cap_coefficient_shift hN hκ] at hh
  apply hh.trans
  have hc := pure_cap_coefficient (N:=d.N k) (κ:=p.κ) (K:=d.K k)
    (fOld:=d.f (p.r (p.lev old))) (fNew:=d.f (p.r (p.lev old)))
    (d₁:=0) (step:=0) (error:=0) (τ:=τ+2*δ₀*d.L) (ε:=ε)
    (by linarith [hd.1 k]) hκ (by simp)
  intro U
  exact mul_le_mul' (by simpa using hc) le_rfl

/-- The physical-parent moving-band profile cap in unsheared old units. -/
theorem Native.PreparedAngularPath.parent_unsheared_moving_signal_profile_cap
    (old : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z∈p.F old)
    (center : EuclideanSpace ℝ (Fin 3) → ℝ) (hcenter : Measurable center)
    {width : ℝ} (hwidth : 0 < width)
    (hresolution : δ (d.N k) (p.r (p.lev old))*(2*width) ≤
      max p.κ (d.K k)*δ (d.N k) r')
    {dimension f₀ error : ℝ}
    (hprofile : |d.f (p.r (p.lev old))-f₀-dimension*p.r (p.lev old)| ≤ error)
    (hprofile' : |d.f r'-f₀-dimension*r'| ≤ error) :
    (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹))⁻¹ •
      (μ.restrict {z | |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
        center (unshearedPacketBase p old z)| ≤ width}).map (unshearedPacketBase p old) ≤
      ENNReal.ofReal (64*(max p.κ (d.K k))^2*p.κ*
        d.N k^(-dimension*(r'-p.r (p.lev old))+2*error+(τ+2*δ₀*d.L)+ε)) • volume := by
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hh := Q.parent_unsheared_moving_signal_band_cap hpure hd hp old r' hr' hr'L
    μ hμ hbase hF center hcenter hwidth hresolution
  rw [unsheared_cap_coefficient_shift hN hκ] at hh
  apply hh.trans
  have hc := pure_cap_coefficient (N:=d.N k) (κ:=p.κ) (K:=d.K k) (τ:=τ+2*δ₀*d.L) (ε:=ε)
    (d₁:=dimension) (step:=r'-p.r (p.lev old))
    (by linarith [hd.1 k]) hκ (profile_increment_for_cap hprofile hprofile')
  intro U
  exact mul_le_mul' hc le_rfl

end Prepared
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
