-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentSignalCap, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentSignalCap.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentSignalCap.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedOldBase
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentSignalFacts
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PreparedSourceCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AffineCoordinates
import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry

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

/-- A physical parent band has the genuine original continuous base cap. -/
theorem Native.PreparedAngularPath.parent_signal_raw_base_cap
    (old : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old)) (center : ℝ)
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z∈p.F old)
    (hband : ∀ᵐ z ∂μ,
      |MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old))-center| ≤
        max p.κ (d.K k)*δ (d.N k) r') :
    μ.map originalPhysicalBase ≤
      (ENNReal.ofReal (d.N k^(-d.f r'+τ+ε))*
        ENNReal.ofReal (64*(max p.κ (d.K k))^2)) • volume := by
  let K := max p.κ (d.K k)
  have hK : 1 ≤ K := hp.1.trans (le_max_left _ _)
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hDK : 0 < d.K k := zero_lt_one.trans_le ((hd.2.2.1).1 k)
  have hDKK : d.K k ≤ K := le_max_right _ _
  have hNk : 0 < d.N k := by linarith [hd.1 k]
  have hNk1 : 1 ≤ d.N k := by linarith [hd.1 k]
  have ha : 0 < δ (d.N k) r' := by unfold δ; positivity
  obtain ⟨nt,-,hδ⟩ := Submission.Obl.k4_horizon_chart_assembly.exists_time_partition hNk1 hr'
  have ha1 : δ (d.N k) r' ≤ 1 := by
    rw [show δ (d.N k) r'=((2:ℝ)^nt)⁻¹ from hδ]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  obtain ⟨hB,hP,hwhole,hlower⟩ := hd.parent_signal_data k (p.γ old)
  have hwholeProd := (Measure.quasiMeasurePreserving_fst
    (μ:=d.ν k (p.γ old)) (ν:=(volume:Measure ℝ))).ae hwhole
  have hμProd : μ ≤ (d.ν k (p.γ old)).prod volume := hμ.trans Measure.restrict_le_self
  have htypical := hpure (p.γ old) μ hμ hbase r' hr' hr'L
  have hgood : ∀ᵐ z ∂μ, z.2∈Icc (0:ℝ) 1 ∧ ‖y z.1 z.2‖ ≤ K ∧
      |MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old))-center| ≤ K*δ (d.N k) r' ∧
      |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 (d.P k (p.γ old)))| ≤ K*d.B k (p.γ old) ∧
      |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (d.P k (p.γ old))))| ≤
        K*(d.B k (p.γ old))^2/δ (d.N k) r' ∧
      d.B k (p.γ old)/K ≤
        |MvPolynomial.eval (xp z.1 z.2) (MvPolynomial.pderiv 3 (d.P k (p.γ old)))| ∧
      d.g k (p.γ old) r' (obs (d.B k (p.γ old)) (δ (d.N k) r') z) ≤
        ENNReal.ofReal (d.N k^(-d.f r'+τ+ε)) := by
    filter_upwards [(ae_mono hμProd) hwholeProd,(ae_mono hμ) hlower,hF,hband,htypical]
      with z hzWhole hzLower hzF hzBand hzTypical
    have ht := path_packet_time_unit hp old hzF
    have hw := hzWhole z.2 ht
    refine ⟨ht,?_,hzBand,?_,?_,?_,hzTypical⟩
    · exact ((le_add_of_nonneg_right (norm_nonneg (v z.1))).trans hw.1).trans hDKK
    · exact hw.2.2.1.trans (mul_le_mul_of_nonneg_right hDKK hB.le)
    · apply hw.2.2.2.trans
      apply (mul_le_mul_of_nonneg_right hDKK (sq_nonneg _)).trans
      apply (le_div_iff₀ ha).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ha1 (by positivity : 0 ≤ K*(d.B k (p.γ old))^2)
    · exact (show d.B k (p.γ old)/K ≤ d.B k (p.γ old)/d.K k by gcongr).trans hzLower
  have hlaw := hd.2.2.2.2.2.2.2.2.2.1 k (p.γ old) r' hr' hr'L
  have hcap := k4_uncapped_native_capping.UWE.native_signal_band_base_cap
    (d.μ k (p.γ old)) μ hμ hK hB ha (d.P k (p.γ old)) hP center
    (d.g k (p.γ old) r') hlaw.1 hlaw.2 _ hgood
  exact hcap

/-- A band of the ORIGINAL physical parent P has the same continuous
pure cap in full old assignment units. This uses P's genuine source
bounds and current derivative floor; the arbitrary old test R is not
substituted for P. -/
theorem Native.PreparedAngularPath.parent_signal_cap
    (old : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old)) (center : ℝ)
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z∈p.F old)
    (hband : ∀ᵐ z ∂μ,
      |MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old))-center| ≤
        max p.κ (d.K k)*δ (d.N k) r') :
    (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹))⁻¹ •
      μ.map (packetBase p old) ≤
      ((ENNReal.ofReal (d.N k^(-d.f r'+τ+ε))*
        ENNReal.ofReal (64*(max p.κ (d.K k))^2))*
        ENNReal.ofReal (p.κ*d.N k^d.f (p.r (p.lev old)))) • volume := by
  have hNk : 0 < d.N k := by linarith [hd.1 k]
  have hcap := Q.parent_signal_raw_base_cap hpure hd hp old r' hr' hr'L
    μ hμ center hbase hF hband
  have hD : (p.Q old).det ≠ 0 := (hp.2.2.2.2.2.2.2 old).2.2.1
  exact base_cap_in_old_packet_units μ originalPhysicalBase
    (by unfold originalPhysicalBase xp; fun_prop) (nativeOldBaseFrame p old)
    (by change 0 < ((2:ℝ)^p.T (p.lev old))⁻¹; positivity) hD hNk
    (zero_lt_one.trans_le hp.1) (d.f (p.r (p.lev old)))
    (d.ν k (p.γ old) (p.A old)) _ (hp.assignment_mass_bounds hNk old).1 hcap

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
