-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorSignalCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AncestorSignalCaps.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentUnshearedBaseCap

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
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

/-- The ACTUAL fixed ancestor test has the original continuous base cap
at every finer signal width. This uses its native chart bounds and
original prepared density, never the physical-P jet hypotheses. -/
theorem Native.PreparedAngularPath.ancestor_signal_raw_base_cap
    (root : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev root)))
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ root)) (center : ℝ)
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ root)) (hF : ∀ᵐ z ∂μ, z∈p.F root)
    (hband : ∀ᵐ z ∂μ, |MvPolynomial.eval (xp z.1 z.2) (p.R root)-center| ≤
      max p.κ (d.K k)*δ (d.N k) r') :
    μ.map originalPhysicalBase ≤
      (ENNReal.ofReal (d.N k^(-d.f r'+τ+ε))*
        ENNReal.ofReal (64*(max p.κ (d.K k))^2)) • volume := by
  let K := max p.κ (d.K k)
  have hB := (hd.parent_signal_data k (p.γ root)).1
  have hg := hd.2.2.2.2.2.2.2.2.2.1 k (p.γ root) r' hr' hr'L
  have hwhole := (Measure.quasiMeasurePreserving_fst
    (μ:=d.ν k (p.γ root)) (ν:=(volume:Measure ℝ))).ae (hd.native_bounds k (p.γ root))
  have hμfull : μ ≤ (d.ν k (p.γ root)).prod volume := hμ.trans Measure.restrict_le_self
  have hy : ∀ᵐ z ∂μ, ‖y z.1 z.2‖ ≤ K := by
    filter_upwards [(ae_mono hμfull) hwhole,hF] with z hz hzF
    exact ((le_add_of_nonneg_right (norm_nonneg (v z.1))).trans
      (hz z.2 (path_packet_time_unit hp root hzF))).trans (le_max_right _ _)
  have hraw := path_packet_native_signal_cap hp root (le_max_left _ _) hB
    (by unfold δ; positivity) hscale μ hμ (d.g k (p.γ root) r') hg.1 hg.2 _ center
    hF hy hband (hpure _ μ hμ hbase r' hr' hr'L)
  exact hraw

/-- The ancestor signal's cap is expressed in the later child's literal
unsheared coordinates and FULL original child reference. No ancestor
assignment normalization is substituted in the output. -/
theorem Native.PreparedAngularPath.ancestor_signal_child_base_cap
    (root child : Fin p.C) (_hworld : p.γ child=p.γ root)
    (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev root)))
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ root)) (center : ℝ)
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ root)) (hF : ∀ᵐ z ∂μ, z∈p.F root)
    (hband : ∀ᵐ z ∂μ, |MvPolynomial.eval (xp z.1 z.2) (p.R root)-center| ≤
      max p.κ (d.K k)*δ (d.N k) r') :
    (d.ν k (p.γ child) (p.A child)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹))⁻¹ •
      μ.map (unshearedPacketBase p child) ≤
      ((ENNReal.ofReal (d.N k^(-d.f r'+τ+ε))*
        ENNReal.ofReal (64*(max p.κ (d.K k))^2))*
        ENNReal.ofReal ((p.κ*d.N k^(2*δ₀*d.L))*d.N k^d.f (p.r (p.lev child)))) • volume := by
  exact unsheared_base_cap_in_old_packet_units hp (by linarith [hd.1 k]) child μ _
    (Q.ancestor_signal_raw_base_cap hpure hd hp root r' hr' hr'L hscale μ hμ center hbase hF hband)

/-- Arbitrary measurable moving centers are allowed for the fixed
ancestor signal in CHILD thickness units. The same original reference
and original prepared density remain fixed for every center. -/
theorem Native.PreparedAngularPath.ancestor_moving_signal_child_band_cap
    (root child : Fin p.C) (hworld : p.γ child=p.γ root)
    (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev root)))
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ root))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ root)) (hF : ∀ᵐ z ∂μ, z∈p.F root)
    (center : EuclideanSpace ℝ (Fin 3) → ℝ) (hcenter : Measurable center)
    {width : ℝ} (hwidth : 0 < width)
    (hresolution : δ (d.N k) (p.r (p.lev child))*(2*width) ≤
      max p.κ (d.K k)*δ (d.N k) r') :
    (d.ν k (p.γ child) (p.A child)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹))⁻¹ •
      (μ.restrict {z | |physicalParentSignal (d.N k) p child (p.R root) z-
        center (unshearedPacketBase p child z)| ≤ width}).map (unshearedPacketBase p child) ≤
      ((ENNReal.ofReal (d.N k^(-d.f r'+τ+ε))*
        ENNReal.ofReal (64*(max p.κ (d.K k))^2))*
        ENNReal.ofReal ((p.κ*d.N k^(2*δ₀*d.L))*d.N k^d.f (p.r (p.lev child)))) • volume := by
  let budget := (d.ν k (p.γ child) (p.A child)*
    ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹))⁻¹
  have ha : 0 < δ (d.N k) (p.r (p.lev child)) := by unfold δ; positivity
  have hconst (a : ℝ) :
      ((budget • μ).restrict {z | |physicalParentSignal (d.N k) p child (p.R root) z-a| ≤ 2*width}).map
        (unshearedPacketBase p child) ≤
      ((ENNReal.ofReal (d.N k^(-d.f r'+τ+ε))*
        ENNReal.ofReal (64*(max p.κ (d.K k))^2))*
        ENNReal.ofReal ((p.κ*d.N k^(2*δ₀*d.L))*d.N k^d.f (p.r (p.lev child)))) • volume := by
    let band := {z | |physicalParentSignal (d.N k) p child (p.R root) z-a| ≤ 2*width}
    have hbandm : MeasurableSet band :=
      measurableSet_le ((measurable_physicalParentSignal (d.N k) p child (p.R root)).sub_const a).abs measurable_const
    have hsub : μ.restrict band ≤ μ := Measure.restrict_le_self
    have hband : ∀ᵐ z ∂μ.restrict band,
        |MvPolynomial.eval (xp z.1 z.2) (p.R root)-δ (d.N k) (p.r (p.lev child))*a| ≤
          max p.κ (d.K k)*δ (d.N k) r' := by
      filter_upwards [ae_restrict_mem hbandm] with z hz
      have heq : MvPolynomial.eval (xp z.1 z.2) (p.R root)=
          δ (d.N k) (p.r (p.lev child))*physicalParentSignal (d.N k) p child (p.R root) z := by
        change MvPolynomial.eval (xp z.1 z.2) (p.R root)=
          δ (d.N k) (p.r (p.lev child))*((δ (d.N k) (p.r (p.lev child)))⁻¹*
            MvPolynomial.eval (xp z.1 z.2) (p.R root))
        rw [←mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]
      calc
        _ = δ (d.N k) (p.r (p.lev child))*|physicalParentSignal (d.N k) p child (p.R root) z-a| := by
          rw [heq,←mul_sub,abs_mul,abs_of_pos ha]
        _ ≤ δ (d.N k) (p.r (p.lev child))*(2*width) := mul_le_mul_of_nonneg_left hz ha.le
        _ ≤ _ := hresolution
    have hh := Q.ancestor_signal_child_base_cap hpure hd hp root child hworld r' hr' hr'L
      hscale (μ.restrict band) (hsub.trans hμ) (δ (d.N k) (p.r (p.lev child))*a)
      ((ae_mono hsub) hbase) ((ae_mono hsub) hF) hband
    change budget • (μ.restrict band).map (unshearedPacketBase p child) ≤ _ at hh
    rw [Measure.restrict_smul,Measure.map_smul _ (measurable_unshearedPacketBase p child).aemeasurable]
    exact hh
  have hh := moving_band_base_cap (budget • μ) volume (unshearedPacketBase p child)
    (measurable_unshearedPacketBase p child) (physicalParentSignal (d.N k) p child (p.R root))
    center hcenter hwidth _ hconst
  rw [Measure.restrict_smul,Measure.map_smul _ (measurable_unshearedPacketBase p child).aemeasurable] at hh
  exact hh

/-- The moving ancestor-signal cap has the original profile exponent
at the later child's thickness, with only the original profile errors. -/
theorem Native.PreparedAngularPath.ancestor_moving_signal_child_profile_cap
    (root child : Fin p.C) (hworld : p.γ child=p.γ root)
    (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (hscale : δ (d.N k) r' ≤ δ (d.N k) (p.r (p.lev root)))
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ root))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ root)) (hF : ∀ᵐ z ∂μ, z∈p.F root)
    (center : EuclideanSpace ℝ (Fin 3) → ℝ) (hcenter : Measurable center)
    {width : ℝ} (hwidth : 0 < width)
    (hresolution : δ (d.N k) (p.r (p.lev child))*(2*width) ≤
      max p.κ (d.K k)*δ (d.N k) r')
    {dimension f₀ error : ℝ}
    (hprofile : |d.f (p.r (p.lev child))-f₀-dimension*p.r (p.lev child)| ≤ error)
    (hprofile' : |d.f r'-f₀-dimension*r'| ≤ error) :
    (d.ν k (p.γ child) (p.A child)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹))⁻¹ •
      (μ.restrict {z | |physicalParentSignal (d.N k) p child (p.R root) z-
        center (unshearedPacketBase p child z)| ≤ width}).map (unshearedPacketBase p child) ≤
      ENNReal.ofReal (64*(max p.κ (d.K k))^2*p.κ*
        d.N k^(-dimension*(r'-p.r (p.lev child))+2*error+(τ+2*δ₀*d.L)+ε)) • volume := by
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hh := Q.ancestor_moving_signal_child_band_cap hpure hd hp root child hworld
    r' hr' hr'L hscale μ hμ hbase hF center hcenter hwidth hresolution
  rw [unsheared_cap_coefficient_shift hN hκ] at hh
  apply hh.trans
  have hc := pure_cap_coefficient (N:=d.N k) (κ:=p.κ) (K:=d.K k) (τ:=τ+2*δ₀*d.L) (ε:=ε)
    (d₁:=dimension) (step:=r'-p.r (p.lev child))
    (by linarith [hd.1 k]) hκ (profile_increment_for_cap hprofile hprofile')
  intro U
  exact mul_le_mul' hc le_rfl

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
