-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorClockBandMass, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalBandWidths
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalCapMass
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRows

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

/-- Return the genuine fixed-ancestor moving-band cap to literal
original mass units, retaining the FULL later-child reference. -/
theorem Native.PreparedAngularPath.ancestor_child_band_mass_cap
    (root child : Fin p.C) (hworld : p.γ child=p.γ root)
    (hscale : δ (d.N k) (p.r (p.lev child)) ≤ δ (d.N k) (p.r (p.lev root)))
    (hr : 0 ≤ p.r (p.lev child)) (hrL : p.r (p.lev child) ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ root))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ root))
    (hFroot : ∀ᵐ z ∂μ, z∈p.F root) (hFchild : ∀ᵐ z ∂μ, z∈p.F child)
    {dimension f₀ error : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r-f₀-dimension*r| ≤ error)
    (center : EuclideanSpace ℝ (Fin 3) → ℝ) (hcenter : Measurable center)
    {width : ℝ} (hwidth : 0 < width)
    (hresolved : d.N k^(-(d.L-p.r (p.lev child))) ≤ 4*width)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    μ {z | unshearedPacketBase p child z∈U ∧
      |physicalParentSignal (d.N k) p child (p.R root) z-center (unshearedPacketBase p child z)| ≤ width} ≤
      ENNReal.ofReal ((64*(max p.κ (d.K k))^2*p.κ*4^dimension*
        d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*width^dimension)*
        (d.ν k (p.γ child) (p.A child)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹))*volume U := by
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hmass : d.ν k (p.γ child) (p.A child)≠0 := (hp.assignment_mass_pos hN child).ne'
  have hmassTop : d.ν k (p.γ child) (p.A child)≠⊤ :=
    ne_of_lt ((hp.assignment_mass_bounds hN child).2.trans_lt ENNReal.ofReal_lt_top)
  let band := {z | |physicalParentSignal (d.N k) p child (p.R root) z-
    center (unshearedPacketBase p child z)| ≤ width}
  have hcap := Q.ancestor_moving_signal_child_all_widths hpure hd hp root child hworld hscale
    hr hrL μ hμ hbase hFroot hFchild hdim hprofile center hcenter hwidth hresolved
  have hh := original_mass_of_normalized_base_cap (μ.restrict band)
    (unshearedPacketBase p child) (measurable_unshearedPacketBase p child)
    (mul_ne_zero hmass (by positivity)) (ENNReal.mul_ne_top hmassTop ENNReal.ofReal_ne_top)
    hcap U hU
  change (μ.restrict band) ((unshearedPacketBase p child) ⁻¹' U) ≤ _ at hh
  rw [Measure.restrict_apply ((measurable_unshearedPacketBase p child) hU)] at hh
  exact hh

/-- On the ancestor's own graph clock there is no absolute aspect
factor: the exact graph-stage band coefficient is the original pure cap. -/
theorem Native.PreparedAngularPath.ancestor_clock_band_mass_cap
    (root : Fin p.C) (hr : 0 ≤ p.r (p.lev root)) (hrL : p.r (p.lev root) ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ root))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ root)) (hFroot : ∀ᵐ z ∂μ, z∈p.F root)
    {dimension f₀ error : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r-f₀-dimension*r| ≤ error)
    (center : EuclideanSpace ℝ (Fin 3) → ℝ) (hcenter : Measurable center)
    {width : ℝ} (hwidth : 0 < width)
    (hresolved : d.N k^(-(d.L-p.r (p.lev root))) ≤ 4*width)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    μ {z | unshearedPacketBase p root z∈U ∧
      |clockParentSignal p root (SignalGraph.ancestorSignal (d.N k) p root) z-
        center (unshearedPacketBase p root z)| ≤ width} ≤
      ENNReal.ofReal ((64*(max p.κ (d.K k))^2*p.κ*4^dimension*
        d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*width^dimension)*
        (d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹))*volume U := by
  have heq : clockParentSignal p root (SignalGraph.ancestorSignal (d.N k) p root)=
      physicalParentSignal (d.N k) p root (p.R root) := by
    ext z
    simpa only [one_mul] using (SignalGraph.ancestorSignal_clock (d.N k) p root z).symm
  rw [heq]
  exact Q.ancestor_child_band_mass_cap hpure hd hp root root rfl le_rfl hr hrL
    μ hμ hbase hFroot hFroot hdim hprofile center hcenter hwidth hresolved U hU

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
