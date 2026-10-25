-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorSignalBandWidths, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AncestorSignalBandWidths.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
/- The source cap proof is adapted from the same tree, o287's
ParentSource/Broad/Source/ParentUnshearedBandWidths.lean, with the
fixed ancestor signal supplied by AncestorSignalCaps. Earlier credits follow. -/
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentUnshearedBandWidths.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalPowerGridCaps
import Submission.Obl.k4_narrow_projected_row_parents.MeshExponent

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

/-- Genuine original pure caps for the FIXED ancestor R in later CHILD
coordinates, at every width resolved by the remaining original depth.
No query-depth or conditional-denominator oracle is supplied. -/
theorem Native.PreparedAngularPath.ancestor_moving_signal_child_all_widths
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
    (hresolved : d.N k^(-(d.L-p.r (p.lev child))) ≤ 4*width) :
    (d.ν k (p.γ child) (p.A child)*
      ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹))⁻¹ •
        (μ.restrict {z | |physicalParentSignal (d.N k) p child (p.R root) z-center (unshearedPacketBase p child z)| ≤ width}).map
          (unshearedPacketBase p child) ≤
      ENNReal.ofReal ((64*(max p.κ (d.K k))^2*p.κ*4^dimension*
        d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*width^dimension) • volume := by
  have hN : 1 < d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans hN
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have herror : 0 ≤ error := (abs_nonneg _).trans (hprofile _ hr hrL)
  by_cases hsmall : 4*width ≤ 1
  · obtain ⟨step,hstep,hstepL,hpow⟩ :=
      Submission.Obl.k4_narrow_projected_row_parents.exists_mesh_exponent
        (a := 0) (b := d.L-p.r (p.lev child)) hN hresolved (by simpa using hsmall)
    have hdepth : p.r (p.lev child)+step ≤ d.L := by linarith
    have hhalf := dyadic_relative_half_width hNp (p.r (p.lev child)) step
    rw [hpow] at hhalf
    have hresolution : δ (d.N k) (p.r (p.lev child))*(2*width) ≤
        max p.κ (d.K k)*δ (d.N k) (p.r (p.lev child)+step) := by
      calc
        _ = δ (d.N k) (p.r (p.lev child))*(4*width)/2 := by ring
        _ ≤ δ (d.N k) (p.r (p.lev child)+step) := hhalf
        _ ≤ _ := le_mul_of_one_le_left (by unfold δ; positivity)
          (hp.1.trans (le_max_left _ _))
    have hqueryScale : δ (d.N k) (p.r (p.lev child)+step) ≤ δ (d.N k) (p.r (p.lev root)) :=
      (Broad.δ_antitone hN.le (le_add_of_nonneg_right hstep)).trans hscale
    have hh := Q.ancestor_moving_signal_child_profile_cap hpure hd hp root child hworld
      (p.r (p.lev child)+step) (add_nonneg hr hstep) hdepth hqueryScale
      μ hμ hbase hFroot center hcenter hwidth hresolution
      (hprofile _ hr hrL) (hprofile _ (add_nonneg hr hstep) hdepth)
    have he : -dimension*((p.r (p.lev child)+step)-p.r (p.lev child))+2*error+(τ+2*δ₀*d.L)+ε =
        (2*error+(τ+2*δ₀*d.L)+ε)+(-step)*dimension := by ring
    have hcoefficient : 64*(max p.κ (d.K k))^2*p.κ*
        d.N k^(-dimension*((p.r (p.lev child)+step)-p.r (p.lev child))+2*error+(τ+2*δ₀*d.L)+ε) =
        (64*(max p.κ (d.K k))^2*p.κ*4^dimension*d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*width^dimension := by
      rw [he,Real.rpow_add hNp,Real.rpow_mul hNp.le,hpow,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hwidth.le]
      ring
    rw [hcoefficient] at hh
    exact hh
  · have hmono := Measure.map_mono (μ := μ.restrict
        {z | |physicalParentSignal (d.N k) p child (p.R root) z-center (unshearedPacketBase p child z)| ≤ width})
      Measure.restrict_le_self (measurable_unshearedPacketBase p child)
    have hμchild : μ ≤ d.μ k (p.γ child) := by rw [hworld]; exact hμ
    have hbaseChild : ∀ᵐ z ∂μ, z∈Q.base (p.γ child) := by rw [hworld]; exact hbase
    have hwhole := Q.unsheared_old_base_cap hpure hd hp child hr hrL μ hμchild hbaseChild hFchild
    apply (le_trans (fun U => mul_le_mul' le_rfl (hmono U)) hwhole).trans
    have hfactor : 1 ≤ (4:ℝ)^dimension*width^dimension := by
      rw [←Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hwidth.le]
      exact Real.one_le_rpow (by linarith) hdim
    have hcoefficient : 64*(max p.κ (d.K k))^2*p.κ*d.N k^((τ+2*δ₀*d.L)+ε) ≤
        (64*(max p.κ (d.K k))^2*p.κ*4^dimension*d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*width^dimension := by
      calc
        _ ≤ 64*(max p.κ (d.K k))^2*p.κ*d.N k^(2*error+(τ+2*δ₀*d.L)+ε) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)) (by positivity)
        _ ≤ (64*(max p.κ (d.K k))^2*p.κ*d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*
            ((4:ℝ)^dimension*width^dimension) := le_mul_of_one_le_right (by positivity) hfactor
        _ = _ := by ring
    intro U
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hcoefficient) le_rfl

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
