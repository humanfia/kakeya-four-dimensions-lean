-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentUnshearedBandWidths, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentUnshearedBandWidths.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentUnshearedBandWidths.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentUnshearedBaseCap
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

/-- Uniform continuous PHYSICAL P moving-band caps in UNSHEARED old coordinates on every width resolved by the
remaining original depth interval. Only the original profile exponent
appears; the moving center has no degree or derivative cost. -/
theorem Native.PreparedAngularPath.parent_unsheared_moving_band_all_widths
    (old : Fin p.C) (hr : 0 ≤ p.r (p.lev old)) (hrL : p.r (p.lev old) ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old))
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z∈p.F old)
    {dimension f₀ error : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r-f₀-dimension*r| ≤ error)
    (center : EuclideanSpace ℝ (Fin 3) → ℝ) (hcenter : Measurable center)
    {width : ℝ} (hwidth : 0 < width)
    (hresolved : d.N k^(-(d.L-p.r (p.lev old))) ≤ 4*width) :
    (d.ν k (p.γ old) (p.A old)*
      ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹))⁻¹ •
        (μ.restrict {z | |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-center (unshearedPacketBase p old z)| ≤ width}).map
          (unshearedPacketBase p old) ≤
      ENNReal.ofReal ((64*(max p.κ (d.K k))^2*p.κ*4^dimension*
        d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*width^dimension) • volume := by
  have hN : 1 < d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans hN
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have herror : 0 ≤ error := (abs_nonneg _).trans (hprofile _ hr hrL)
  by_cases hsmall : 4*width ≤ 1
  · obtain ⟨step,hstep,hstepL,hpow⟩ :=
      Submission.Obl.k4_narrow_projected_row_parents.exists_mesh_exponent
        (a := 0) (b := d.L-p.r (p.lev old)) hN hresolved (by simpa using hsmall)
    have hdepth : p.r (p.lev old)+step ≤ d.L := by linarith
    have hhalf := dyadic_relative_half_width hNp (p.r (p.lev old)) step
    rw [hpow] at hhalf
    have hresolution : δ (d.N k) (p.r (p.lev old))*(2*width) ≤
        max p.κ (d.K k)*δ (d.N k) (p.r (p.lev old)+step) := by
      calc
        _ = δ (d.N k) (p.r (p.lev old))*(4*width)/2 := by ring
        _ ≤ δ (d.N k) (p.r (p.lev old)+step) := hhalf
        _ ≤ _ := le_mul_of_one_le_left (by unfold δ; positivity)
          (hp.1.trans (le_max_left _ _))
    have hh := Q.parent_unsheared_moving_signal_profile_cap hpure hd hp old
      (p.r (p.lev old)+step) (add_nonneg hr hstep) hdepth
      μ hμ hbase hF center hcenter hwidth hresolution
      (hprofile _ hr hrL) (hprofile _ (add_nonneg hr hstep) hdepth)
    have he : -dimension*((p.r (p.lev old)+step)-p.r (p.lev old))+2*error+(τ+2*δ₀*d.L)+ε =
        (2*error+(τ+2*δ₀*d.L)+ε)+(-step)*dimension := by ring
    have hcoefficient : 64*(max p.κ (d.K k))^2*p.κ*
        d.N k^(-dimension*((p.r (p.lev old)+step)-p.r (p.lev old))+2*error+(τ+2*δ₀*d.L)+ε) =
        (64*(max p.κ (d.K k))^2*p.κ*4^dimension*d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*width^dimension := by
      rw [he,Real.rpow_add hNp,Real.rpow_mul hNp.le,hpow,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hwidth.le]
      ring
    rw [hcoefficient] at hh
    exact hh
  · have hmono := Measure.map_mono (μ := μ.restrict
        {z | |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-center (unshearedPacketBase p old z)| ≤ width})
      Measure.restrict_le_self (measurable_unshearedPacketBase p old)
    have hwhole := Q.unsheared_old_base_cap hpure hd hp old hr hrL μ hμ hbase hF
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
