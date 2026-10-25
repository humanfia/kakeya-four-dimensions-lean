-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentUnshearedBandCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentUnshearedBandCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentUnshearedBandCaps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentMovingBandCap

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

/-- The parent-P band cap in the literal unsheared old coordinates. -/
theorem Native.PreparedAngularPath.parent_unsheared_signal_cap
    (old : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old)) (center : ℝ)
    (hbase : ∀ᵐ z ∂μ, z∈Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z∈p.F old)
    (hband : ∀ᵐ z ∂μ,
      |MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old))-center| ≤
        max p.κ (d.K k)*δ (d.N k) r') :
    (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹))⁻¹ •
      μ.map (unshearedPacketBase p old) ≤
      ((ENNReal.ofReal (d.N k^(-d.f r'+τ+ε))*
        ENNReal.ofReal (64*(max p.κ (d.K k))^2))*
        ENNReal.ofReal ((p.κ*d.N k^(2*δ₀*d.L))*d.N k^d.f (p.r (p.lev old)))) • volume := by
  exact unsheared_base_cap_in_old_packet_units hp (by linarith [hd.1 k]) old μ _
    (Q.parent_signal_raw_base_cap hpure hd hp old r' hr' hr'L μ hμ center hbase hF hband)

/-- The ORIGINAL physical parent pure cap controls a band around any measurable function
of the exact old base, including a polynomial potential. The signal is the physical parent from pb. Its denominator
is the full original assignment mass and clock. No derivative or range
bound on the moving center is required. -/
theorem Native.PreparedAngularPath.parent_unsheared_moving_signal_band_cap
    (old : Fin p.C) (r' : ℝ) (hr' : 0 ≤ r') (hr'L : r' ≤ d.L)
    (μ : Measure Ev) (hμ : μ ≤ d.μ k (p.γ old))
    (hbase : ∀ᵐ z ∂μ, z ∈ Q.base (p.γ old)) (hF : ∀ᵐ z ∂μ, z ∈ p.F old)
    (center : EuclideanSpace ℝ (Fin 3) → ℝ) (hcenter : Measurable center)
    {width : ℝ} (hwidth : 0 < width)
    (hresolution : δ (d.N k) (p.r (p.lev old)) * (2*width) ≤
      max p.κ (d.K k) * δ (d.N k) r') :
    (d.ν k (p.γ old) (p.A old) *
      ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))⁻¹ •
        (μ.restrict {z | |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-center (unshearedPacketBase p old z)| ≤ width}).map
          (unshearedPacketBase p old) ≤
      ((ENNReal.ofReal (d.N k ^ (-d.f r' + τ + ε)) *
        ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
        ENNReal.ofReal ((p.κ*d.N k^(2*δ₀*d.L)) * d.N k ^ d.f (p.r (p.lev old)))) • volume := by
  let budget := (d.ν k (p.γ old) (p.A old) *
    ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev old))⁻¹))⁻¹
  have hδ : 0 < δ (d.N k) (p.r (p.lev old)) := by unfold δ; positivity
  have hconst (a : ℝ) :
      ((budget • μ).restrict {z | |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-a| ≤ 2*width}).map
        (unshearedPacketBase p old) ≤
      ((ENNReal.ofReal (d.N k ^ (-d.f r' + τ + ε)) *
        ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
        ENNReal.ofReal ((p.κ*d.N k^(2*δ₀*d.L)) * d.N k ^ d.f (p.r (p.lev old)))) • volume := by
    let band := {z | |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-a| ≤ 2*width}
    have hbandm : MeasurableSet band :=
      measurableSet_le ((measurable_physicalParentSignal (d.N k) p old (d.P k (p.γ old))).sub_const a).abs measurable_const
    have hsub : μ.restrict band ≤ μ := Measure.restrict_le_self
    have hband : ∀ᵐ z ∂μ.restrict band,
        |MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old))-δ (d.N k) (p.r (p.lev old))*a| ≤
          max p.κ (d.K k)*δ (d.N k) r' := by
      filter_upwards [ae_restrict_mem hbandm] with z hz
      have hid : MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old)) =
          δ (d.N k) (p.r (p.lev old))*physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z := by
        change MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old)) =
          δ (d.N k) (p.r (p.lev old)) * ((δ (d.N k) (p.r (p.lev old)))⁻¹ *
            MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old)))
        rw [← mul_assoc,mul_inv_cancel₀ hδ.ne',one_mul]
      calc
        _ = δ (d.N k) (p.r (p.lev old))*|physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-a| := by
          rw [hid,←mul_sub,abs_mul,abs_of_pos hδ]
        _ ≤ δ (d.N k) (p.r (p.lev old))*(2*width) :=
          mul_le_mul_of_nonneg_left hz hδ.le
        _ ≤ _ := hresolution
    have hh := Q.parent_unsheared_signal_cap hpure hd hp old r' hr' hr'L
      (μ.restrict band) (hsub.trans hμ) (δ (d.N k) (p.r (p.lev old))*a)
      ((ae_mono hsub) hbase) ((ae_mono hsub) hF) hband
    change budget • (μ.restrict band).map (unshearedPacketBase p old) ≤ _ at hh
    rw [Measure.restrict_smul,Measure.map_smul _ (measurable_unshearedPacketBase p old).aemeasurable]
    exact hh
  have hh := moving_band_base_cap (budget • μ) volume (unshearedPacketBase p old)
    (measurable_unshearedPacketBase p old) (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) center hcenter hwidth _ hconst
  rw [Measure.restrict_smul,Measure.map_smul _ (measurable_unshearedPacketBase p old).aemeasurable] at hh
  exact hh


end Prepared

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
