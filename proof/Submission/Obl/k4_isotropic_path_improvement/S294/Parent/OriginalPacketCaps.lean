-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.OriginalPacketCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/OriginalPacketCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentUnshearedBandWidths

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace OriginalPacketCaps

/-- A ceiling in full-reference units returns to the original law by
multiplying by that same full reference. -/
theorem original_cap_of_normalized_map {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] (μ : Measure Ω) (targetMeasure : Measure Y)
    (f : Ω → Y) (hf : Measurable f) {ref C : ENNReal}
    (href : ref ≠ 0) (hreftop : ref ≠ ∞)
    (hcap : ref⁻¹ • μ.map f ≤ C • targetMeasure) (U : Set Y) (hU : MeasurableSet U) :
    μ (f ⁻¹' U) ≤ C * ref * targetMeasure U := by
  have hh := hcap U
  simp only [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf hU] at hh
  calc
    μ (f ⁻¹' U) = ref * (ref⁻¹ * μ (f ⁻¹' U)) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel href hreftop, one_mul]
    _ ≤ ref * (C * targetMeasure U) := mul_le_mul' le_rfl hh
    _ = C * ref * targetMeasure U := by ring

section Prepared

open ParentSource ParentSource.Native

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set ParentSource.Event} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- The actual original event has the literal unsheared base ceiling,
with its full assignment and original clock as reference. -/
theorem base_cap (old : Fin p.C) (hr : 0 ≤ p.r (p.lev old))
    (hrL : p.r (p.lev old) ≤ d.L)
    (current : Set ParentSource.Event) (hcurrent : MeasurableSet current)
    (hE : current ⊆ d.E k (p.γ old))
    (hbase : current ⊆ Q.base (p.γ old)) (hF : current ⊆ p.F old)
    (hA : d.ν k (p.γ old) (p.A old) ≠ 0)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    (((d.ν k (p.γ old)).prod volume).restrict current)
      {z | unshearedPacketBase p old z ∈ U} ≤
        ENNReal.ofReal (64*(max p.κ (d.K k))^2*p.κ*
          d.N k^(τ+2*δ₀*d.L+ε)) *
        (ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹)*d.ν k (p.γ old) (p.A old)) *
          volume U := by
  haveI : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  let μ := ((d.ν k (p.γ old)).prod volume).restrict current
  let ref := d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹)
  have hμ : μ ≤ d.μ k (p.γ old) := Measure.restrict_mono_set _ hE
  have hsource := ae_restrict_mem hcurrent (μ := (d.ν k (p.γ old)).prod volume)
  have hc := Q.unsheared_old_base_cap hpure hd hp old hr hrL μ hμ
    (hsource.mono (fun z hz => hbase hz)) (hsource.mono (fun z hz => hF hz))
  have href : ref ≠ 0 := mul_ne_zero hA (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have htop : ref ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hh := original_cap_of_normalized_map μ volume (unshearedPacketBase p old)
    (measurable_unshearedPacketBase p old) href htop hc U hU
  simpa only [μ, ref, Set.preimage, mul_comm (d.ν k (p.γ old) (p.A old))] using hh

/-- All resolved moving bands retain their original full-reference cap,
under the actual current law. The moving center may be any measurable
function of the literal unsheared base. -/
theorem moving_band_cap (old : Fin p.C) (hr : 0 ≤ p.r (p.lev old))
    (hrL : p.r (p.lev old) ≤ d.L)
    (current : Set ParentSource.Event) (hcurrent : MeasurableSet current)
    (hE : current ⊆ d.E k (p.γ old))
    (hbase : current ⊆ Q.base (p.γ old)) (hF : current ⊆ p.F old)
    (hA : d.ν k (p.γ old) (p.A old) ≠ 0)
    {dimension f₀ error width : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r-f₀-dimension*r| ≤ error)
    (hwidth : 0 < width) (hresolved : d.N k^(-(d.L-p.r (p.lev old))) ≤ 4*width)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U)
    (center : EuclideanSpace ℝ (Fin 3) → ℝ) (hcenter : Measurable center) :
    (((d.ν k (p.γ old)).prod volume).restrict current)
      {z | unshearedPacketBase p old z ∈ U ∧
        |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
          center (unshearedPacketBase p old z)| ≤ width} ≤
        ENNReal.ofReal ((64*(max p.κ (d.K k))^2*p.κ*4^dimension*
          d.N k^(2*error+(τ+2*δ₀*d.L)+ε))*width^dimension) *
        (ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹)*d.ν k (p.γ old) (p.A old)) *
          volume U := by
  haveI : IsProbabilityMeasure (d.ν k (p.γ old)) := (hd.weights k).2.2 _
  let μ := ((d.ν k (p.γ old)).prod volume).restrict current
  let ref := d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2 : ℝ)^p.T (p.lev old))⁻¹)
  let band := {z | |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
    center (unshearedPacketBase p old z)| ≤ width}
  have hμ : μ ≤ d.μ k (p.γ old) := Measure.restrict_mono_set _ hE
  have hsource := ae_restrict_mem hcurrent (μ := (d.ν k (p.γ old)).prod volume)
  have hc := Q.parent_unsheared_moving_band_all_widths hpure hd hp old hr hrL μ hμ
    (hsource.mono (fun z hz => hbase hz)) (hsource.mono (fun z hz => hF hz))
    hdim hprofile center hcenter hwidth hresolved
  have href : ref ≠ 0 := mul_ne_zero hA (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have htop : ref ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hh := original_cap_of_normalized_map (μ.restrict band) volume (unshearedPacketBase p old)
    (measurable_unshearedPacketBase p old) href htop hc U hU
  rw [Measure.restrict_apply ((measurable_unshearedPacketBase p old) hU)] at hh
  have heq : unshearedPacketBase p old ⁻¹' U ∩ band =
      {z | unshearedPacketBase p old z ∈ U ∧
        |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
          center (unshearedPacketBase p old z)| ≤ width} := rfl
  rw [heq] at hh
  simpa only [μ, ref, Set.preimage, mul_comm (d.ν k (p.γ old) (p.A old))] using hh

end Prepared

end OriginalPacketCaps

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent
