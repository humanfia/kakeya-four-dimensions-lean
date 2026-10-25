-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.AncestorRowInputs, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalBandWidths

/-!
# The band cap input of the ancestor rows

`ancestor_velocity_rows` asks for a band cap of the clock signal `2^T_a X_a = R_a/δ_a` of the
ancestor at the coarse width, around any measurable function of the unsheared base, in the full
reference of `a`. With child = root = `a` this is x1065's
`PreparedAngularPath.ancestor_moving_signal_child_all_widths` (pure caps of the prepared path),
read on a measurable base set: `ancestor_rows_band`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open ParentSource.Native
open scoped ENNReal

noncomputable section

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) (hpure : Q.uniformPureCeiling ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- **Band cap of the ancestor clock signal** on any source of the ancestor inside its counted
events, the problem's events and the prepared base, at every resolved width. -/
theorem ancestor_rows_band (a : Fin p.C) (hr : 0 ≤ p.r (p.lev a)) (hrL : p.r (p.lev a) ≤ d.L)
    (source : Set Ev) (hsource : MeasurableSet source) (hsE : source ⊆ d.E k (p.γ a))
    (hsbase : source ⊆ Q.base (p.γ a)) (hsF : source ⊆ p.F a)
    {dimension f₀ error : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - f₀ - dimension * r| ≤ error)
    {coarse : ℝ} (hcoarse : 0 < coarse)
    (hresolved : d.N k ^ (-(d.L - p.r (p.lev a))) ≤ 4 * coarse) :
    ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ a)).prod volume).restrict source)
        {x | unshearedPacketBase p a x ∈ U ∧
          |clockParentSignal p a (ancestorSignal (d.N k) p a) x -
            c (unshearedPacketBase p a x)| ≤ coarse} ≤
      ENNReal.ofReal ((64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
          d.N k ^ (2 * error + (τ + 2 * δ₀ * d.L) + ε)) * 1 ^ (-dimension) * coarse ^ dimension) *
        (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) * volume U := by
  intro U hU c hc
  have : IsProbabilityMeasure (d.ν k (p.γ a)) := (hd.weights k).2.2 _
  set μ : Measure Ev := ((d.ν k (p.γ a)).prod volume).restrict source with hμdef
  have hμ : μ ≤ d.μ k (p.γ a) := by
    rw [hμdef, ProblemData.μ]
    exact Measure.restrict_mono hsE le_rfl
  have hbaseAE : ∀ᵐ z ∂μ, z ∈ Q.base (p.γ a) :=
    (ae_restrict_mem hsource).mono fun z hz => hsbase hz
  have hFAE : ∀ᵐ z ∂μ, z ∈ p.F a := (ae_restrict_mem hsource).mono fun z hz => hsF hz
  have hcap := Q.ancestor_moving_signal_child_all_widths hpure hd hp a a rfl le_rfl hr hrL
    μ hμ hbaseAE hFAE hFAE hdim hprofile c hc hcoarse hresolved
  have hcapU := hcap U
  simp only [Measure.smul_apply, smul_eq_mul] at hcapU
  have hbaseM := measurable_unshearedPacketBase p a
  set ref := d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹) with hrefdef
  set band := {z : Ev | |physicalParentSignal (d.N k) p a (p.R a) z -
    c (unshearedPacketBase p a z)| ≤ coarse} with hbanddef
  have hbandM : MeasurableSet band :=
    measurableSet_le ((((measurable_physicalParentSignal _ _ _ _).sub
      (hc.comp hbaseM))).abs) measurable_const
  rw [Measure.map_apply hbaseM hU, Measure.restrict_apply (hbaseM hU)] at hcapU
  -- the clock signal of the scaled test is the physical signal
  have hset : {x | unshearedPacketBase p a x ∈ U ∧
      |clockParentSignal p a (ancestorSignal (d.N k) p a) x - c (unshearedPacketBase p a x)| ≤
        coarse} = unshearedPacketBase p a ⁻¹' U ∩ band := by
    ext x
    simp only [mem_setOf_eq, mem_inter_iff, mem_preimage, hbanddef]
    rw [← ancestorSignal_clock (d.N k) p a x, one_mul]
  rw [hset]
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hrefpos : ref ≠ 0 := by
    exact mul_ne_zero (hp.assignment_mass_pos hN a).ne' (by positivity)
  have hreftop : ref ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hone : (1 : ℝ) ^ (-dimension) = 1 := Real.one_rpow _
  rw [hone, mul_one]
  calc μ (unshearedPacketBase p a ⁻¹' U ∩ band)
      = ref * (ref⁻¹ * μ (unshearedPacketBase p a ⁻¹' U ∩ band)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hrefpos hreftop, one_mul]
    _ ≤ ref * (ENNReal.ofReal ((64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ dimension *
          d.N k ^ (2 * error + (τ + 2 * δ₀ * d.L) + ε)) * coarse ^ dimension) * volume U) :=
        mul_le_mul' le_rfl hcapU
    _ = _ := by ring
