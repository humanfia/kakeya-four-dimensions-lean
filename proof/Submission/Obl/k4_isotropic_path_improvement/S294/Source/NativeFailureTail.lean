-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeFailureTail, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeFailureMassBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.DyadicGridCount

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Filter
open Parent.Qualification
open Parent.Qualification.PhysicalModel (OriginalRootScales)

noncomputable section

/-- Choose the native failure tail before all actual scale packages.
A fixed residual length and a polynomial qualification cutoff supply
the two discrete counts internally. -/
theorem eventually_native_failure_mass_bound
    (N : ℕ → ℝ) (hN : Tendsto N atTop atTop) (Lres : ℕ)
    {Z e : ℝ} (hZ : 0 ≤ Z) (he : 0 < e) :
    ∀ᶠ k in atTop, ∀ s : OriginalRootScales,
      s.incidence.N=N k → s.incidence.L ≤ Lres → N k^(-Z) ≤ s.zeta →
      s.H ≤ s.incidence.N^e → s.canonicalConstant ≤ s.incidence.N^e →
      s.incidence.Cstate ≤ s.incidence.N^e →
      s.Krow ≤ s.incidence.N^(2*e) → s.Kcap ≤ s.incidence.N^(8*e) →
      s.incidence.entryCut0=s.incidence.N^(-4*e) →
      (∀ i < s.incidence.L, s.incidence.entryCut i=s.incidence.N^(-4*e)) →
      (∀ i < s.incidence.L, s.incidence.cut i=s.incidence.N^(-32*e)) →
      s.incidence.nativeCut=s.incidence.N^(-4*e) →
      (200*(Lres:ℝ)+100)*e ≤ s.incidence.ch*s.incidence.alpha →
      s.nativeFailureBound ≤ ENNReal.ofReal (N k^(-e)) := by
  have hlarge := ((tendsto_rpow_atTop he).comp hN).eventually
    (eventually_ge_atTop ((10:ℝ)^100))
  have hlength := ((tendsto_rpow_atTop he).comp hN).eventually
    (eventually_ge_atTop ((Lres+1:ℕ):ℝ))
  have hquery := Jets2.eventually_parameterLevel_add_one_le N hN hZ he
  filter_upwards [hN.eventually (eventually_ge_atTop 1),hlarge,hlength,hquery] with k hk hc hl hq
  change (10:ℝ)^100 ≤ N k^e at hc
  change ((Lres+1:ℕ):ℝ) ≤ N k^e at hl
  intro s hsN hL hzeta hH hcanonical hstate hrow hcap hentry0 hentry hcut hnative hgap
  have hlengthS : ((s.incidence.L+1:ℕ):ℝ) ≤ s.incidence.N^e := by
    rw [hsN]
    have hh : ((s.incidence.L+1:ℕ):ℝ) ≤ ((Lres+1:ℕ):ℝ) := by
      exact_mod_cast Nat.add_le_add_right hL 1
    exact hh.trans hl
  have hlevelsS : ((Jets2.parameterLevel s.zeta+1:ℕ):ℝ) ≤ s.incidence.N^e := by
    rw [hsN]
    exact hq s.zeta hzeta s.hzeta1
  have hgapS : (200*(s.incidence.L:ℝ)+100)*e ≤ s.incidence.ch*s.incidence.alpha := by
    have hh : (s.incidence.L:ℝ)*e ≤ (Lres:ℝ)*e :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hL) he.le
    nlinarith only [hh,hgap]
  have hh := native_failure_mass_bound s (by simpa only [hsN] using hk) he
    (by simpa only [hsN] using hc) hH hcanonical hstate hrow hcap
    hentry0 hentry hcut hnative hlengthS hlevelsS hgapS
  simpa only [hsN] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
