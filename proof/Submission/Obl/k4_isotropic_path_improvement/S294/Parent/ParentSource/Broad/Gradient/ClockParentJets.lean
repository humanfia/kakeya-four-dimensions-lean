-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ClockParentJets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ClockParentJets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit c5f477fdc5b972684b967b4654ceacc9f5a8f0ff,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ClockParentJets.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ClockParentCoefficients

/-! # Bounded clock jets on the unchanged original trajectory space

Only the two signal jets and the two physical planar velocities enter
the curvature velocity backend. The remaining three coefficients are
left unrestricted, including the possibly large constant P/h.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
open MeasureTheory Set MvPolynomial
noncomputable section

theorem clockPacket_jet_bounds {W : ℕ} {P : Po} (hP : P.totalDegree≤2)
    (p : Native.PathData W) (old : Fin p.C)
    (hbin : p.j old<2^p.T (p.lev old)) {K B : ℝ} (hK : 0≤K) {l : Ln}
    (hgood : l∈goodLines P K B) (hvel : ‖v l‖≤K) :
    |clockPacketCoefficients P p old l 1|≤24*K ∧
    |clockPacketCoefficients P p old l 2|≤24*K ∧
    |clockPacketCoefficients P p old l 4|≤24*K ∧
    |clockPacketCoefficients P p old l 6|≤24*K := by
  let clock : ℝ := (2:ℝ)^p.T (p.lev old)
  let h : ℝ := clock⁻¹
  let t0 : ℝ := (p.j old:ℝ)*h
  have hc : 0<clock := by dsimp [clock]; positivity
  have hc1 : 1≤clock := one_le_pow₀ (by norm_num)
  have hh : 0<h := inv_pos.mpr hc
  have hh1 : h≤1 := by
    simpa only [h,inv_one] using inv_anti₀ (by norm_num : (0:ℝ)<1) hc1
  have ht0 : t0∈Icc (0:ℝ) 1 := by
    have hj : (p.j old:ℝ) ≤ clock := by
      dsimp [clock]
      exact_mod_cast Nat.le_of_lt hbin
    refine ⟨by dsimp [t0]; positivity, ?_⟩
    simpa only [t0,h,div_eq_mul_inv] using (div_le_one hc).mpr hj
  have hs := oldBlock_signal_coefficient_bounds hP hgood ht0 hh.le (p.c old) (p.u old)
  have h1 : |clockPacketCoefficients P p old l 1|≤24*K := by
    change |clock*oldBlockCoefficients P t0 h _ _ _ 1|≤_
    rw [abs_mul,abs_of_pos hc]
    calc
      _ ≤ clock*(24*K*h) := mul_le_mul_of_nonneg_left hs.2.1 hc.le
      _ = _ := by dsimp [h]; field_simp
  have h2 : |clockPacketCoefficients P p old l 2|≤24*K := by
    change |clock*oldBlockCoefficients P t0 h _ _ _ 2|≤_
    rw [abs_mul,abs_of_pos hc]
    calc
      _ ≤ clock*(8*K*h^2) := mul_le_mul_of_nonneg_left hs.2.2 hc.le
      _ = 8*K*h := by dsimp [h]; field_simp
      _ ≤ 8*K*1 := by gcongr
      _ ≤ _ := by nlinarith
  have h4 : |clockPacketCoefficients P p old l 4|≤24*K := by
    change |l.2 3|≤_
    exact ((PiLp.norm_apply_le (v l) 0).trans hvel).trans (by linarith)
  have h6 : |clockPacketCoefficients P p old l 6|≤24*K := by
    change |l.2 4|≤_
    exact ((PiLp.norm_apply_le (v l) 1).trans hvel).trans (by linarith)
  exact ⟨h1,h2,h4,h6⟩

def clockJetGood (P : Po) (K B : ℝ) : Set Ln :=
  goodLines P K B∩{l | ‖v l‖≤K}

theorem measurableSet_clockJetGood (P : Po) (K B : ℝ) : MeasurableSet (clockJetGood P K B) := by
  apply (measurableSet_goodLines P K B).inter
  apply measurableSet_le _ measurable_const
  exact (show Continuous v by unfold v; fun_prop).measurable.norm

/-- The four jets are zero only on excluded lines. All intercepts and
every coefficient on the actual good source are unchanged. -/
def eraseClockJets (c : Fin 7 → ℝ) : Fin 7 → ℝ := ![c 0,0,0,c 3,0,c 5,0]

theorem measurable_eraseClockJets : Measurable eraseClockJets := by
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j <;> dsimp only [eraseClockJets] <;> fun_prop

def safeClockCoefficients {W : ℕ} (P : Po) (K B : ℝ) (p : Native.PathData W)
    (old : Fin p.C) (l : Ln) : Fin 7 → ℝ := by
  classical
  exact if l∈clockJetGood P K B then clockPacketCoefficients P p old l else
    eraseClockJets (clockPacketCoefficients P p old l)

theorem safeClockCoefficients_eq {W : ℕ} (P : Po) (K B : ℝ) (p : Native.PathData W)
    (old : Fin p.C) {l : Ln} (hl : l∈clockJetGood P K B) :
    safeClockCoefficients P K B p old l=clockPacketCoefficients P p old l := by
  classical
  exact if_pos hl

theorem measurable_safeClockCoefficients {W : ℕ} (P : Po) (K B : ℝ)
    (p : Native.PathData W) (old : Fin p.C) : Measurable (safeClockCoefficients P K B p old) := by
  classical
  have hc := measurable_clockPacketCoefficients P p old
  exact Measurable.ite (measurableSet_clockJetGood P K B) hc
    (measurable_eraseClockJets.comp hc)

theorem safeClockCoefficients_jets {W : ℕ} {P : Po} (hP : P.totalDegree≤2)
    (p : Native.PathData W) (old : Fin p.C) (hbin : p.j old<2^p.T (p.lev old))
    {K B : ℝ} (hK : 0≤K) (l : Ln) :
    |safeClockCoefficients P K B p old l 1|≤24*K ∧
    |safeClockCoefficients P K B p old l 2|≤24*K ∧
    |safeClockCoefficients P K B p old l 4|≤24*K ∧
    |safeClockCoefficients P K B p old l 6|≤24*K := by
  by_cases hl : l∈clockJetGood P K B
  · rw [safeClockCoefficients_eq P K B p old hl]
    exact clockPacket_jet_bounds hP p old hbin hK hl.1 hl.2
  · simp only [safeClockCoefficients,if_neg hl,eraseClockJets,Fin.isValue,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val,abs_zero]
    have hh : 0≤24*K := by positivity
    exact ⟨hh,hh,hh,hh⟩

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
