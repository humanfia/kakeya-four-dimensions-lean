-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ClockParentCoefficients, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ClockParentCoefficients.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit84825054,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ClockParentCoefficients.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.OldBlockParentCoefficients

/-! # The clock parent coefficient table

Only the signal coordinates are divided by the old clock length. The
constant signal coefficient can be large; all six other coefficients have
a fixed power bound from the original parent and velocity-good line.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
noncomputable section

def scaleSignal (a : ℝ) (c : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![a*c 0, a*c 1, a*c 2, c 3, c 4, c 5, c 6]

theorem scaleSignal_zx (a : ℝ) (c : Fin 7 → ℝ) (t : ℝ) :
    Jets2.zx (scaleSignal a c) t = a*Jets2.zx c t := by
  dsimp [scaleSignal, Jets2.zx]
  ring

theorem scaleSignal_zy (a : ℝ) (c : Fin 7 → ℝ) (t : ℝ) :
    Jets2.zy (scaleSignal a c) t = Jets2.zy c t := rfl

theorem scaleSignal_zv (a : ℝ) (c : Fin 7 → ℝ) :
    Jets2.zv (scaleSignal a c) = Jets2.zv c := rfl

theorem measurable_scaleSignal (a : ℝ) : Measurable (scaleSignal a) := by
  apply measurable_pi_iff.mpr
  intro e
  fin_cases e
  all_goals dsimp [scaleSignal]
  all_goals fun_prop

def clockPacketCoefficients {W : ℕ} (P : Po) (p : Native.PathData W) (old : Fin p.C)
    (l : Ln) : Fin 7 → ℝ :=
  scaleSignal ((2:ℝ)^p.T (p.lev old)) (oldPacketCoefficients P p old l)

theorem measurable_clockPacketCoefficients {W : ℕ} (P : Po) (p : Native.PathData W)
    (old : Fin p.C) : Measurable (clockPacketCoefficients P p old) :=
  (measurable_scaleSignal _).comp (measurable_oldPacketCoefficients _ _ _)

theorem clockPacket_signal {W : ℕ} {P : Po} (hP : P.totalDegree ≤ 2)
    (p : Native.PathData W) (old : Fin p.C) (q : Ev) :
    Jets2.zx (clockPacketCoefficients P p old q.1) (packetTime p old q) =
      (2:ℝ)^p.T (p.lev old)*eval (xp q.1 q.2) P := by
  rw [clockPacketCoefficients, scaleSignal_zx, oldPacket_signal hP]

theorem clockPacket_base {W : ℕ} (P : Po) (p : Native.PathData W)
    (old : Fin p.C) (q : Ev) :
    WithLp.toLp 2 (Jets2.zy (clockPacketCoefficients P p old q.1) (packetTime p old q)) =
      WithLp.toLp 2 ![unshearedPacketBase p old q 1, unshearedPacketBase p old q 2] :=
  oldPacket_base P p old q

theorem clockPacket_velocity {W : ℕ} (P : Po) (p : Native.PathData W)
    (old : Fin p.C) (l : Ln) :
    Jets2.zv (clockPacketCoefficients P p old l) = fun i => v l i :=
  oldBlock_velocity P ((p.j old:ℝ)*((2:ℝ)^p.T (p.lev old))⁻¹)
    (((2:ℝ)^p.T (p.lev old))⁻¹) (p.c old) (p.u old) l

/-- The clock derivative of P/h is the original-time derivative of P.
There is no inverse old thickness or inverse clock factor in this rate. -/
theorem clockPacket_rate {W : ℕ} {P : Po} (hP : P.totalDegree ≤ 2)
    (p : Native.PathData W) (old : Fin p.C) (q : Ev) :
    clockPacketCoefficients P p old q.1 1 +
      2*clockPacketCoefficients P p old q.1 2*packetTime p old q = rate P q.1 q.2 := by
  have hc : (2:ℝ)^p.T (p.lev old) ≠ 0 := by positivity
  change (2:ℝ)^p.T (p.lev old)*oldPacketCoefficients P p old q.1 1 +
    2*((2:ℝ)^p.T (p.lev old)*oldPacketCoefficients P p old q.1 2)*
      packetTime p old q = _
  calc
    _ = (2:ℝ)^p.T (p.lev old)*(oldPacketCoefficients P p old q.1 1 +
      2*oldPacketCoefficients P p old q.1 2*packetTime p old q) := by ring
    _ = (2:ℝ)^p.T (p.lev old)*(((2:ℝ)^p.T (p.lev old))⁻¹*rate P q.1 q.2) := by
      rw [oldPacket_rate hP]
    _ = _ := by rw [←mul_assoc, mul_inv_cancel₀ hc, one_mul]

theorem clockPacket_residual {W : ℕ} {P : Po} (hP : P.totalDegree ≤ 2)
    (p : Native.PathData W) (old : Fin p.C) (q : Ev) (F : ℝ → Fin 2 → ℝ) :
    Jets2.zR F (clockPacketCoefficients P p old q.1) (packetTime p old q) =
      rate P q.1 q.2-F (packetTime p old q) ⬝ᵥ (fun i => v q.1 i) := by
  unfold Jets2.zR
  rw [clockPacket_rate hP, clockPacket_velocity]

/-- The constant height coefficient is deliberately omitted. It is
removed by the central quadratic when choosing a coefficient world. -/
theorem clockPacket_nonconstant_coefficients_bound {d : Native.ProblemData} (hd : d.Valid)
    {k m : ℕ} {p : Native.PathData (d.W k)} {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ) (old : Fin p.C) {K : ℝ} (hK : 24 ≤ K)
    (hmax : max p.κ (d.K k) ≤ K) {q : Ev} (hq : q ∈ p.F old)
    (hgood : q.1 ∈ goodLines (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)))
    (hvel : ‖v q.1‖ ≤ d.K k) :
    ∀ e : Fin 7, e ≠ 0 →
      |clockPacketCoefficients (d.P k (p.γ old)) p old q.1 e| ≤ K^4 := by
  have hK1 : 1 ≤ K := by linarith
  have hDK : d.K k ≤ K := (le_max_right _ _).trans hmax
  have hDK0 : 0 ≤ d.K k := by linarith [hd.2.2.1.1 k]
  have hold := oldPacket_coefficient_bounds hd hp old hK hmax hq hgood hvel
  let clock : ℝ := (2:ℝ)^p.T (p.lev old)
  let h : ℝ := clock⁻¹
  let t0 : ℝ := (p.j old:ℝ)*h
  have hc : 0 < clock := by dsimp [clock]; positivity
  have hc1 : 1 ≤ clock := one_le_pow₀ (by norm_num)
  have hh : 0 < h := inv_pos.mpr hc
  have hh1 : h ≤ 1 := by simpa only [h, inv_one] using inv_anti₀ (by norm_num : (0:ℝ)<1) hc1
  have hj : (p.j old:ℝ) ≤ clock := by
    dsimp [clock]
    exact_mod_cast Nat.le_of_lt (hp.2.2.2.2.2.2.2 old).2.1
  have ht0 : t0∈Icc (0:ℝ) 1 := by
    refine ⟨by dsimp [t0]; positivity, ?_⟩
    simpa only [t0,h,div_eq_mul_inv] using (div_le_one hc).mpr hj
  have hP := (original_parent_bounds (show pb d.N d.K d.L d.d d.S d.η d.W d.ω d.ν d.E
    d.P d.B d.f d.g d.G from hd) k (p.γ old)).1
  have hs := oldBlock_signal_coefficient_bounds hP hgood ht0 hh.le (p.c old) (p.u old)
  have h1 : |clockPacketCoefficients (d.P k (p.γ old)) p old q.1 1| ≤ 24*K := by
    change |clock*oldBlockCoefficients _ t0 h _ _ _ 1| ≤ _
    rw [abs_mul, abs_of_pos hc]
    calc
      _ ≤ clock*(24*d.K k*h) := mul_le_mul_of_nonneg_left hs.2.1 hc.le
      _ = 24*d.K k := by dsimp [h]; field_simp
      _ ≤ _ := by gcongr
  have h2 : |clockPacketCoefficients (d.P k (p.γ old)) p old q.1 2| ≤ 8*K := by
    change |clock*oldBlockCoefficients _ t0 h _ _ _ 2| ≤ _
    rw [abs_mul, abs_of_pos hc]
    calc
      _ ≤ clock*(8*d.K k*h^2) := mul_le_mul_of_nonneg_left hs.2.2 hc.le
      _ = 8*d.K k*h := by dsimp [h]; field_simp
      _ ≤ 8*K*1 := by gcongr
      _ = _ := mul_one _
  have hpower : 24*K ≤ K^4 := by
    have h2 : 24*K ≤ K^2 := by nlinarith
    exact h2.trans (pow_le_pow_right₀ hK1 (by norm_num : (2:ℕ)≤4))
  intro e he
  fin_cases e
  · exact (he rfl).elim
  · exact h1.trans hpower
  · exact h2.trans ((by nlinarith : 8*K ≤ 24*K).trans hpower)
  · exact hold 3
  · exact hold 4
  · exact hold 5
  · exact hold 6

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
