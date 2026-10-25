-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.OldBlockParentCoefficients, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/OldBlockParentCoefficients.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/OldBlockParentCoefficients.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.UnshearedSourceBox
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeCube
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface

/-! # A physical parent on the unit old clock -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

noncomputable section

/-- Physical parent values, unit-clock derivatives, and unsheared planar coordinates.
The signal is kept in physical units. -/
def oldBlockCoefficients (P : Po) (t0 h : ℝ) (c u : P2) (l : Ln) : Fin 7 → ℝ :=
  ![eval (xp l t0) P,
    h * (Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
      2 * t0 * Submission.Lib.K4ProjectedGroups.sc2 P l.2),
    h ^ 2 * Submission.Lib.K4ProjectedGroups.sc2 P l.2,
    (l.2 0 + t0 * l.2 3 - (c 0 + t0 * u 0)) / h, l.2 3,
    (l.2 1 + t0 * l.2 4 - (c 1 + t0 * u 1)) / h, l.2 4]

theorem continuous_oldBlockCoefficients (P : Po) (t0 h : ℝ) (c u : P2) :
    Continuous (oldBlockCoefficients P t0 h c u) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact (Submission.Lib.K4ProjectedGroups.continuous_sig P t0).comp continuous_snd
  · exact continuous_const.mul
      (((Submission.Lib.K4ProjectedGroups.continuous_sc1 P).comp continuous_snd).add
        (continuous_const.mul
          ((Submission.Lib.K4ProjectedGroups.continuous_sc2 P).comp continuous_snd)))
  · exact continuous_const.mul
      ((Submission.Lib.K4ProjectedGroups.continuous_sc2 P).comp continuous_snd)
  · change Continuous (fun l : Ln => (l.2 0 + t0 * l.2 3 - (c 0 + t0 * u 0)) / h)
    fun_prop
  · change Continuous (fun l : Ln => l.2 3)
    fun_prop
  · change Continuous (fun l : Ln => (l.2 1 + t0 * l.2 4 - (c 1 + t0 * u 1)) / h)
    fun_prop
  · change Continuous (fun l : Ln => l.2 4)
    fun_prop

theorem measurable_oldBlockCoefficients (P : Po) (t0 h : ℝ) (c u : P2) :
    Measurable (oldBlockCoefficients P t0 h c u) :=
  (continuous_oldBlockCoefficients P t0 h c u).measurable

/-- The coefficient table represents the original parent on the exact old clock. -/
theorem oldBlock_signal {P : Po} (hP : P.totalDegree ≤ 2) (t0 h : ℝ) (c u : P2)
    (l : Ln) (t : ℝ) :
    Jets2.zx (oldBlockCoefficients P t0 h c u l) t = eval (xp l (t0 + h * t)) P := by
  change Submission.Lib.K4ProjectedGroups.sig P l.2 t0 +
    h * (Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
      2 * t0 * Submission.Lib.K4ProjectedGroups.sc2 P l.2) * t +
    (h ^ 2 * Submission.Lib.K4ProjectedGroups.sc2 P l.2) * t ^ 2 =
      Submission.Lib.K4ProjectedGroups.sig P l.2 (t0 + h * t)
  rw [Submission.Lib.K4ProjectedGroups.sig_eq hP, Submission.Lib.K4ProjectedGroups.sig_eq hP]
  ring

/-- Unit old time differentiates the physical parent with the expected factor `h`. -/
theorem oldBlock_rate {P : Po} (hP : P.totalDegree ≤ 2) (t0 h : ℝ) (c u : P2)
    (l : Ln) (t : ℝ) :
    oldBlockCoefficients P t0 h c u l 1 + 2 * oldBlockCoefficients P t0 h c u l 2 * t =
      h * rate P l (t0 + h * t) := by
  rw [rate_eq_coefficients hP]
  dsimp only [oldBlockCoefficients]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Unsheared planar velocity on the unit old clock is the original physical velocity. -/
theorem oldBlock_velocity (P : Po) (t0 h : ℝ) (c u : P2) (l : Ln) :
    Jets2.zv (oldBlockCoefficients P t0 h c u l) = fun i => v l i := by
  ext i
  fin_cases i <;> rfl

theorem oldBlock_base (P : Po) (t0 h : ℝ) (hh : h ≠ 0) (c u : P2)
    (l : Ln) (t : ℝ) :
    WithLp.toLp 2 (Jets2.zy (oldBlockCoefficients P t0 h c u l) t) =
      h⁻¹ • (y l (t0 + h * t) - (c + t0 • u)) := by
  ext i
  fin_cases i <;>
    simp [oldBlockCoefficients, Jets2.zy, y, x, xp, div_eq_mul_inv] <;>
    field_simp [hh] <;> ring

theorem oldBlock_residual {P : Po} (hP : P.totalDegree ≤ 2) (t0 h : ℝ) (c u : P2)
    (l : Ln) (F : ℝ → Fin 2 → ℝ) (t : ℝ) :
    Jets2.zR F (oldBlockCoefficients P t0 h c u l) t =
      h * rate P l (t0 + h * t) - F t ⬝ᵥ (fun i => v l i) := by
  unfold Jets2.zR
  rw [oldBlock_rate hP, oldBlock_velocity]

/-- Whole original parent bounds give physical, small unit-clock signal coefficients. -/
theorem oldBlock_signal_coefficient_bounds {P : Po} (hP : P.totalDegree ≤ 2)
    {K B t0 h : ℝ} {l : Ln} (hl : l ∈ goodLines P K B)
    (ht0 : t0 ∈ Icc (0 : ℝ) 1) (hh : 0 ≤ h) (c u : P2) :
    |oldBlockCoefficients P t0 h c u l 0| ≤ K ∧
      |oldBlockCoefficients P t0 h c u l 1| ≤ 24 * K * h ∧
      |oldBlockCoefficients P t0 h c u l 2| ≤ 8 * K * h ^ 2 := by
  have hs := fun t ht => (hl t ht).1
  refine ⟨(hl t0 ht0).1, ?_, ?_⟩
  · change |h * (Submission.Lib.K4ProjectedGroups.sc1 P l.2 +
      2 * t0 * Submission.Lib.K4ProjectedGroups.sc2 P l.2)| ≤ _
    rw [← rate_eq_coefficients hP, abs_mul, abs_of_nonneg hh]
    calc
      _ ≤ h * (24 * K) := mul_le_mul_of_nonneg_left (abs_rate_le hP hs ht0) hh
      _ = _ := by ring
  · change |h ^ 2 * Submission.Lib.K4ProjectedGroups.sc2 P l.2| ≤ _
    rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
    calc
      _ ≤ h ^ 2 * (8 * K) :=
        mul_le_mul_of_nonneg_left (Submission.Lib.K4ProjectedGroups.abs_sc2_le hs) (sq_nonneg h)
      _ = _ := by ring

/-- The physical parent table for one actual old packet. -/
def oldPacketCoefficients {W : ℕ} (P : Po) (p : Native.PathData W) (old : Fin p.C)
    (l : Ln) : Fin 7 → ℝ :=
  let h := ((2 : ℝ) ^ p.T (p.lev old))⁻¹
  oldBlockCoefficients P ((p.j old : ℝ) * h) h (p.c old) (p.u old) l

/-- Exact reconstruction of original time from the same unit old clock. -/
theorem oldPacket_time_reconstruction {W : ℕ} (p : Native.PathData W) (old : Fin p.C)
    (q : Ev) :
    let h := ((2 : ℝ) ^ p.T (p.lev old))⁻¹
    (p.j old : ℝ) * h + h * packetTime p old q = q.2 := by
  dsimp only [packetTime, nativeOldBaseFrame]
  field_simp
  ring

theorem measurable_oldPacketCoefficients {W : ℕ} (P : Po) (p : Native.PathData W)
    (old : Fin p.C) : Measurable (oldPacketCoefficients P p old) :=
  measurable_oldBlockCoefficients _ _ _ _ _

/-- At the actual source time, the table is exactly the original physical parent. -/
theorem oldPacket_signal {W : ℕ} {P : Po} (hP : P.totalDegree ≤ 2)
    (p : Native.PathData W) (old : Fin p.C) (q : Ev) :
    Jets2.zx (oldPacketCoefficients P p old q.1) (packetTime p old q) = eval (xp q.1 q.2) P := by
  unfold oldPacketCoefficients
  rw [oldBlock_signal hP, oldPacket_time_reconstruction]

/-- The table's planar coordinates are the literal unsheared source coordinates. -/
theorem oldPacket_base {W : ℕ} (P : Po) (p : Native.PathData W) (old : Fin p.C) (q : Ev) :
    WithLp.toLp 2 (Jets2.zy (oldPacketCoefficients P p old q.1) (packetTime p old q)) =
      WithLp.toLp 2 ![unshearedPacketBase p old q 1, unshearedPacketBase p old q 2] := by
  unfold oldPacketCoefficients
  rw [oldBlock_base _ _ _ (by positivity), oldPacket_time_reconstruction]
  ext i
  fin_cases i <;> simp [unshearedPacketBase, y, x, xp, div_eq_mul_inv] <;> ring

theorem oldPacket_rate {W : ℕ} {P : Po} (hP : P.totalDegree ≤ 2)
    (p : Native.PathData W) (old : Fin p.C) (q : Ev) :
    oldPacketCoefficients P p old q.1 1 +
      2 * oldPacketCoefficients P p old q.1 2 * packetTime p old q =
        ((2 : ℝ) ^ p.T (p.lev old))⁻¹ * rate P q.1 q.2 := by
  unfold oldPacketCoefficients
  rw [oldBlock_rate hP, oldPacket_time_reconstruction]

/-- The actual current incidence and the original parent/velocity-good line bound
all seven old-clock coefficients by one fixed power. -/
theorem oldPacket_coefficient_bounds {d : Native.ProblemData} (hd : d.Valid)
    {k m : ℕ} {p : Native.PathData (d.W k)} {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ) (old : Fin p.C) {K : ℝ} (hK : 24 ≤ K)
    (hmax : max p.κ (d.K k) ≤ K) {q : Ev} (hq : q ∈ p.F old)
    (hgood : q.1 ∈ goodLines (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)))
    (hvel : ‖v q.1‖ ≤ d.K k) :
    ∀ e, |oldPacketCoefficients (d.P k (p.γ old)) p old q.1 e| ≤ K ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hDK : d.K k ≤ K := (le_max_right _ _).trans hmax
  have hκK : p.κ ≤ K := (le_max_left _ _).trans hmax
  have hDK0 : 0 ≤ d.K k := by linarith [hd.2.2.1.1 k]
  let clock : ℝ := (2 : ℝ) ^ p.T (p.lev old)
  let h := clock⁻¹
  let t0 := (p.j old : ℝ) * h
  have hc : 0 < clock := by dsimp [clock]; positivity
  have hc1 : 1 ≤ clock := one_le_pow₀ (by norm_num)
  have hh : 0 < h := inv_pos.mpr hc
  have hh1 : h ≤ 1 := by
    simpa only [h, one_div, inv_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hc1
  have hj : p.j old < 2 ^ p.T (p.lev old) := (hp.2.2.2.2.2.2.2 old).2.1
  have hjle : (p.j old : ℝ) ≤ clock := by
    dsimp [clock]
    exact_mod_cast Nat.le_of_lt hj
  have ht0 : t0 ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by dsimp [t0]; positivity, ?_⟩
    simpa only [t0, h, div_eq_mul_inv] using (div_le_one hc).mpr hjle
  have hP := (original_parent_bounds (show pb d.N d.K d.L d.d d.S d.η d.W d.ω d.ν d.E
    d.P d.B d.f d.g d.G from hd) k (p.γ old)).1
  have hs := oldBlock_signal_coefficient_bounds hP hgood ht0 hh.le (p.c old) (p.u old)
  let C := oldPacketCoefficients (d.P k (p.γ old)) p old q.1
  have hsignal0 : |C 0| ≤ K := hs.1.trans hDK
  have hsignal1 : |C 1| ≤ 24 * K := by
    refine hs.2.1.trans ?_
    calc
      _ ≤ 24 * K * 1 := by gcongr
      _ = _ := mul_one _
  have hsignal2 : |C 2| ≤ 8 * K := by
    refine hs.2.2.trans ?_
    have hh2 : h ^ 2 ≤ 1 := by nlinarith
    calc
      _ ≤ 8 * K * 1 := by gcongr
      _ = _ := mul_one _
  let Z := unshearedPacketBase p old q
  have hZ : ‖Z‖ ≤ K ^ 3 := original_unsheared_source_box hd hp (by linarith) hκK hDK old hq
  have htime : |Z 0| ≤ 1 := by
    have ht := packetTime_unit hp old hq
    have heq : Z 0 = packetTime p old q := by
      simp [Z, unshearedPacketBase, packetTime, nativeOldBaseFrame, div_eq_mul_inv]
    rw [heq, abs_of_nonneg ht.1]
    exact ht.2
  have hZ1 : |Z 1| ≤ K ^ 3 := (PiLp.norm_apply_le Z 1).trans hZ
  have hZ2 : |Z 2| ≤ K ^ 3 := (PiLp.norm_apply_le Z 2).trans hZ
  have hV0 : |q.1.2 3| ≤ K := (PiLp.norm_apply_le (v q.1) 0).trans (hvel.trans hDK)
  have hV1 : |q.1.2 4| ≤ K := (PiLp.norm_apply_le (v q.1) 1).trans (hvel.trans hDK)
  have hbase0 : |C 3| ≤ K ^ 3 + K := by
    have heq : C 3 = Z 1 - Z 0 * q.1.2 3 := by
      change (q.1.2 0 + t0 * q.1.2 3 - (p.c old 0 + t0 * p.u old 0)) / h =
        (q.1.2 0 + q.2 * q.1.2 3 - (p.c old 0 + t0 * p.u old 0)) / h -
          ((q.2 - t0) / h) * q.1.2 3
      ring
    rw [heq]
    calc
      _ ≤ |Z 1| + |Z 0| * |q.1.2 3| := by simpa only [abs_mul] using abs_sub (Z 1) (Z 0 * q.1.2 3)
      _ ≤ K ^ 3 + 1 * K := by gcongr
      _ = _ := by ring
  have hbase1 : |C 5| ≤ K ^ 3 + K := by
    have heq : C 5 = Z 2 - Z 0 * q.1.2 4 := by
      change (q.1.2 1 + t0 * q.1.2 4 - (p.c old 1 + t0 * p.u old 1)) / h =
        (q.1.2 1 + q.2 * q.1.2 4 - (p.c old 1 + t0 * p.u old 1)) / h -
          ((q.2 - t0) / h) * q.1.2 4
      ring
    rw [heq]
    calc
      _ ≤ |Z 2| + |Z 0| * |q.1.2 4| := by simpa only [abs_mul] using abs_sub (Z 2) (Z 0 * q.1.2 4)
      _ ≤ K ^ 3 + 1 * K := by gcongr
      _ = _ := by ring
  have hK4 : K ≤ K ^ 4 := by simpa only [pow_one] using pow_le_pow_right₀ hK1 (by norm_num : (1 : ℕ) ≤ 4)
  have hsignalK : 24 * K ≤ K ^ 4 := by
    have hK2 : 24 * K ≤ K ^ 2 := by nlinarith
    exact hK2.trans (pow_le_pow_right₀ hK1 (by norm_num : (2 : ℕ) ≤ 4))
  have hbaseK : K ^ 3 + K ≤ K ^ 4 := by
    have hK3 : K ≤ K ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hK1 (by norm_num : (1 : ℕ) ≤ 3)
    calc
      _ ≤ K ^ 3 + K ^ 3 := by linarith
      _ = 2 * K ^ 3 := by ring
      _ ≤ K * K ^ 3 := by gcongr; linarith
      _ = _ := by ring
  intro e
  change |C e| ≤ _
  fin_cases e
  · exact hsignal0.trans hK4
  · exact hsignal1.trans hsignalK
  · exact hsignal2.trans ((by nlinarith : 8 * K ≤ 24 * K).trans hsignalK)
  · exact hbase0.trans hbaseK
  · exact hV0.trans hK4
  · exact hbase1.trans hbaseK
  · exact hV1.trans hK4

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
