-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.SignalJets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.SignalClockStage
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct.BlockCoefficientBounds

/-!
# Clock jets of a signal that is small on an enclosing block

The relative row packet uses, at a packet `b`, the clock model of the signal `X = (q/δ_A) R_A`
built from the test `R_A` of an ancestor `A` (block `[t_A, t_A + q]`, thickness `δ_A`). Along a
line of `A` the chart gives `|R_A| ≤ κ δ_A` on the whole block of `A`, i.e. `|X| ≤ κ q`. The
clock coefficients of `X` at `b` are bounded by Markov on the block of `A` (not of `b`, which
would lose the ratio of the two clocks):

* `rate_le_of_block`: `|rate X l t| ≤ 24 M / q` for `t` in the block, if `|X| ≤ M` there;
* `clockPacket_jets_of_block`: the clock coefficients `1, 2` of `X` at any packet whose block
  lies in the enclosing block are bounded by `24 M / q`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open ParentSource.Native
open Submission.Lib.K4GlobalParentSignal
open scoped ENNReal

noncomputable section

/-- **Markov on an enclosing block.** A degree-two signal bounded by `M` along a line on the block
`[t₀, t₀ + q]` has rate at most `24 M / q` there. -/
theorem rate_le_of_block (X : Po) (hX : X.totalDegree ≤ 2) (l : Ln) {t₀ q M : ℝ} (hq : 0 < q)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |eval (xp l (t₀ + q * s)) X| ≤ M) {t : ℝ}
    (ht : t ∈ Icc t₀ (t₀ + q)) :
    |rate X l t| ≤ 24 * M / q := by
  obtain ⟨-, h1, h2⟩ := Direct.oldBlock_local_signal_bounds X hX t₀ q 0 0 l hbound
  set s := (t - t₀) / q with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith [ht.1]) hq.le
  have hs1 : s ≤ 1 := (div_le_one hq).mpr (by linarith [ht.2])
  have hts : t = t₀ + q * s := by rw [hs]; field_simp; ring
  have hr := ParentSignal.oldBlock_rate hX t₀ q 0 0 l s
  rw [← hts] at hr
  -- `q * rate = c₁ + 2 c₂ s`
  have hbnd : |q * rate X l t| ≤ 24 * M := by
    rw [← hr]
    have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbound 0 (by norm_num))
    calc |ParentSignal.oldBlockCoefficients X t₀ q 0 0 l 1 +
          2 * ParentSignal.oldBlockCoefficients X t₀ q 0 0 l 2 * s|
        ≤ |ParentSignal.oldBlockCoefficients X t₀ q 0 0 l 1| +
          2 * |ParentSignal.oldBlockCoefficients X t₀ q 0 0 l 2| * s := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hs0]
      _ ≤ 8 * M + 2 * (8 * M) * 1 := by gcongr
      _ = 24 * M := by ring
  rw [abs_mul, abs_of_pos hq] at hbnd
  rw [le_div_iff₀ hq]
  linarith

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}

/-- **Clock jets from an enclosing block.** If `X` is bounded by `M` along `l` on a block
`[t₀, t₀ + q]` containing the block of `b`, the first two clock coefficients of `X` at `b` are
bounded by `24 M / q`. -/
theorem clockPacket_jets_of_block (X : Po) (hX : X.totalDegree ≤ 2) (b : Fin p.C) (l : Ln)
    {t₀ q M : ℝ} (hq : 0 < q)
    (hbound : ∀ s ∈ Icc (0 : ℝ) 1, |eval (xp l (t₀ + q * s)) X| ≤ M)
    (hlow : t₀ ≤ (p.j b : ℝ) * ((2 : ℝ) ^ p.T (p.lev b))⁻¹)
    (hup : ((p.j b : ℝ) + 1) * ((2 : ℝ) ^ p.T (p.lev b))⁻¹ ≤ t₀ + q) :
    |ParentSignal.clockPacketCoefficients X p b l 1| ≤ 24 * M / q ∧
      |ParentSignal.clockPacketCoefficients X p b l 2| ≤ 24 * M / q := by
  set h := ((2 : ℝ) ^ p.T (p.lev b))⁻¹ with hh
  set tb := (p.j b : ℝ) * h with htb
  have hh0 : 0 < h := by positivity
  have hclock : (2 : ℝ) ^ p.T (p.lev b) * h = 1 := by rw [hh]; field_simp
  -- the rate at the two ends of the block of `b`
  have hrate (s : ℝ) :
      ParentSignal.clockPacketCoefficients X p b l 1 +
        2 * ParentSignal.clockPacketCoefficients X p b l 2 * s = rate X l (tb + h * s) := by
    have hr := ParentSignal.oldBlock_rate hX tb h (p.c b) (p.u b) l s
    change (2 : ℝ) ^ p.T (p.lev b) * ParentSignal.oldBlockCoefficients X tb h (p.c b) (p.u b) l 1 +
      2 * ((2 : ℝ) ^ p.T (p.lev b) *
        ParentSignal.oldBlockCoefficients X tb h (p.c b) (p.u b) l 2) * s = _
    calc (2 : ℝ) ^ p.T (p.lev b) * ParentSignal.oldBlockCoefficients X tb h (p.c b) (p.u b) l 1 +
          2 * ((2 : ℝ) ^ p.T (p.lev b) *
            ParentSignal.oldBlockCoefficients X tb h (p.c b) (p.u b) l 2) * s
        = (2 : ℝ) ^ p.T (p.lev b) *
            (ParentSignal.oldBlockCoefficients X tb h (p.c b) (p.u b) l 1 +
              2 * ParentSignal.oldBlockCoefficients X tb h (p.c b) (p.u b) l 2 * s) := by ring
      _ = (2 : ℝ) ^ p.T (p.lev b) * (h * rate X l (tb + h * s)) := by rw [hr]
      _ = rate X l (tb + h * s) := by rw [← mul_assoc, hclock, one_mul]
  have h0 : tb + h * 0 ∈ Icc t₀ (t₀ + q) := by
    constructor <;> nlinarith [hlow, hup]
  have h1 : tb + h * 1 ∈ Icc t₀ (t₀ + q) := by
    constructor
    · nlinarith [hlow]
    · have : tb + h * 1 = ((p.j b : ℝ) + 1) * h := by rw [htb]; ring
      rw [this]; exact hup
  have r0 := rate_le_of_block X hX l hq hbound h0
  have r1 := rate_le_of_block X hX l hq hbound h1
  have e0 := hrate 0
  have e1 := hrate 1
  simp only [mul_zero, add_zero, mul_one] at e0 e1
  refine ⟨?_, ?_⟩
  · rw [e0]; simpa using r0
  · have hc2 : ParentSignal.clockPacketCoefficients X p b l 2 =
        (rate X l (tb + h) - rate X l tb) / 2 := by
      have := e1; rw [e0] at this; linarith
    have hM : 0 ≤ 24 * M / q := le_trans (abs_nonneg _) r0
    rw [hc2, abs_div, abs_two]
    calc |rate X l (tb + h) - rate X l tb| / 2 ≤ (|rate X l (tb + h)| + |rate X l tb|) / 2 := by
          gcongr; exact abs_sub _ _
      _ ≤ (24 * M / q + 24 * M / q) / 2 := by
          gcongr
          · simpa using r1
          · simpa using r0
      _ = 24 * M / q := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph
