-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleNumerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Per-sample side conditions of the producers at the skeleton's scalars (session x1088).

* `cap_constants_le_K`: the constants of the base ceiling and the band cap
  (`Source.ChildCaps.childCapClauses`) are below `K = N^kexp`.
* `eps_resolved`: the band widths are resolved at the state mesh, `N^-(L - r_b) ≤ 4 ε`, for
  `ε = epsOf …` whenever the relative depth and the precision exponents fit in `L - r_b`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages
import Submission.Obl.k4_clean_cover_graph_atlas

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- The cap constants are below `K = N^kexp` once `κ, K_d ≤ N^(kexp/8)`, `2^12 ≤ N^(kexp/8)`,
`τ, ε₀ ≤ δ₀ L` and `6 δ₀ L ≤ kexp/8`. -/
theorem cap_constants_le_K {N kexp κ Kd δ₀ L τ ε₀ d₁ : ℝ} (hN : 1 < N) (hk : 0 < kexp)
    (hκ1 : 1 ≤ κ) (hκ : κ ≤ N ^ (kexp / 8)) (hKd0 : 0 ≤ Kd) (hKd : Kd ≤ N ^ (kexp / 8))
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ δ₀ * L) (hε0 : 0 ≤ ε₀) (hε : ε₀ ≤ δ₀ * L) (hδ0 : 0 ≤ δ₀ * L)
    (hδ : 6 * (δ₀ * L) ≤ kexp / 8) (h12 : 2 ^ 12 ≤ N ^ (kexp / 8)) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ ≤ 1) :
    64 * (max κ Kd) ^ 2 * κ * N ^ (τ + 2 * δ₀ * L + ε₀) ≤ N ^ kexp ∧
      64 * (max κ Kd) ^ 2 * κ * 4 ^ d₁ * N ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + ε₀) ≤
        N ^ kexp := by
  have hNp : 0 < N := by linarith
  set Y := N ^ (kexp / 8) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN.le (by positivity)
  have hmax : max κ Kd ≤ Y := max_le hκ hKd
  have hmax0 : 0 ≤ max κ Kd := le_trans (by linarith) (le_max_left κ Kd)
  have hpow : ∀ a b : ℝ, N ^ a * N ^ b = N ^ (a + b) := fun a b => (Real.rpow_add hNp a b).symm
  have hY8 : N ^ kexp = Y ^ 8 := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; congr 1; push_cast; ring
  -- the exponential factors are at most `Y`
  have hE1 : N ^ (τ + 2 * δ₀ * L + ε₀) ≤ Y :=
    Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
  have hE2 : N ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + ε₀) ≤ Y :=
    Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
  have h4 : (4 : ℝ) ^ d₁ ≤ 4 := by
    calc (4 : ℝ) ^ d₁ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hd₁
      _ = 4 := Real.rpow_one 4
  have h40 : (0 : ℝ) ≤ 4 ^ d₁ := by positivity
  have hm2 : (max κ Kd) ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hmax0 hmax 2
  have hκ0 : 0 ≤ κ := by linarith
  have hY0 : 0 ≤ Y := by linarith
  -- `256 Y^4 ≤ Y^8` since `2^12 ≤ Y`
  have hY4 : 256 * Y ^ 4 ≤ Y ^ 8 := by
    have h1 : (256 : ℝ) ≤ Y ^ 4 := by
      calc (256 : ℝ) ≤ 2 ^ 12 := by norm_num
        _ ≤ Y := h12
        _ ≤ Y ^ 4 := le_self_pow₀ hY1 (by norm_num)
    calc 256 * Y ^ 4 ≤ Y ^ 4 * Y ^ 4 := by gcongr
      _ = Y ^ 8 := by ring
  rw [hY8]
  constructor
  · calc 64 * (max κ Kd) ^ 2 * κ * N ^ (τ + 2 * δ₀ * L + ε₀) ≤ 64 * Y ^ 2 * Y * Y := by
          gcongr
      _ ≤ 256 * Y ^ 4 := by nlinarith [pow_nonneg hY0 4]
      _ ≤ Y ^ 8 := hY4
  · calc 64 * (max κ Kd) ^ 2 * κ * 4 ^ d₁ * N ^ (2 * (δ₀ * L) + (τ + 2 * δ₀ * L) + ε₀)
        ≤ 64 * Y ^ 2 * Y * 4 * Y := by gcongr
      _ = 256 * Y ^ 4 := by ring
      _ ≤ Y ^ 8 := hY4

/-- **Resolution of the band widths at the state mesh**: `N^-(L - r_b) ≤ 4 ε` for
`ε = epsOf Ep precision loss gain N L r_a r_b T_a T_b`, when the relative depth plus the
precision exponents fit below `L - r_b`. -/
theorem eps_resolved {N L rA rB precision loss gain : ℝ} {Ep TA TB : ℕ} (hN : 1 < N)
    (hTAB : TA ≤ TB) (hpgl : 0 ≤ precision * gain * L) (hkexp : 0 ≤ loss * gain * L / ((Ep : ℝ) + 1))
    (hfit : (rB - rA) + ((Ep : ℝ) + 1) * (precision * gain * L) +
      (2 * (Ep : ℝ) + 2) * (loss * gain * L / ((Ep : ℝ) + 1)) ≤ L - rB) :
    N ^ (-(L - rB)) ≤ 4 * epsOf Ep precision loss gain N L rA rB TA TB := by
  have hNp : 0 < N := by linarith
  have hlb : N ^ (-rB) ≤ O204.Split.δ N rB :=
    (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp rB).1
  have hua : O204.Split.δ N rA ≤ 2 * N ^ (-rA) :=
    (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp rA).2
  have hlz : N ^ (-(precision * gain * L)) ≤ O204.Split.δ N (precision * gain * L) :=
    (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp (precision * gain * L)).1
  set kexp := loss * gain * L / ((Ep : ℝ) + 1) with hkdef
  set pgl := precision * gain * L with hpgldef
  have hδA : 0 < O204.Split.δ N rA := by
    have := Real.rpow_pos_of_pos hNp (-rA)
    have : 0 < O204.Split.δ N rA := O204.Tangent.δ_pos N rA
    exact this
  -- the relative thickness, divided by the relative clock `≤ 1`
  have hh1 : hRelOf TA TB ≤ 1 := by
    unfold hRelOf; exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hh0 : 0 < hRelOf TA TB := by unfold hRelOf; positivity
  have ha : N ^ (rA - rB) / 2 ≤ aRelOf N rA rB := by
    unfold aRelOf
    rw [div_le_div_iff₀ (by norm_num) hδA]
    calc N ^ (rA - rB) * O204.Split.δ N rA ≤ N ^ (rA - rB) * (2 * N ^ (-rA)) := by gcongr
      _ = 2 * N ^ (-rB) := by
          rw [mul_comm 2, ← mul_assoc, ← Real.rpow_add hNp]; ring_nf
      _ ≤ O204.Split.δ N rB * 2 := by linarith
  have hah : N ^ (rA - rB) / 2 ≤ aRelOf N rA rB / hRelOf TA TB := by
    refine ha.trans ?_
    rw [le_div_iff₀ hh0]
    have : 0 ≤ aRelOf N rA rB := le_trans (by positivity) ha
    nlinarith
  have hz : N ^ (-pgl) ≤ zetaOf precision gain N L := hlz
  have hz0 : 0 ≤ N ^ (-pgl) := by positivity
  have hzEp : (N ^ (-pgl)) ^ Ep ≤ zetaOf precision gain N L ^ Ep := pow_le_pow_left₀ hz0 hz Ep
  have hK : KOf Ep loss gain N L = N ^ kexp := rfl
  have hKp : ∀ n : ℕ, KOf Ep loss gain N L ^ n = N ^ ((n : ℝ) * kexp) := by
    intro n; rw [hK, ← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; ring_nf
  have hNpow : ∀ n : ℕ, (N ^ (-pgl)) ^ n = N ^ (-((n : ℝ) * pgl)) := by
    intro n; rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; ring_nf
  -- assemble
  unfold epsOf thetaOf
  rw [hKp Ep, hKp (Ep + 2)]
  have key : N ^ (rA - rB) / 2 * N ^ (-((Ep : ℝ) * pgl)) / N ^ ((Ep : ℝ) * kexp) *
      N ^ (-pgl) / N ^ (((Ep + 2 : ℕ) : ℝ) * kexp) ≤
      aRelOf N rA rB / hRelOf TA TB * zetaOf precision gain N L ^ Ep / N ^ ((Ep : ℝ) * kexp) *
        zetaOf precision gain N L / N ^ (((Ep + 2 : ℕ) : ℝ) * kexp) := by
    rw [← hNpow Ep]
    have hz0' : 0 ≤ zetaOf precision gain N L := le_trans hz0 hz
    have haR0 : 0 ≤ aRelOf N rA rB / hRelOf TA TB := le_trans (by positivity) hah
    have hzpow : 0 ≤ (N ^ (-pgl)) ^ Ep := by positivity
    have hNa : 0 ≤ N ^ (rA - rB) / 2 := by positivity
    gcongr
  refine le_trans ?_ (mul_le_mul_of_nonneg_left key (by norm_num))
  -- the lower bound is `N^(rA - rB - (Ep+1) pgl - (2Ep+2) kexp) / 2`
  have hexp : N ^ (rA - rB) / 2 * N ^ (-((Ep : ℝ) * pgl)) / N ^ ((Ep : ℝ) * kexp) * N ^ (-pgl) /
      N ^ (((Ep + 2 : ℕ) : ℝ) * kexp) =
      N ^ (rA - rB - ((Ep : ℝ) + 1) * pgl - (2 * (Ep : ℝ) + 2) * kexp) / 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ← Real.rpow_neg hNp.le, ← Real.rpow_neg hNp.le]
    have : rA - rB - ((Ep : ℝ) + 1) * pgl - (2 * (Ep : ℝ) + 2) * kexp =
        (rA - rB) + (-((Ep : ℝ) * pgl)) + (-((Ep : ℝ) * kexp)) + (-pgl) +
          (-(((Ep + 2 : ℕ) : ℝ) * kexp)) := by push_cast; ring
    rw [this, Real.rpow_add hNp, Real.rpow_add hNp, Real.rpow_add hNp, Real.rpow_add hNp]
    ring
  rw [hexp]
  have hle : -(L - rB) ≤ rA - rB - ((Ep : ℝ) + 1) * pgl - (2 * (Ep : ℝ) + 2) * kexp := by
    linarith
  have := Real.rpow_le_rpow_of_exponent_le hN.le hle
  have hpos := Real.rpow_pos_of_pos hNp (rA - rB - ((Ep : ℝ) + 1) * pgl - (2 * (Ep : ℝ) + 2) * kexp)
  linarith

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
