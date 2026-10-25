-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.ListLane, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleFinal
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.MiddleLevel
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.GridMono
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootLists
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Glue
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleScalars

/-!
# The list lane of one sample (session x1082)

The list budget `hsmallList` of `Source.SampleFinal.sample_final` at a middle level `mid` between
the ancestor level `i` and the child level `i + c`:
`Lp ((h_b/h_a) 2θ + 2 K^8 δ_mid/δ_a + B (h_b/h_mid) 6θ + ρ) ≤ θ` (times `aA/q`).

* `list_depth_quarter`: `A δ_mid/δ_a ≤ θ` from the structure `θ = (δ_b/δ_a) 2^(T_b-T_a) ζ^Ep/K^Ep`
  once `A ≤ N^e`, `r_b - r_mid ≤ D` and `a + e + D + Ep·precision·gain·L + Ep·kexp ≤ G` where
  `N^G ≤ 2^(T_b - T_a)` (`2 ≤ N^a`);
* `list_lane`: the middle level `mid = midOf i X m` with the clock gap
  `Y = (e₂/L + 2 δ₀)/κ₁` to the child, and all list hypotheses of `sample_final`
  (`jmid hmidb hmida hrmid hrLmid hwidthmid hsmallList`) from `Lp ρ ≤ θ/8`, `Lp 2^-(T_b-T_a) ≤ 1/8`,
  `16 Lp K^8 ≤ N^e₁`, `24 Lp B ≤ N^e₂` and one room inequality.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

/-- **The depth quarter of the list budget.** -/
theorem list_depth_quarter {N L rA rB rM precision loss gain a e D G : ℝ} {Ep TA TB : ℕ}
    (hN : 1 < N) (_hTAB : TA ≤ TB) (h2 : 2 ≤ N ^ a) {A : ℝ} (_hA0 : 0 ≤ A) (hA : A ≤ N ^ e)
    (hD : rB - rM ≤ D) (hG : N ^ G ≤ (2 : ℝ) ^ (TB - TA))
    (hroom : a + e + D + (Ep : ℝ) * (precision * gain * L) +
      (Ep : ℝ) * (loss * gain * L / ((Ep : ℝ) + 1)) ≤ G) :
    A * (O204.Split.δ N rM / O204.Split.δ N rA) ≤
      thetaOf Ep precision loss gain N L rA rB TA TB := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hδA := O204.Tangent.δ_pos N rA
  have hδB := O204.Tangent.δ_pos N rB
  have hδM := O204.Tangent.δ_pos N rM
  set pgl := precision * gain * L with hpgl
  set kexp := loss * gain * L / ((Ep : ℝ) + 1) with hkexp
  -- `θ = (δ_b/δ_a) 2^(T_b - T_a) ζ^Ep/K^Ep`
  have hθ : thetaOf Ep precision loss gain N L rA rB TA TB =
      (O204.Split.δ N rB / O204.Split.δ N rA) *
        ((2 : ℝ) ^ (TB - TA) * (zetaOf precision gain N L ^ Ep / KOf Ep loss gain N L ^ Ep)) := by
    unfold thetaOf aRelOf hRelOf
    rw [div_inv_eq_mul]
    ring
  rw [hθ]
  -- reduce to `A δ_mid/δ_b ≤ 2^(T_b-T_a) ζ^Ep/K^Ep`
  have hsplit : A * (O204.Split.δ N rM / O204.Split.δ N rA) =
      (O204.Split.δ N rB / O204.Split.δ N rA) * (A * (O204.Split.δ N rM / O204.Split.δ N rB)) := by
    field_simp
  rw [hsplit]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hδB.le hδA.le)
  -- the left side is at most `2 N^(e + D)`
  have hMB : O204.Split.δ N rM / O204.Split.δ N rB ≤ 2 * N ^ (rB - rM) := by
    have hM := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN0 rM).2
    have hB := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN0 rB).1
    rw [div_le_iff₀ hδB]
    calc O204.Split.δ N rM ≤ 2 * N ^ (-rM) := hM
      _ = 2 * N ^ (rB - rM) * N ^ (-rB) := by
          rw [mul_assoc, ← Real.rpow_add hN0]; ring_nf
      _ ≤ 2 * N ^ (rB - rM) * O204.Split.δ N rB :=
          mul_le_mul_of_nonneg_left hB (by positivity)
  have hleft : A * (O204.Split.δ N rM / O204.Split.δ N rB) ≤ N ^ (a + e + D) := by
    calc A * (O204.Split.δ N rM / O204.Split.δ N rB) ≤ N ^ e * (2 * N ^ D) := by
          apply mul_le_mul hA _ (div_nonneg hδM.le hδB.le) (by positivity)
          exact hMB.trans (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hN.le hD) (by norm_num))
      _ ≤ N ^ e * (N ^ a * N ^ D) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = N ^ (a + e + D) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf
  -- the right side is at least `N^(G - Ep pgl - Ep kexp)`
  have hζ : N ^ (-pgl) ≤ zetaOf precision gain N L :=
    (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN0 pgl).1
  have hζEp : N ^ (-((Ep : ℝ) * pgl)) ≤ zetaOf precision gain N L ^ Ep := by
    calc N ^ (-((Ep : ℝ) * pgl)) = (N ^ (-pgl)) ^ Ep := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hζ Ep
  have hKEp : KOf Ep loss gain N L ^ Ep = N ^ ((Ep : ℝ) * kexp) := by
    unfold KOf
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, hkexp]
    congr 1; ring
  have hright : N ^ (G - (Ep : ℝ) * pgl - (Ep : ℝ) * kexp) ≤
      (2 : ℝ) ^ (TB - TA) * (zetaOf precision gain N L ^ Ep / KOf Ep loss gain N L ^ Ep) := by
    rw [hKEp]
    have e1 : N ^ (G - (Ep : ℝ) * pgl - (Ep : ℝ) * kexp) =
        N ^ G * (N ^ (-((Ep : ℝ) * pgl)) / N ^ ((Ep : ℝ) * kexp)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      ring_nf
    rw [e1]
    apply mul_le_mul hG _ (by positivity) (by positivity)
    exact div_le_div_of_nonneg_right hζEp (by positivity)
  refine hleft.trans (le_trans ?_ hright)
  exact Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)

/-- The list budget from four quarter budgets (any association of the terms). -/
theorem list_sum_of_quarters {Lp θ aA q t₁ t₂ t₃ t₄ : ℝ} (hscale : 0 ≤ aA / q)
    (h1 : Lp * t₁ ≤ θ / 4) (h2 : Lp * t₂ ≤ θ / 4) (h3 : Lp * t₃ ≤ θ / 4) (h4 : Lp * t₄ ≤ θ / 4) :
    ((aA / q) * Lp) * (t₁ + (t₂ + t₃) + t₄) ≤ (aA / q) * θ := by
  have hsum : Lp * (t₁ + (t₂ + t₃) + t₄) ≤ θ := by
    have e : Lp * (t₁ + (t₂ + t₃) + t₄) = Lp * t₁ + (Lp * t₂ + Lp * t₃) + Lp * t₄ := by ring
    rw [e]; linarith
  calc ((aA / q) * Lp) * (t₁ + (t₂ + t₃) + t₄) = (aA / q) * (Lp * (t₁ + (t₂ + t₃) + t₄)) := by ring
    _ ≤ (aA / q) * θ := mul_le_mul_of_nonneg_left hsum hscale

/-- The relative clock length of two levels. -/
theorem clock_div_eq {Ta Tb : ℕ} (h : Ta ≤ Tb) :
    ((2 : ℝ) ^ Tb)⁻¹ / ((2 : ℝ) ^ Ta)⁻¹ = ((2 : ℝ) ^ (Tb - Ta))⁻¹ := by
  rw [pow_sub₀ _ (by norm_num : (2 : ℝ) ≠ 0) h]
  field_simp

/-- **The room of the list lane**: both room inequalities of `list_lane` once the two exponents are
at most `κ₁ gain L/4`. -/
theorem list_room {L κ₁ δ₀ precision loss gain e₁ e₂ : ℝ} {Ep m : ℕ} (hL : 0 < L) (hκ : 0 < κ₁)
    (hκ1 : κ₁ ≤ 1) (hδ0 : 0 ≤ δ₀) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁) (hprec : 1 ≤ precision)
    (hloss : 0 ≤ loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain) (hm : 0 < m)
    (hgm : 8 ≤ gain * (m : ℝ)) (he₁ : e₁ ≤ κ₁ * (gain * L) / 4) (he₂ : e₂ ≤ κ₁ * (gain * L) / 4) :
    (e₂ / L + 2 * δ₀) / κ₁ + 1 / (m : ℝ) ≤ (childOffset κ₁ Ep precision gain m : ℝ) / m ∧
      gain * L + e₁ + ((((e₂ / L + 2 * δ₀) / κ₁ + 1 / (m : ℝ)) * L + 2 * δ₀ * L)) +
        (Ep : ℝ) * (precision * gain * L) + (Ep : ℝ) * (loss * gain * L / ((Ep : ℝ) + 1)) ≤
          κ₁ * ((childOffset κ₁ Ep precision gain m : ℝ) / m) * L - 2 * δ₀ * L := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlow := childOffset_lower (κ₁ := κ₁) (precision := precision) (gain := gain) (Ep := Ep) hκ hm
  set cm := (childOffset κ₁ Ep precision gain m : ℝ) / m with hcm
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hE1 : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
  -- the elementary bounds
  have h1m : 1 / (m : ℝ) ≤ gain / 8 := by
    rw [div_le_div_iff₀ hmR (by norm_num)]; linarith
  have hδ : δ₀ ≤ κ₁ * gain / 32 := by
    have h1 : δ₀ * (m : ℝ) ≤ κ₁ / 4 := by linarith
    have h2 : δ₀ ≤ κ₁ / 4 * (1 / (m : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ hmR]; exact h1
    calc δ₀ ≤ κ₁ / 4 * (1 / (m : ℝ)) := h2
      _ ≤ κ₁ / 4 * (gain / 8) := mul_le_mul_of_nonneg_left h1m (by positivity)
      _ = κ₁ * gain / 32 := by ring
  have hδκ : 2 * δ₀ / κ₁ ≤ gain / 16 := by
    rw [div_le_iff₀ hκ]; nlinarith
  have he₂κ : e₂ / L / κ₁ ≤ gain / 4 := by
    rw [div_div, div_le_iff₀ (by positivity)]; nlinarith
  have hY : (e₂ / L + 2 * δ₀) / κ₁ ≤ gain / 4 + gain / 16 := by
    rw [add_div]; linarith
  -- `c/m ≥ 2 ((Ep+1) precision + 2) gain/κ₁ ≥ 6 gain`
  have hcm6 : 6 * gain ≤ cm := by
    refine le_trans ?_ hlow
    rw [le_div_iff₀ hκ]
    have : 3 ≤ ((Ep : ℝ) + 1) * precision + 2 := by nlinarith
    nlinarith
  have hκcm : 2 * (((Ep : ℝ) + 1) * precision + 2) * gain ≤ κ₁ * cm := by
    have := mul_le_mul_of_nonneg_left hlow hκ.le
    rwa [mul_div_cancel₀ _ hκ.ne'] at this
  refine ⟨by linarith, ?_⟩
  -- the second room
  have hloss' : (Ep : ℝ) * (loss * gain * L / ((Ep : ℝ) + 1)) ≤ gain * L := by
    rw [mul_div_assoc', div_le_iff₀ hE1]
    have : loss * gain * L ≤ gain * L := by
      have := mul_le_mul_of_nonneg_right hloss1 (mul_pos hgain hL).le
      linarith
    nlinarith
  have hYL : (((e₂ / L + 2 * δ₀) / κ₁ + 1 / (m : ℝ)) * L) ≤ (gain / 4 + gain / 16 + gain / 8) * L :=
    mul_le_mul_of_nonneg_right (by linarith) hL.le
  have hδL : 2 * δ₀ * L ≤ κ₁ * gain * L / 16 := by nlinarith
  have hκcmL : 2 * (((Ep : ℝ) + 1) * precision + 2) * gain * L ≤ κ₁ * cm * L :=
    mul_le_mul_of_nonneg_right hκcm hL.le
  have hκa : κ₁ * (gain * L) ≤ gain * L := by
    have := mul_le_mul_of_nonneg_right hκ1 (mul_pos hgain hL).le; linarith
  have hEp : (Ep : ℝ) * (precision * gain * L) ≤ (Ep : ℝ) * precision * (gain * L) := by ring_nf; rfl
  nlinarith [mul_pos hgain hL, mul_nonneg hE (mul_nonneg (by linarith : (0:ℝ) ≤ precision) (mul_pos hgain hL).le)]

/-- **The powers of the list lane**: `16 Lp K^8 ≤ N^(κ₁ a/4)` and `24 Lp B ≤ N^(κ₁ a/4)` (`a = gain L`)
from `Lp ≤ N^(κ₁ a/8)`, `K, κ, K_d ≤ N^g`, `N^(2 δ₀ L) ≤ N^g` and one power budget. -/
theorem list_powers {N Lp K κ Kd δ₀ L g A : ℝ} {R J : ℕ} (hN : 1 < N) (hK0 : 0 < K)
    (hκ0 : 0 ≤ κ) (hKd0 : 0 ≤ Kd) (hg : 0 ≤ g) (hA : 0 ≤ A)
    (hLp0 : 0 ≤ Lp) (hLp : Lp ≤ N ^ (A / 8)) (hK : K ≤ N ^ g) (hκ : κ ≤ N ^ g) (hKd : Kd ≤ N ^ g)
    (hδ : 2 * δ₀ * L ≤ g)
    (hbudget : (((3 * R + 58 + 7) * J + R + 12 : ℕ) : ℝ) * g ≤ A / 64)
    (h432 : 432 ≤ N ^ (A / 64)) :
    16 * Lp * (K ^ 14 * (K ^ 6)⁻¹) ≤ N ^ (A / 4) ∧
      24 * Lp * (((K ^ (3 * R + 58 + 7)) ^ J * (κ + K ^ 14 * (K ^ 6)⁻¹)) *
        (K ^ R * (1 + 2 * (κ * N ^ (2 * δ₀ * L)) * (1 + (Kd + 2 * κ ^ 2))))) ≤ N ^ (A / 4) := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hNg1 : 1 ≤ N ^ g := Real.one_le_rpow hN.le hg
  have hpow : ∀ n : ℕ, (N ^ g) ^ n = N ^ ((n : ℝ) * g) := by
    intro n; rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hK8 : K ^ 14 * (K ^ 6)⁻¹ = K ^ 8 := by
    field_simp
  have hKpow : ∀ n : ℕ, K ^ n ≤ N ^ ((n : ℝ) * g) := by
    intro n; rw [← hpow]; exact pow_le_pow_left₀ hK0.le hK n
  have hbud0 : 0 ≤ A / 64 := by positivity
  -- exponents below the budget
  have hle : ∀ n : ℕ, n ≤ (3 * R + 58 + 7) * J + R + 12 → (n : ℝ) * g ≤ A / 64 := by
    intro n hn
    refine le_trans ?_ hbudget
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hg
  have h16 : (16 : ℝ) ≤ N ^ (A / 64) := le_trans (by norm_num) h432
  constructor
  · rw [hK8]
    have h8 : K ^ 8 ≤ N ^ (A / 64) :=
      (hKpow 8).trans (Real.rpow_le_rpow_of_exponent_le hN.le (hle 8 (by omega)))
    calc 16 * Lp * K ^ 8 ≤ N ^ (A / 64) * N ^ (A / 8) * N ^ (A / 64) := by gcongr
      _ = N ^ (A / 64 + A / 8 + A / 64) := by rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      _ ≤ N ^ (A / 4) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
  · rw [hK8]
    set n₁ := (3 * R + 58 + 7) * J with hn₁
    -- the factors
    have hf1 : (K ^ (3 * R + 58 + 7)) ^ J ≤ N ^ ((n₁ : ℝ) * g) := by
      rw [← pow_mul]; exact hKpow _
    have hf2 : κ + K ^ 8 ≤ 2 * N ^ (8 * g) := by
      have h1 : κ ≤ N ^ (8 * g) :=
        hκ.trans (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith))
      have h2 : K ^ 8 ≤ N ^ (8 * g) := by
        have := hKpow 8; push_cast at this; exact this
      linarith
    have hf3 : K ^ R ≤ N ^ ((R : ℝ) * g) := hKpow R
    have hNδ : N ^ (2 * δ₀ * L) ≤ N ^ g := Real.rpow_le_rpow_of_exponent_le hN.le hδ
    have hf4 : 1 + 2 * (κ * N ^ (2 * δ₀ * L)) * (1 + (Kd + 2 * κ ^ 2)) ≤ 9 * N ^ (4 * g) := by
      have hNg0 : 0 ≤ N ^ g := by positivity
      have e2 : N ^ (2 * g) = N ^ g * N ^ g := by rw [← Real.rpow_add hN0]; ring_nf
      have e4 : N ^ (4 * g) = N ^ (2 * g) * N ^ (2 * g) := by rw [← Real.rpow_add hN0]; ring_nf
      have h1 : κ * N ^ (2 * δ₀ * L) ≤ N ^ (2 * g) := by
        rw [e2]; exact mul_le_mul hκ hNδ (by positivity) hNg0
      have h2 : 1 + (Kd + 2 * κ ^ 2) ≤ 4 * N ^ (2 * g) := by
        have hκ2 : κ ^ 2 ≤ N ^ (2 * g) := by
          rw [e2, sq]; exact mul_le_mul hκ hκ (by positivity) hNg0
        have hg2 : 1 ≤ N ^ (2 * g) := Real.one_le_rpow hN.le (by linarith)
        have hKd2 : Kd ≤ N ^ (2 * g) := hKd.trans (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith))
        linarith
      have hg4 : 1 ≤ N ^ (4 * g) := Real.one_le_rpow hN.le (by linarith)
      have h12 : 2 * (κ * N ^ (2 * δ₀ * L)) * (1 + (Kd + 2 * κ ^ 2)) ≤ 2 * N ^ (2 * g) * (4 * N ^ (2 * g)) := by
        have : 0 ≤ κ * N ^ (2 * δ₀ * L) := by positivity
        have : 0 ≤ 1 + (Kd + 2 * κ ^ 2) := by positivity
        gcongr
      have e8 : 2 * N ^ (2 * g) * (4 * N ^ (2 * g)) = 8 * N ^ (4 * g) := by rw [e4]; ring
      linarith
    have hB : ((K ^ (3 * R + 58 + 7)) ^ J * (κ + K ^ 8)) *
        (K ^ R * (1 + 2 * (κ * N ^ (2 * δ₀ * L)) * (1 + (Kd + 2 * κ ^ 2)))) ≤
        18 * N ^ (((n₁ + R + 12 : ℕ) : ℝ) * g) := by
      have e : N ^ (((n₁ + R + 12 : ℕ) : ℝ) * g) =
          N ^ ((n₁ : ℝ) * g) * N ^ (8 * g) * N ^ ((R : ℝ) * g) * N ^ (4 * g) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0]; push_cast; ring_nf
      rw [e]
      have h0a : 0 ≤ (K ^ (3 * R + 58 + 7)) ^ J := by positivity
      have h0b : 0 ≤ κ + K ^ 8 := by positivity
      have h0c : 0 ≤ K ^ R := by positivity
      have h0d : 0 ≤ 1 + 2 * (κ * N ^ (2 * δ₀ * L)) * (1 + (Kd + 2 * κ ^ 2)) := by positivity
      calc ((K ^ (3 * R + 58 + 7)) ^ J * (κ + K ^ 8)) *
            (K ^ R * (1 + 2 * (κ * N ^ (2 * δ₀ * L)) * (1 + (Kd + 2 * κ ^ 2))))
          ≤ (N ^ ((n₁ : ℝ) * g) * (2 * N ^ (8 * g))) * (N ^ ((R : ℝ) * g) * (9 * N ^ (4 * g))) := by
            gcongr
        _ = 18 * (N ^ ((n₁ : ℝ) * g) * N ^ (8 * g) * N ^ ((R : ℝ) * g) * N ^ (4 * g)) := by ring
    have hBexp : N ^ (((n₁ + R + 12 : ℕ) : ℝ) * g) ≤ N ^ (A / 64) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (hle _ (by omega))
    have hB0 : 0 ≤ ((K ^ (3 * R + 58 + 7)) ^ J * (κ + K ^ 8)) *
        (K ^ R * (1 + 2 * (κ * N ^ (2 * δ₀ * L)) * (1 + (Kd + 2 * κ ^ 2)))) := by positivity
    calc 24 * Lp * (((K ^ (3 * R + 58 + 7)) ^ J * (κ + K ^ 8)) *
          (K ^ R * (1 + 2 * (κ * N ^ (2 * δ₀ * L)) * (1 + (Kd + 2 * κ ^ 2)))))
        ≤ 24 * N ^ (A / 8) * (18 * N ^ (A / 64)) := by
          have hB' := hB.trans (mul_le_mul_of_nonneg_left hBexp (by norm_num))
          exact mul_le_mul (mul_le_mul_of_nonneg_left hLp (by norm_num)) hB' hB0 (by positivity)
      _ = 432 * N ^ (A / 8) * N ^ (A / 64) := by ring
      _ ≤ N ^ (A / 64) * N ^ (A / 8) * N ^ (A / 64) := by gcongr
      _ = N ^ (A / 64 + A / 8 + A / 64) := by rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
      _ ≤ N ^ (A / 4) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)

section Lane

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)} {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ}
    {Mp Dp : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The list lane of one sample.** -/
theorem list_lane (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hs : ∀ l, s l = ((l : ℝ) + 1) / m) (hm : 0 < m) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1)
    (hδ0 : 0 ≤ δ₀) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁)
    {Ep : ℕ} {precision loss gain : ℝ} (hprec : 1 ≤ precision) (hloss : 0 ≤ loss)
    (hgain : 0 < gain) {i nfam : ℕ}
    (hib : i + childOffset κ₁ Ep precision gain m < m)
    (hcfam : childOffset κ₁ Ep precision gain m < nfam)
    {τ θ Lp ρ aA q : ℝ} (hτ : 0 ≤ τ)
    (hθdef : θ = thetaOf Ep precision loss gain (d.N k) d.L (p.r i)
      (p.r (i + childOffset κ₁ Ep precision gain m)) (p.T i)
      (p.T (i + childOffset κ₁ Ep precision gain m)))
    (haA : 0 < aA) (hq : 0 < q)
    (hLp0 : 0 ≤ Lp) (hLpρ : Lp * ρ ≤ θ / 8)
    (hLpClock : Lp * ((2 : ℝ) ^ (p.T (i + childOffset κ₁ Ep precision gain m) - p.T i))⁻¹ ≤ 1 / 8)
    {e₁ e₂ : ℝ} (_he₁ : 0 ≤ e₁) (he₂ : 0 ≤ e₂)
    (hA₁ : 16 * Lp * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹) ≤ d.N k ^ e₁)
    (hA₂ : 24 * Lp * (((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^
        FixedSourcePowers.jet * (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
      (coreK p τ ^ FixedSourcePowers.coreRadius *
        (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))))) ≤ d.N k ^ e₂)
    (h2a : 2 ≤ d.N k ^ (gain * d.L))
    (hroom1 : (e₂ / d.L + 2 * δ₀) / κ₁ + 1 / (m : ℝ) ≤
      (childOffset κ₁ Ep precision gain m : ℝ) / m)
    (hroom2 : gain * d.L + e₁ + ((((e₂ / d.L + 2 * δ₀) / κ₁ + 1 / (m : ℝ)) * d.L + 2 * δ₀ * d.L)) +
      (Ep : ℝ) * (precision * gain * d.L) + (Ep : ℝ) * (loss * gain * d.L / ((Ep : ℝ) + 1)) ≤
        κ₁ * ((childOffset κ₁ Ep precision gain m : ℝ) / m) * d.L - 2 * δ₀ * d.L) :
    ∃ jmid : Fin nfam,
      (∀ b, p.lev b = i + childOffset κ₁ Ep precision gain m → (i + (jmid : ℕ)) ≤ p.lev b) ∧
      (∀ b, p.lev b = i + childOffset κ₁ Ep precision gain m →
        p.lev b - childOffset κ₁ Ep precision gain m ≤ (i + (jmid : ℕ))) ∧
      0 ≤ p.r ((i + (jmid : ℕ))) ∧ p.r ((i + (jmid : ℕ))) ≤ d.L ∧
      δ (d.N k) (p.r ((i + (jmid : ℕ)))) ≤ δ (d.N k) (p.r i) ∧
      (∀ b, p.lev b = i + childOffset κ₁ Ep precision gain m →
        ((aA / q) * Lp) * ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
            ((2 : ℝ) ^ p.T (p.lev (p.par^[childOffset κ₁ Ep precision gain m] b)))⁻¹) * (2 * θ) +
          (2 * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹ * (δ (d.N k) (p.r ((i + (jmid : ℕ)))) /
            δ (d.N k) (p.r (p.lev (p.par^[childOffset κ₁ Ep precision gain m] b))))) +
            ((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^ FixedSourcePowers.jet *
              (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
              (coreK p τ ^ FixedSourcePowers.coreRadius *
                ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
                ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
                  ((2 : ℝ) ^ p.T (p.lev (p.par^[p.lev b - (i + (jmid : ℕ))] b)))⁻¹) *
                    (6 * θ))))) +
          ρ) ≤ (aA / q) * θ) := by
  set c := childOffset κ₁ Ep precision gain m with hc
  have hN2 : (2 : ℝ) ≤ d.N k := hd.1 k
  have hN1 : (1 : ℝ) < d.N k := by linarith
  have hL : 0 < d.L := hd.2.2.2.1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hκp1 : 1 ≤ p.κ := hp.1
  obtain ⟨hK2304, -, -, -⟩ :=
    Submission.Lib.K4NativePreparationNumerics.native_pre_geometry_envelope_bounds
      (source := d.K k) hκp1 hN1.le (by linarith : 0 ≤ τ + τ)
  have hK0 : 0 < coreK p τ := lt_of_lt_of_le (by norm_num) hK2304
  have hθ0 : 0 < θ := by
    rw [hθdef]
    exact (sample_scalars_pos (Ep := Ep) (precision := precision) (loss := loss) (gain := gain)
      (N := d.N k) (L := d.L) (rA := p.r i) (rB := p.r (i + c)) (TA := p.T i)
      (TB := p.T (i + c)) hN1 (by positivity) (by positivity)).1
  -- the middle level
  set Y := (e₂ / d.L + 2 * δ₀) / κ₁ with hY
  set X := (c : ℝ) / m - Y - 1 / (m : ℝ) with hX
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hX0 : 0 ≤ X := by rw [hX]; linarith
  have hsc : s (i + c) - s i = (c : ℝ) / m := by rw [hs, hs]; push_cast; ring
  have hgap : X + Y + 1 / (m : ℝ) ≤ s (i + c) - s i := by rw [hsc, hX]; linarith
  obtain ⟨hmid1, hmid2, hmidX, hmidY⟩ := midOf_spec hm hs hX0 hY0 hgap
  set mid := midOf i X m with hmid
  have hmidm : mid < m := by omega
  have hjmid : mid - i < nfam := by omega
  have hjeq : i + (mid - i) = mid := by omega
  -- the three levels on the path
  have hA := hp.2.2.2.2.1 i (by omega)
  have hM := hp.2.2.2.2.1 mid hmidm
  have hB := hp.2.2.2.2.1 (i + c) hib
  have hTab : p.T i ≤ p.T (i + c) := path_T_le hp hN1 hL hm hs hδm hκ (by omega) hib
  have hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r i) :=
    path_delta_le hp hN1.le hL hm hs hδm hκ1 hmid1 hmidm
  have hrLe : ∀ l, l < m → p.r l ≤ d.L := by
    intro l hl
    have h := path_r_le hp hL hm hs hδm hκ1 (show l ≤ m - 1 by omega) (by omega)
    rw [hp.2.2.2.1] at h
    exact h
  -- the gap from the middle level to the child
  have hbm_hi : s (i + c) - s mid ≤ Y + 1 / (m : ℝ) := by
    have : s (i + c) - s mid = (s (i + c) - s i) - (s mid - s i) := by ring
    rw [this, hsc]; rw [hX] at hmidX; linarith
  -- the clock quarter
  have hsep : κ₁ * s mid + δ₀ ≤ κ₁ * s (i + c) - δ₀ := by
    have h1 : κ₁ * Y ≤ κ₁ * (s (i + c) - s mid) := mul_le_mul_of_nonneg_left hmidY hκ.le
    have h2 : κ₁ * Y = e₂ / d.L + 2 * δ₀ := by rw [hY]; field_simp
    have h3 : 0 ≤ e₂ / d.L := by positivity
    nlinarith
  have hTmb : p.T mid ≤ p.T (i + c) := clock_mono hN1 hL.le hM.2.2.2.1 hB.2.2.1 hsep
  have hcr := clock_ratio_le (N := d.N k) (L := d.L) (κ₁ := κ₁) (δ₀ := δ₀) (sx := s mid)
    (sy := s (i + c)) hN1 hTmb hM.2.2.2.1 hB.2.2.1
  have hclock : 24 * Lp * (((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^
        FixedSourcePowers.jet * (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
      (coreK p τ ^ FixedSourcePowers.coreRadius *
        (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))))) *
        ((2 : ℝ) ^ (p.T (i + c) - p.T mid))⁻¹ ≤ 1 := by
    have he₂le : e₂ ≤ (κ₁ * (s (i + c) - s mid) - 2 * δ₀) * d.L := by
      have h1 : κ₁ * Y ≤ κ₁ * (s (i + c) - s mid) := mul_le_mul_of_nonneg_left hmidY hκ.le
      have h2 : κ₁ * Y = e₂ / d.L + 2 * δ₀ := by rw [hY]; field_simp
      have h3 : e₂ = (e₂ / d.L) * d.L := by field_simp
      nlinarith
    calc _ ≤ d.N k ^ e₂ * d.N k ^ (-((κ₁ * (s (i + c) - s mid) - 2 * δ₀) * d.L)) :=
          mul_le_mul hA₂ hcr (by positivity) (by positivity)
      _ = d.N k ^ (e₂ - (κ₁ * (s (i + c) - s mid) - 2 * δ₀) * d.L) := by
          rw [← Real.rpow_add (by linarith)]; ring_nf
      _ ≤ d.N k ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1.le (by linarith)
      _ = 1 := Real.rpow_zero _
  -- the depth quarter
  have hdepthQ : 16 * Lp * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹) *
      (δ (d.N k) (p.r mid) / δ (d.N k) (p.r i)) ≤ θ := by
    rw [hθdef]
    apply list_depth_quarter (a := gain * d.L) (e := e₁)
      (D := ((e₂ / d.L + 2 * δ₀) / κ₁ + 1 / (m : ℝ)) * d.L + 2 * δ₀ * d.L)
      (G := κ₁ * ((c : ℝ) / m) * d.L - 2 * δ₀ * d.L) hN1 hTab h2a (by positivity) hA₁
    · -- the depth from the middle level to the child
      have h1 := (abs_le.mp hB.1).2
      have h2 := (abs_le.mp hM.1).1
      have h3 : (s (i + c) - s mid) * d.L ≤ (Y + 1 / (m : ℝ)) * d.L :=
        mul_le_mul_of_nonneg_right hbm_hi hL.le
      rw [hY] at h3
      nlinarith
    · -- the clock from the ancestor to the child
      rw [pow_sub₀ _ (by norm_num : (2 : ℝ) ≠ 0) hTab, ← div_eq_mul_inv,
        le_div_iff₀ (by positivity)]
      calc d.N k ^ (κ₁ * ((c : ℝ) / m) * d.L - 2 * δ₀ * d.L) * (2 : ℝ) ^ p.T i
          ≤ d.N k ^ (κ₁ * ((c : ℝ) / m) * d.L - 2 * δ₀ * d.L) *
              d.N k ^ ((κ₁ * s i + δ₀) * d.L) :=
            mul_le_mul_of_nonneg_left hA.2.2.2.1 (by positivity)
        _ = d.N k ^ ((κ₁ * s (i + c) - δ₀) * d.L) := by
            rw [← Real.rpow_add (by linarith)]
            congr 1
            have : s (i + c) = s i + (c : ℝ) / m := by linarith
            rw [this]; ring
        _ ≤ (2 : ℝ) ^ p.T (i + c) := hB.2.2.1
    · exact hroom2
  -- the jmid index
  refine ⟨⟨mid - i, hjmid⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb; simp only; omega
  · intro b hb; simp only; omega
  · simp only; rw [hjeq]; exact (hM.2.1).le
  · simp only; rw [hjeq]; exact hrLe mid hmidm
  · simp only; rw [hjeq]; exact hwidth
  · intro b hb
    simp only
    rw [hjeq]
    have hcb : c ≤ p.lev b := by omega
    have hlevA : p.lev (p.par^[c] b) = i := by
      have := (Broad.iterate_par_spec hp.toOriginal c b hcb).1
      change p.lev (p.par^[c] b) = p.lev b - c at this
      rw [this, hb]; omega
    have hmb : p.lev b - mid ≤ p.lev b := Nat.sub_le _ _
    have hlevM : p.lev (p.par^[p.lev b - mid] b) = mid := by
      have := (Broad.iterate_par_spec hp.toOriginal (p.lev b - mid) b hmb).1
      change p.lev (p.par^[p.lev b - mid] b) = p.lev b - (p.lev b - mid) at this
      rw [this]; omega
    rw [hlevM, hlevA, hb, clock_div_eq hTab, clock_div_eq hTmb]
    apply list_sum_of_quarters (div_nonneg haA.le hq.le)
    · -- the time direction
      calc Lp * (((2 : ℝ) ^ (p.T (i + c) - p.T i))⁻¹ * (2 * θ))
          = (Lp * ((2 : ℝ) ^ (p.T (i + c) - p.T i))⁻¹) * (2 * θ) := by ring
        _ ≤ (1 / 8) * (2 * θ) := mul_le_mul_of_nonneg_right hLpClock (by positivity)
        _ = θ / 4 := by ring
    · -- the depth direction
      have e : Lp * (2 * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹ *
          (δ (d.N k) (p.r mid) / δ (d.N k) (p.r i)))) =
          (16 * Lp * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹) *
            (δ (d.N k) (p.r mid) / δ (d.N k) (p.r i))) / 8 := by ring
      rw [e]; linarith
    · -- the transversal direction
      set B := (((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^
        FixedSourcePowers.jet * (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
      (coreK p τ ^ FixedSourcePowers.coreRadius *
        (1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))))) with hBdef
      have e : Lp * (((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^
          FixedSourcePowers.jet * (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
          (coreK p τ ^ FixedSourcePowers.coreRadius *
            ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
              (((2 : ℝ) ^ (p.T (i + c) - p.T mid))⁻¹ * (6 * θ))))) =
          (24 * Lp * B * ((2 : ℝ) ^ (p.T (i + c) - p.T mid))⁻¹) * (θ / 4) := by
        rw [hBdef]; ring
      rw [e]
      calc (24 * Lp * B * ((2 : ℝ) ^ (p.T (i + c) - p.T mid))⁻¹) * (θ / 4) ≤ 1 * (θ / 4) :=
            mul_le_mul_of_nonneg_right hclock (by positivity)
        _ = θ / 4 := one_mul _
    · linarith


set_option maxHeartbeats 2000000 in
/-- **The list block of one sample**: `list_lane` with its powers (`list_powers`) and rooms
(`list_room`) from `Lp ≤ N^(κ₁ gain L/8)` and one geometry exponent `g` bounding the core envelope,
`κ`, `K_d` and `N^(2 δ₀ L)`. -/
theorem list_block (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hs : ∀ l, s l = ((l : ℝ) + 1) / m) (hm : 0 < m) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1)
    (hδ0 : 0 ≤ δ₀) (hδm : 4 * δ₀ * (m : ℝ) ≤ κ₁)
    {Ep : ℕ} {precision loss gain : ℝ} (hprec : 1 ≤ precision) (hloss : 0 ≤ loss)
    (hloss1 : loss ≤ 1) (hgain : 0 < gain) (hgm : 8 ≤ gain * (m : ℝ)) {i nfam : ℕ}
    (hib : i + childOffset κ₁ Ep precision gain m < m)
    (hcfam : childOffset κ₁ Ep precision gain m < nfam)
    {τ θ Lp ρ aA q : ℝ} (hτ : 0 ≤ τ)
    (hθdef : θ = thetaOf Ep precision loss gain (d.N k) d.L (p.r i)
      (p.r (i + childOffset κ₁ Ep precision gain m)) (p.T i)
      (p.T (i + childOffset κ₁ Ep precision gain m)))
    (haA : 0 < aA) (hq : 0 < q)
    (hLp0 : 0 ≤ Lp) (hLp : Lp ≤ d.N k ^ (κ₁ * (gain * d.L) / 8)) (hLpρ : Lp * ρ ≤ θ / 8)
    (hLpClock : Lp * ((2 : ℝ) ^ (p.T (i + childOffset κ₁ Ep precision gain m) - p.T i))⁻¹ ≤ 1 / 8)
    {g : ℝ} (hg0 : 0 ≤ g) (hKg : coreK p τ ≤ d.N k ^ g) (hκg : p.κ ≤ d.N k ^ g)
    (hKdg : d.K k ≤ d.N k ^ g) (hδg : 2 * δ₀ * d.L ≤ g)
    (hbudget : (((3 * FixedSourcePowers.coreRadius + 58 + 7) * FixedSourcePowers.jet +
      FixedSourcePowers.coreRadius + 12 : ℕ) : ℝ) * g ≤ κ₁ * (gain * d.L) / 64)
    (h432 : 432 ≤ d.N k ^ (κ₁ * (gain * d.L) / 64)) (h2a : 2 ≤ d.N k ^ (gain * d.L)) :
    ∃ jmid : Fin nfam,
      (∀ b, p.lev b = i + childOffset κ₁ Ep precision gain m → (i + (jmid : ℕ)) ≤ p.lev b) ∧
      (∀ b, p.lev b = i + childOffset κ₁ Ep precision gain m →
        p.lev b - childOffset κ₁ Ep precision gain m ≤ (i + (jmid : ℕ))) ∧
      0 ≤ p.r ((i + (jmid : ℕ))) ∧ p.r ((i + (jmid : ℕ))) ≤ d.L ∧
      δ (d.N k) (p.r ((i + (jmid : ℕ)))) ≤ δ (d.N k) (p.r i) ∧
      (∀ b, p.lev b = i + childOffset κ₁ Ep precision gain m →
        ((aA / q) * Lp) * ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
            ((2 : ℝ) ^ p.T (p.lev (p.par^[childOffset κ₁ Ep precision gain m] b)))⁻¹) * (2 * θ) +
          (2 * (coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹ * (δ (d.N k) (p.r ((i + (jmid : ℕ)))) /
            δ (d.N k) (p.r (p.lev (p.par^[childOffset κ₁ Ep precision gain m] b))))) +
            ((coreK p τ ^ (3 * FixedSourcePowers.coreRadius + 58 + 7)) ^ FixedSourcePowers.jet *
              (p.κ + coreK p τ ^ 14 * (coreK p τ ^ 6)⁻¹)) *
              (coreK p τ ^ FixedSourcePowers.coreRadius *
                ((1 + 2 * (p.κ * d.N k ^ (2 * δ₀ * d.L)) * (1 + (d.K k + 2 * p.κ ^ 2))) *
                ((((2 : ℝ) ^ p.T (p.lev b))⁻¹ /
                  ((2 : ℝ) ^ p.T (p.lev (p.par^[p.lev b - (i + (jmid : ℕ))] b)))⁻¹) *
                    (6 * θ))))) +
          ρ) ≤ (aA / q) * θ) := by
  have hN2 : (2 : ℝ) ≤ d.N k := hd.1 k
  have hN1 : (1 : ℝ) < d.N k := by linarith
  have hL : 0 < d.L := hd.2.2.2.1
  have hκp1 : 1 ≤ p.κ := hp.1
  obtain ⟨hK2304, -, -, -⟩ :=
    Submission.Lib.K4NativePreparationNumerics.native_pre_geometry_envelope_bounds
      (source := d.K k) hκp1 hN1.le (by linarith : 0 ≤ τ + τ)
  have hK0 : 0 < coreK p τ := lt_of_lt_of_le (by norm_num) hK2304
  have hA : 0 ≤ κ₁ * (gain * d.L) := by positivity
  obtain ⟨hA₁, hA₂⟩ := list_powers (A := κ₁ * (gain * d.L)) hN1 hK0 (by linarith) (zero_le_one.trans (hd.2.2.1.1 k)) hg0
    hA hLp0 (by rwa [show κ₁ * (gain * d.L) / 8 = κ₁ * (gain * d.L) / 8 from rfl]) hKg hκg hKdg
    hδg hbudget h432
  obtain ⟨hroom1, hroom2⟩ := list_room (L := d.L) (precision := precision) (loss := loss)
    (Ep := Ep) (e₁ := κ₁ * (gain * d.L) / 4) (e₂ := κ₁ * (gain * d.L) / 4) hL hκ hκ1 hδ0 hδm
    hprec hloss hloss1 hgain hm hgm le_rfl le_rfl
  exact list_lane hd hp hs hm hκ hκ1 hδ0 hδm hprec hloss hgain hib hcfam hτ hθdef haA hq hLp0 hLpρ
    hLpClock (by positivity) (by positivity) hA₁ hA₂ h2a hroom1 hroom2

end Lane

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
