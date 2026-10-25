-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleAtNumerics, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- Sample-level numerics of the outer assembly (session x1088).

* `residual_velocity_le`: velocities on the broad residual are at most `2 K_d`
  (`Qp.velocity_bound` on the base).
* `gain_scaled_le`: `gain ((Ep+1) precision + 3) depth ≤ (1-d₁)² κ₁²/2^48`.
* `childOffset_div_le`: `childOffset/m ≤ 2 ((Ep+1) precision + 3) gain/κ₁` once
  `1/m ≤ gain/κ₁`.
* `eps_exponent_le`: the exponent of x1095's floor `epsOf ≥ N^(-X)/2` is at most
  `3 ((Ep+1) precision + 3) gain L/κ₁`.
* `thetaN_le_theta`: the native fit target `N^(-gtc gain L)` is below `θ` once
  `64 ((Ep+1) precision + 3)/κ₁ ≤ gtc` and `2 ≤ N^(gain L)`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Glue
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleScalars
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordStateMeshLower

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

noncomputable section

/-- **Velocities on the broad residual.** -/
theorem residual_velocity_le {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {m : ℕ} {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
    (Q : PreparedAngularPath d k p m H u τ) {i stop : ℕ} {a₁ A : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a₁ A θ} {r fraction : ℝ} (R : BroadResidual F r fraction) :
    ∀ w, ∀ z ∈ R.residual w, ‖Parent.v z.1‖ ≤ 2 * d.K k := by
  intro w z hz
  have hb := broadResidual_subset_base R w hz
  have hv := Q.velocity_bound w z hb
  calc ‖Parent.v z.1‖ ≤ ∑ j : Fin 2, |Parent.v z.1 j| :=
        Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _
    _ ≤ ∑ _j : Fin 2, d.K k := Finset.sum_le_sum (fun j _ => hv j)
    _ = 2 * d.K k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- **The gain is tiny** against the depth and the precision. -/
theorem gain_scaled_le (tune : Tuning) {κ₁ d₁ precision loss e0 : ℝ} {Ep : ℕ}
    (hκ : 0 < κ₁) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (hprec : 1 ≤ precision) (hloss : 0 < loss)
    (hloss1 : loss ≤ 1) (he0 : 0 < e0) :
    gainOf tune κ₁ d₁ Ep precision loss e0 *
        ((((Ep : ℝ) + 1) * precision + 3) * tune.depth κ₁ d₁ Ep precision loss) ≤
      (1 - d₁) ^ 2 * κ₁ ^ 2 / 2 ^ 48 := by
  have hg := gainOf_le_cap (tune := tune) (κ₁ := κ₁) (d₁ := d₁) (Ep := Ep)
    (precision := precision) (loss := loss) (e0 := e0)
  have hg0 := gainOf_pos (tune := tune) (Ep := Ep) hκ hd₁ hprec hloss he0
  have hD := tune.one_le_depth κ₁ d₁ Ep precision loss
  have hB0 := tune.budget_pos κ₁ d₁ Ep precision loss
  have hB1 := tune.budget_le_one κ₁ d₁ Ep precision loss
  have hE : (1 : ℝ) ≤ (Ep : ℝ) + 1 := by have := (Nat.cast_nonneg Ep : (0 : ℝ) ≤ Ep); linarith
  have hP : (1 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by nlinarith
  set P := ((Ep : ℝ) + 1) * precision + 3
  set D := tune.depth κ₁ d₁ Ep precision loss
  set B := tune.budget κ₁ d₁ Ep precision loss
  have hPD : 1 ≤ P * D := one_le_mul_of_one_le_of_one_le hP hD
  calc gainOf tune κ₁ d₁ Ep precision loss e0 * (P * D)
      ≤ gainCap tune κ₁ d₁ Ep precision loss * (P * D) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
    _ = loss * (1 - d₁) ^ 2 * κ₁ ^ 2 * B / (2 ^ 48 * ((Ep : ℝ) + 1) * P * D) := by
        have hgc : gainCap tune κ₁ d₁ Ep precision loss =
            loss * (1 - d₁) ^ 2 * κ₁ ^ 2 * B / (2 ^ 48 * ((Ep : ℝ) + 1) * P ^ 2 * D ^ 2) := rfl
        rw [hgc]
        have hP0 : P ≠ 0 := by positivity
        have hD0 : D ≠ 0 := by positivity
        field_simp
    _ ≤ (1 - d₁) ^ 2 * κ₁ ^ 2 / 2 ^ 48 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have h1 : loss * B ≤ 1 := by nlinarith
        have h2 : (1 : ℝ) ≤ ((Ep : ℝ) + 1) * P * D := by
          have := one_le_mul_of_one_le_of_one_le hE hPD
          linarith [show ((Ep : ℝ) + 1) * P * D = ((Ep : ℝ) + 1) * (P * D) by ring]
        have h0 : 0 ≤ (1 - d₁) ^ 2 * κ₁ ^ 2 := by positivity
        calc loss * (1 - d₁) ^ 2 * κ₁ ^ 2 * B * 2 ^ 48 = ((1 - d₁) ^ 2 * κ₁ ^ 2) * (loss * B) *
              2 ^ 48 := by ring
          _ ≤ ((1 - d₁) ^ 2 * κ₁ ^ 2) * 1 * 2 ^ 48 := by gcongr
          _ ≤ (1 - d₁) ^ 2 * κ₁ ^ 2 * (2 ^ 48 * ((Ep : ℝ) + 1) * P * D) := by
              have : (2 : ℝ) ^ 48 ≤ 2 ^ 48 * ((Ep : ℝ) + 1) * P * D := by
                calc (2 : ℝ) ^ 48 = 2 ^ 48 * 1 := by ring
                  _ ≤ 2 ^ 48 * (((Ep : ℝ) + 1) * P * D) := by gcongr
                  _ = _ := by ring
              nlinarith

/-- **The child level** in grid units. -/
theorem childOffset_div_le {κ₁ precision gain : ℝ} {Ep m : ℕ} (hκ : 0 < κ₁) (hm : 0 < m)
    (hg : 0 < gain) (hprec : 1 ≤ precision) (hmg : 1 / (m : ℝ) ≤ gain / κ₁) :
    (childOffset κ₁ Ep precision gain m : ℝ) / m ≤
      2 * (((Ep : ℝ) + 1) * precision + 3) * gain / κ₁ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hco : (childOffset κ₁ Ep precision gain m : ℝ) ≤
      2 * (((Ep : ℝ) + 1) * precision + 2) * gain * m / κ₁ + 2 := by
    unfold childOffset; push_cast
    have := (Nat.ceil_lt_add_one (show 0 ≤ 2 * (((Ep : ℝ) + 1) * precision + 2) * gain * m / κ₁
      by positivity)).le
    linarith
  rw [div_le_iff₀ hmR]
  have h2 : (2 : ℝ) ≤ 2 * gain / κ₁ * m := by
    rw [div_le_div_iff₀ hmR hκ] at hmg
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    nlinarith
  have e : 2 * (((Ep : ℝ) + 1) * precision + 3) * gain / κ₁ * m =
      2 * (((Ep : ℝ) + 1) * precision + 2) * gain * m / κ₁ + 2 * gain / κ₁ * m := by
    field_simp
    ring
  linarith

/-- **The exponent of the state-mesh floor.** -/
theorem eps_exponent_le {L rA rB sA sB precision loss gain κ₁ δ₀ : ℝ} {Ep : ℕ} (hL : 0 < L)
    (hg : 0 < gain) (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hprec : 1 ≤ precision) (hκ : 0 < κ₁)
    (hκ1 : κ₁ ≤ 1) (hrA : |rA - sA * L| ≤ δ₀ * L) (hrB : |rB - sB * L| ≤ δ₀ * L)
    (hsAB : sB - sA ≤ 2 * (((Ep : ℝ) + 1) * precision + 3) * gain / κ₁) (hδ : δ₀ ≤ gain / 100) :
    (rB - rA) + ((Ep : ℝ) + 1) * (precision * gain * L) +
        (2 * (Ep : ℝ) + 2) * (loss * gain * L / ((Ep : ℝ) + 1)) ≤
      3 * (((Ep : ℝ) + 1) * precision + 3) * gain * L / κ₁ := by
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hE1 : (0 : ℝ) < (Ep : ℝ) + 1 := by linarith
  have h1 := (abs_le.mp hrA).1
  have h2 := (abs_le.mp hrB).2
  have hk : (2 * (Ep : ℝ) + 2) * (loss * gain * L / ((Ep : ℝ) + 1)) = 2 * loss * gain * L := by
    field_simp
  rw [hk]
  have hP : (1 : ℝ) ≤ ((Ep : ℝ) + 1) * precision := by nlinarith
  set P := ((Ep : ℝ) + 1) * precision
  -- everything is a multiple of `gain L`
  have hrBA : rB - rA ≤ (sB - sA + 2 * δ₀) * L := by nlinarith
  have hsL : (sB - sA) * L ≤ 2 * (P + 3) * gain / κ₁ * L := mul_le_mul_of_nonneg_right hsAB hL.le
  have hδL : 2 * δ₀ * L ≤ gain / 50 * L := by nlinarith
  have hgk : gain ≤ gain / κ₁ := by
    rw [le_div_iff₀ hκ]; nlinarith
  have hPg : P * gain ≤ P * gain / κ₁ := by
    rw [le_div_iff₀ hκ]; nlinarith [mul_pos (by linarith : (0:ℝ) < P) hg]
  have e1 : 3 * (P + 3) * gain * L / κ₁ =
      (2 * (P + 3) * gain / κ₁ + (P * gain / κ₁ + 3 * (gain / κ₁))) * L := by
    field_simp; ring
  rw [e1]
  have hgL : 0 ≤ gain * L := by positivity
  have hlg : 2 * loss * gain * L ≤ 2 * (gain / κ₁) * L := by
    have : loss * gain ≤ gain / κ₁ := by nlinarith
    nlinarith
  have hPL : P * (gain * L) ≤ P * gain / κ₁ * L := by
    have := mul_le_mul_of_nonneg_right hPg hL.le
    linarith [show P * gain * L = P * (gain * L) by ring]
  have hδ2 : gain / 50 * L ≤ gain / κ₁ * L := by
    apply mul_le_mul_of_nonneg_right _ hL.le
    linarith [show gain / 50 ≤ gain by linarith]
  nlinarith

/-- **The child's state mesh resolves to the end** (`eps_resolved`'s room). -/
theorem eps_fit (tune : Tuning) {κ₁ d₁ precision loss e0 L δ₀ rA rB sA sB : ℝ} {Ep : ℕ}
    (hL : 0 < L) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (hprec : 1 ≤ precision)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (he0 : 0 < e0)
    (hrA : |rA - sA * L| ≤ δ₀ * L) (hrB : |rB - sB * L| ≤ δ₀ * L)
    (hsAB : sB - sA ≤
      2 * (((Ep : ℝ) + 1) * precision + 3) * gainOf tune κ₁ d₁ Ep precision loss e0 / κ₁)
    (hδ : δ₀ ≤ gainOf tune κ₁ d₁ Ep precision loss e0 / 100)
    (hg8 : gainOf tune κ₁ d₁ Ep precision loss e0 ≤ 1 / 8) (hsB : sB ≤ 1 / 2) :
    (rB - rA) + ((Ep : ℝ) + 1) * (precision * gainOf tune κ₁ d₁ Ep precision loss e0 * L) +
        (2 * (Ep : ℝ) + 2) * (loss * gainOf tune κ₁ d₁ Ep precision loss e0 * L / ((Ep : ℝ) + 1)) ≤
      L - rB := by
  set g := gainOf tune κ₁ d₁ Ep precision loss e0 with hgdef
  have hg : 0 < g := gainOf_pos hκ hd₁ hprec hloss he0
  have h1 := eps_exponent_le (Ep := Ep) hL hg hloss hloss1 hprec hκ hκ1 hrA hrB hsAB hδ
  have hgP := gain_scaled_le tune (Ep := Ep) hκ hd₀ hd₁ hprec hloss hloss1 he0
  rw [← hgdef] at hgP
  have hrB' := (abs_le.mp hrB).2
  have hδ14 : δ₀ ≤ 1 / 4 := by linarith
  have hD := tune.one_le_depth κ₁ d₁ Ep precision loss
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hP0 : 0 ≤ ((Ep : ℝ) + 1) * precision + 3 := by
    have : (0 : ℝ) ≤ precision := by linarith
    positivity
  have h2 : g * (((Ep : ℝ) + 1) * precision + 3) ≤ (1 - d₁) ^ 2 * κ₁ ^ 2 / 2 ^ 48 := by
    refine le_trans ?_ hgP
    apply mul_le_mul_of_nonneg_left _ hg.le
    nlinarith
  have h3 : (1 - d₁) ^ 2 * κ₁ ^ 2 / 2 ^ 48 ≤ κ₁ / 12 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    have : (1 - d₁) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hsmall : 3 * (((Ep : ℝ) + 1) * precision + 3) * g * L / κ₁ ≤ L / 4 := by
    rw [div_le_iff₀ hκ]
    have h4 : g * (((Ep : ℝ) + 1) * precision + 3) ≤ κ₁ / 12 := h2.trans h3
    have e : 3 * (((Ep : ℝ) + 1) * precision + 3) * g * L =
        3 * L * (g * (((Ep : ℝ) + 1) * precision + 3)) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 3 * L)
    nlinarith
  have hroom : L / 4 ≤ L - rB := by nlinarith
  linarith

/-- `6 δ₀ L ≤ kexp/8` from the tolerance. -/
theorem six_delta_le (tune : Tuning) {κ₁ d₁ precision loss gain L δ₀ : ℝ} {Ep : ℕ}
    (hL : 0 < L) (hloss : 0 < loss) (hg : 0 < gain) (hδ0 : 0 ≤ δ₀)
    (hδ : δ₀ ≤ tolOf tune κ₁ d₁ Ep precision loss gain) :
    6 * (δ₀ * L) ≤ loss * gain * L / ((Ep : ℝ) + 1) / 8 := by
  have h := hδ.trans (tolOf_le tune κ₁ d₁ Ep hloss hg)
  have hE : (0 : ℝ) < (Ep : ℝ) + 1 := by positivity
  have e : loss * gain * L / ((Ep : ℝ) + 1) / 8 =
      (loss * gain / (10000 * ((Ep : ℝ) + 1))) * L * 1250 := by
    field_simp; ring
  rw [e]
  have : δ₀ * L ≤ (loss * gain / (10000 * ((Ep : ℝ) + 1))) * L :=
    mul_le_mul_of_nonneg_right h hL.le
  have h0 : 0 ≤ δ₀ * L := by positivity
  nlinarith

/-- **The native fit target lies below `θ`.** -/
theorem thetaN_le_theta {N L rA rB sA sB precision loss gain κ₁ δ₀ gtc : ℝ} {Ep TA TB : ℕ}
    (hN : 1 < N) (hL : 0 < L) (hg : 0 < gain) (hloss : 0 < loss) (hloss1 : loss ≤ 1)
    (hprec : 1 ≤ precision) (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hrA : |rA - sA * L| ≤ δ₀ * L)
    (hrB : |rB - sB * L| ≤ δ₀ * L)
    (hsAB : sB - sA ≤ 2 * (((Ep : ℝ) + 1) * precision + 3) * gain / κ₁) (hδ : δ₀ ≤ gain / 100)
    (hgtc : 64 * (((Ep : ℝ) + 1) * precision + 3) / κ₁ ≤ gtc) (h2 : 2 ≤ N ^ (gain * L)) :
    N ^ (-(gtc * gain * L)) ≤ thetaOf Ep precision loss gain N L rA rB TA TB := by
  have hNp : 0 < N := by linarith
  have hX := eps_exponent_le (Ep := Ep) hL hg hloss hloss1 hprec hκ hκ1 hrA hrB hsAB hδ
  set X := (rB - rA) + ((Ep : ℝ) + 1) * (precision * gain * L) +
    (2 * (Ep : ℝ) + 2) * (loss * gain * L / ((Ep : ℝ) + 1))
  have hfloor := epsOf_lower_power (N := N) (L := L) (rA := rA) (rB := rB) (precision := precision)
    (loss := loss) (gain := gain) Ep TA TB hNp
  have hεθ := (sample_scalars_pos (Ep := Ep) (precision := precision) (loss := loss) (gain := gain)
    (L := L) (rA := rA) (rB := rB) (TA := TA) (TB := TB) hN (by positivity) (by
      have : (0 : ℝ) ≤ precision := by linarith
      positivity)).2.2.2.1
  refine le_trans ?_ (hfloor.trans hεθ)
  -- `N^(-gtc gain L) ≤ N^(-X)/2`
  have hE : (0 : ℝ) ≤ Ep := Nat.cast_nonneg Ep
  have hP : (4 : ℝ) ≤ ((Ep : ℝ) + 1) * precision + 3 := by nlinarith
  have hexp : X + gain * L ≤ gtc * gain * L := by
    have h1 : 3 * (((Ep : ℝ) + 1) * precision + 3) * gain * L / κ₁ + gain * L ≤
        64 * (((Ep : ℝ) + 1) * precision + 3) / κ₁ * gain * L := by
      have hgk : gain * L ≤ (((Ep : ℝ) + 1) * precision + 3) * gain * L / κ₁ := by
        rw [le_div_iff₀ hκ]
        have : 0 < gain * L := by positivity
        nlinarith
      have e : 64 * (((Ep : ℝ) + 1) * precision + 3) / κ₁ * gain * L =
          64 * ((((Ep : ℝ) + 1) * precision + 3) * gain * L / κ₁) := by ring
      have e' : 3 * (((Ep : ℝ) + 1) * precision + 3) * gain * L / κ₁ =
          3 * ((((Ep : ℝ) + 1) * precision + 3) * gain * L / κ₁) := by ring
      rw [e, e']
      have : 0 ≤ (((Ep : ℝ) + 1) * precision + 3) * gain * L / κ₁ := by positivity
      linarith
    have h2' : 64 * (((Ep : ℝ) + 1) * precision + 3) / κ₁ * gain * L ≤ gtc * gain * L := by
      have : 0 ≤ gain * L := by positivity
      nlinarith
    linarith
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc N ^ (-(gtc * gain * L)) * 2 ≤ N ^ (-(gtc * gain * L)) * N ^ (gain * L) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_pos_of_pos hNp _).le
    _ = N ^ (-(gtc * gain * L) + gain * L) := by rw [← Real.rpow_add hNp]
    _ ≤ N ^ (-X) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
