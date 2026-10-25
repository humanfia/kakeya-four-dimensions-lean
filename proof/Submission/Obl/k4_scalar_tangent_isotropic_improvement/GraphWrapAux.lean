import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphStage
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphRows

/-!
# Auxiliary facts for the asymptotic velocity-graph wrapper

Frozen-coordinate forms of the cells, fine-state palette domination from heaviness, finiteness of
the incidence laws, and the polynomial size of the graph and coarse row-count bounds.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Filter Submission.Lib.K4ContinuousKakeya
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- The frozen physical cell index is `cellIdx` of `physOf`. -/
lemma cellIdx_physOf (w : ℝ) (p : Inc) :
    cellIdx w (physOf p) = fun e => ⌊(![p.2, p.1.2 0 + p.2 * p.1.2 1,
      p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4] : Fin 3 → ℝ) e / w⌋ := by
  funext e
  simp only [cellIdx, physOf_apply]

/-- A fine cell in the frozen `(z, x)` coordinates. -/
lemma preimage_cellSet_eq_frozen (w : ℝ) (f : Fin 3 → ℤ) :
    physOf ⁻¹' cellSet w f = {p : Inc | (fun e => ⌊(![p.2, p.1.2 0 + p.2 * p.1.2 1] : Fin 2 → ℝ) e /
      w⌋) = ![f 0, f 1] ∧ ⌊(p.1.2 2 + p.2 * p.1.2 3 + p.2 ^ 2 * p.1.2 4) / w⌋ = f 2} := by
  ext p
  simp only [Set.mem_preimage, cellSet, Set.mem_ofPred_eq, cellIdx_physOf, funext_iff,
    Fin.forall_fin_two, Fin.forall_fin_succ, Fin.isValue]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.forall_fin_one]
  tauto

/-- Fine-state palette domination from the frozen joint cap and heaviness. -/
lemma palette_of_heavy {ρ : Measure Inc} {E F V : Set Inc} {cap lam Hp πc : ℝ≥0∞}
    (hcap : ρ (F ∩ V) ≤ cap * πc) (hheavy : ρ.restrict E F ≠ 0 → lam ≤ ρ.restrict E F)
    (hHp : cap ≤ Hp * lam) :
    ρ.restrict E (F ∩ V) ≤ Hp * ρ.restrict E F * πc := by
  by_cases h0 : ρ.restrict E F = 0
  · have : ρ.restrict E (F ∩ V) = 0 := measure_mono_null Set.inter_subset_left h0
    rw [this]; exact zero_le
  · calc ρ.restrict E (F ∩ V) ≤ ρ (F ∩ V) := Measure.restrict_le_self _
      _ ≤ cap * πc := hcap
      _ ≤ Hp * lam * πc := by gcongr
      _ ≤ Hp * ρ.restrict E F * πc := by gcongr; exact hheavy h0

/-- A law dominated by a probability prior times Lebesgue, carried on unit times, is finite. -/
lemma isFiniteMeasure_of_dom {ν : Measure (ℕ × (Fin 5 → ℝ))} [IsProbabilityMeasure ν]
    {ρ : Measure Inc} {K : ℝ} (hle : ρ ≤ ENNReal.ofReal K • ν.prod volume)
    (hsupp : ρ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0) : IsFiniteMeasure ρ := by
  constructor
  have h1 : ρ Set.univ ≤ ρ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) + ρ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ := by
    rw [← Set.union_compl_self (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)]
    exact measure_union_le _ _
  rw [hsupp, add_zero] at h1
  calc ρ Set.univ ≤ ρ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := by
        simpa using h1
    _ ≤ (ENNReal.ofReal K • ν.prod volume) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := hle _
    _ = ENNReal.ofReal K * (ν Set.univ * volume (Set.Icc (0 : ℝ) 1)) := by
        rw [Measure.smul_apply, Measure.prod_prod, smul_eq_mul]
    _ < ⊤ := by
        rw [Real.volume_Icc, measure_univ]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp)

/-- The graph bound is polynomial in `U ≥ H₀, N^b'`. -/
lemma graphBd_le {N H₀ b' U : ℝ} (hN : 2 ≤ N) (hH₀ : 1 ≤ H₀) (hUH : H₀ ≤ U)
    (hUY : N ^ b' ≤ U) : graphBd H₀ N b' ≤ 104 * U ^ 3 := by
  have hN0 : 0 < N := by linarith
  have hY : 2 * (3 * H₀) / (N ^ (-b') / 2) = 12 * H₀ * N ^ b' := by
    rw [Real.rpow_neg hN0.le]; field_simp; ring
  have hU1 : 1 ≤ U := le_trans hH₀ hUH
  unfold graphBd
  rw [hY]
  have h1 : 3 * H₀ + 1 ≤ 4 * U := by linarith
  have h2 : 12 * H₀ * N ^ b' + 1 ≤ 13 * U ^ 2 := by
    have : H₀ * N ^ b' ≤ U * U :=
      mul_le_mul hUH hUY (Real.rpow_nonneg hN0.le _) (by linarith)
    nlinarith
  calc 2 * ((3 * H₀ + 1) * (12 * H₀ * N ^ b' + 1)) ≤ 2 * ((4 * U) * (13 * U ^ 2)) := by
        gcongr
    _ = 104 * U ^ 3 := by ring

/-- **The coarse row-count bound at the stage parameters is polynomial in `U`.** -/
lemma rowBound_le {N H₀ K U r r' L b' : ℝ} {B m : ℕ} (hN : 2 ≤ N) (hH₀ : 1 ≤ H₀) (hK : 1 ≤ K)
    (hUH : H₀ ≤ U) (hUK : K ≤ U) (hUY : N ^ b' ≤ U) (hr0 : 0 ≤ r) (hrr : r ≤ r')
    (hr'r : N ^ (r' - r) ≤ H₀) (hr'B : r' ≤ B) (hrL : r ≤ L)
    (hm : m = ⌈N ^ (-b') / N ^ (-r')⌉₊ + 3) :
    rowBound (N ^ (-(B : ℝ))) (N ^ (-r)) (N ^ (-r')) H₀ (N ^ (-L) * (1 + 4 * H₀) * graphBd H₀ N b')
      (graphBd H₀ N b') (200 * K * H₀ ^ 2) H₀ m ≤ 10 ^ 17 * U ^ 25 := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hU1 : 1 ≤ U := le_trans hH₀ hUH
  have hU0 : 0 ≤ U := by linarith
  have hGb := graphBd_le hN hH₀ hUH hUY
  have hGb0 : 0 ≤ graphBd H₀ N b' := by unfold graphBd; positivity
  -- scales
  set wr : ℝ := N ^ (-r) with hwr
  set w' : ℝ := N ^ (-r') with hw'
  set b : ℝ := N ^ (-(B : ℝ)) with hb
  set W : ℝ := N ^ (-b') with hW
  set Y : ℝ := N ^ b' with hYdef
  set Gb : ℝ := graphBd H₀ N b' with hGbdef
  have hwr0 : 0 < wr := Real.rpow_pos_of_pos hN0 _
  have hw'0 : 0 < w' := Real.rpow_pos_of_pos hN0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hN0 _
  have hW0 : 0 < W := Real.rpow_pos_of_pos hN0 _
  have hWY : W * Y = 1 := by rw [hW, hYdef, ← Real.rpow_add hN0]; simp
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hN0 _
  have hres0 : 0 ≤ N ^ (-L) * (1 + 4 * H₀) * Gb := by positivity
  have hwr1 : wr ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hw'wr : w' ≤ wr := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hbw' : b ≤ w' := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hwrw' : wr ≤ H₀ * w' := by
    have : wr = N ^ (r' - r) * w' := by rw [hwr, hw', ← Real.rpow_add hN0]; ring_nf
    rw [this]; exact mul_le_mul_of_nonneg_right hr'r hw'0.le
  have hres : N ^ (-L) ≤ wr := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  set res : ℝ := N ^ (-L) * (1 + 4 * H₀) * Gb with hresdef
  have hreswr : res ≤ (1 + 4 * H₀) * Gb * wr := by
    rw [hresdef]
    have := mul_le_mul_of_nonneg_left hres (by positivity : (0 : ℝ) ≤ (1 + 4 * H₀) * Gb)
    linarith
  -- the separation
  have hmr : W / w' + 3 ≤ (m : ℝ) := by
    rw [hm]; push_cast; have := Nat.le_ceil (W / w'); linarith
  have hden : W ≤ (m : ℝ) * w' - 2 * w' := by
    have := mul_le_mul_of_nonneg_right hmr hw'0.le
    have e : (W / w' + 3) * w' = W + 3 * w' := by field_simp
    linarith
  clear_value wr w' b W Y Gb res
  set eX : ℝ := (5 + 2 * H₀) * w' with heX
  have heX0 : 0 ≤ eX := by positivity
  -- slope error
  have hsl : slopeErr res eX Gb w' m ≤ Y * (2 * res + 2 * eX + 2 * Gb * w') := by
    unfold slopeErr
    have hres0' : 0 ≤ res := hres0
    have hnum : 0 ≤ 2 * res + 2 * eX + 2 * Gb * w' := by positivity
    rw [div_le_iff₀ (lt_of_lt_of_le hW0 hden)]
    calc 2 * res + 2 * eX + 2 * Gb * w' = Y * (2 * res + 2 * eX + 2 * Gb * w') * W := by
          rw [show Y * (2 * res + 2 * eX + 2 * Gb * w') * W =
            (2 * res + 2 * eX + 2 * Gb * w') * (W * Y) by ring, hWY, mul_one]
      _ ≤ Y * (2 * res + 2 * eX + 2 * Gb * w') * ((m : ℝ) * w' - 2 * w') := by
          gcongr
  -- polynomial bounds
  have hU2 : U ≤ U ^ 2 := le_self_pow₀ hU1 (by norm_num)
  have hU3 : U ^ 2 ≤ U ^ 3 := pow_le_pow_right₀ hU1 (by norm_num)
  have hU4 : U ^ 3 ≤ U ^ 4 := pow_le_pow_right₀ hU1 (by norm_num)
  have hU5 : U ^ 4 ≤ U ^ 5 := pow_le_pow_right₀ hU1 (by norm_num)
  have hU6 : U ^ 5 ≤ U ^ 6 := pow_le_pow_right₀ hU1 (by norm_num)
  have hwr' : w' ≤ 1 := le_trans hw'wr hwr1
  have hnumle : 2 * res + 2 * eX + 2 * Gb * w' ≤
      (2 * (1 + 4 * H₀) * Gb + 2 * (5 + 2 * H₀) + 2 * Gb) * wr := by
    have h1 : eX ≤ (5 + 2 * H₀) * wr := by rw [heX]; gcongr
    have h2 : Gb * w' ≤ Gb * wr := by gcongr
    linarith only [hreswr, h1, h2]
  have hpoly1 : Y * (2 * (1 + 4 * H₀) * Gb + 2 * (5 + 2 * H₀) + 2 * Gb) ≤ 1262 * U ^ 5 := by
    have hY' : Y ≤ U := hUY
    have hin : 2 * (1 + 4 * H₀) * Gb + 2 * (5 + 2 * H₀) + 2 * Gb ≤ 1262 * U ^ 4 := by
      have a1 : (1 + 4 * H₀) * Gb ≤ (5 * U) * (104 * U ^ 3) := by
        apply mul_le_mul (by linarith) hGb hGb0 (by positivity)
      have a2 : 5 + 2 * H₀ ≤ 7 * U ^ 4 := by linarith only [hUH, hU1, hU2, hU3, hU4]
      have a3 : Gb ≤ 104 * U ^ 4 := by linarith only [hGb, hU4]
      linarith only [a1, a2, a3]
    calc Y * (2 * (1 + 4 * H₀) * Gb + 2 * (5 + 2 * H₀) + 2 * Gb) ≤ U * (1262 * U ^ 4) := by
          apply mul_le_mul hY' hin (by positivity) hU0
      _ = 1262 * U ^ 5 := by ring
  have hsl2 : slopeErr res eX Gb w' m ≤ 1262 * U ^ 5 * wr := by
    calc slopeErr res eX Gb w' m ≤ Y * (2 * res + 2 * eX + 2 * Gb * w') := hsl
      _ ≤ Y * ((2 * (1 + 4 * H₀) * Gb + 2 * (5 + 2 * H₀) + 2 * Gb) * wr) := by
          gcongr
      _ = Y * (2 * (1 + 4 * H₀) * Gb + 2 * (5 + 2 * H₀) + 2 * Gb) * wr := by ring
      _ ≤ 1262 * U ^ 5 * wr := by gcongr
  have hsl0 : 0 ≤ slopeErr res eX Gb w' m := by
    unfold slopeErr
    have : 0 ≤ res := hres0
    apply div_nonneg (by positivity) (le_trans hW0.le hden)
  have hin2 : interErr res eX Gb H₀ w' m ≤ 3155 * U ^ 6 * wr := by
    unfold interErr
    have b1 : res ≤ 520 * U ^ 6 * wr := by
      have hh : (1 + 4 * H₀) * Gb ≤ 520 * U ^ 6 := by
        have := mul_le_mul (by linarith : 1 + 4 * H₀ ≤ 5 * U) hGb hGb0 (by positivity)
        linarith only [this, hU4, hU5, hU6]
      calc res ≤ (1 + 4 * H₀) * Gb * wr := hreswr
        _ ≤ 520 * U ^ 6 * wr := by gcongr
    have b2 : eX ≤ 7 * U ^ 6 * wr := by
      rw [heX]
      have : 5 + 2 * H₀ ≤ 7 * U ^ 6 := by linarith only [hUH, hU1, hU2, hU3, hU4, hU5, hU6]
      calc (5 + 2 * H₀) * w' ≤ (7 * U ^ 6) * wr := by gcongr
        _ = 7 * U ^ 6 * wr := by ring
    have b3 : slopeErr res eX Gb w' m * H₀ ≤ 1262 * U ^ 6 * wr := by
      calc slopeErr res eX Gb w' m * H₀ ≤ (1262 * U ^ 5 * wr) * U := by gcongr
        _ = 1262 * U ^ 6 * wr := by ring
    have b4 : (Gb + slopeErr res eX Gb w' m) * w' ≤ (104 * U ^ 6 + 1262 * U ^ 6) * wr := by
      have c1 : Gb * w' ≤ 104 * U ^ 6 * wr := by
        have : Gb ≤ 104 * U ^ 6 := by linarith only [hGb, hU4, hU5, hU6]
        calc Gb * w' ≤ (104 * U ^ 6) * wr := by gcongr
          _ = 104 * U ^ 6 * wr := by ring
      have c2 : slopeErr res eX Gb w' m * w' ≤ 1262 * U ^ 6 * wr := by
        calc slopeErr res eX Gb w' m * w' ≤ slopeErr res eX Gb w' m * 1 := by gcongr
          _ ≤ 1262 * U ^ 5 * wr := by rw [mul_one]; exact hsl2
          _ ≤ 1262 * U ^ 6 * wr := by gcongr
      linarith only [c1, c2]
    linarith only [b1, b2, b3, b4]
  have hnb : ((wr + 2 * b) / w' + 2) ^ 3 ≤ 125 * U ^ 3 := by
    have : (wr + 2 * b) / w' + 2 ≤ 5 * U := by
      rw [div_add' _ _ _ hw'0.ne', div_le_iff₀ hw'0]
      have hUw : w' ≤ U * w' := le_mul_of_one_le_left hw'0.le hU1
      have hHw : H₀ * w' ≤ U * w' := mul_le_mul_of_nonneg_right hUH hw'0.le
      linarith only [hwrw', hbw', hUw, hHw]
    calc ((wr + 2 * b) / w' + 2) ^ 3 ≤ (5 * U) ^ 3 := by
          gcongr
      _ = 125 * U ^ 3 := by ring
  unfold rowBound
  have hwrU6 : wr ≤ U ^ 6 * wr := le_mul_of_one_le_left hwr0.le (one_le_pow₀ hU1)
  have hwrU5 : wr ≤ U ^ 5 * wr := le_mul_of_one_le_left hwr0.le (one_le_pow₀ hU1)
  have hf1 : 2 * interErr res eX Gb H₀ w' m / wr + 2 ≤ 6312 * U ^ 6 := by
    rw [div_add' _ _ _ hwr0.ne', div_le_iff₀ hwr0]
    linarith only [hin2, hwrU6]
  have hf2 : 2 * slopeErr res eX Gb w' m / wr + 2 ≤ 2526 * U ^ 5 := by
    rw [div_add' _ _ _ hwr0.ne', div_le_iff₀ hwr0]
    linarith only [hsl2, hwrU5]
  have hH' : 200 * K * H₀ ^ 2 ≤ 200 * U ^ 3 := by
    have : K * H₀ ^ 2 ≤ U * U ^ 2 := by
      apply mul_le_mul hUK (pow_le_pow_left₀ (by linarith) hUH 2) (by positivity) hU0
    have e : U * U ^ 2 = U ^ 3 := by ring
    linarith only [this, e]
  have hin0 : 0 ≤ interErr res eX Gb H₀ w' m := by
    unfold interErr
    have : 0 ≤ res := hres0
    positivity
  have hHU : H₀ ≤ U := hUH
  calc 2 * (200 * K * H₀ ^ 2) ^ 2 * ((((wr + 2 * b) / w' + 2) ^ 3 * H₀) ^ 2 *
        ((2 * interErr res eX Gb H₀ w' m / wr + 2) * (2 * slopeErr res eX Gb w' m / wr + 2)))
      ≤ 2 * (200 * U ^ 3) ^ 2 * (((125 * U ^ 3) * U) ^ 2 * ((6312 * U ^ 6) * (2526 * U ^ 5))) := by
        gcongr
    _ = (2 * 200 ^ 2 * 125 ^ 2 * 6312 * 2526) * U ^ 25 := by ring
    _ ≤ 10 ^ 17 * U ^ 25 := by gcongr; norm_num

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
