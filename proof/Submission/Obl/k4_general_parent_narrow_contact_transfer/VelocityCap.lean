/- Retained from this obligation, o255, branch x0901 at commit 0f8ba410.
   Earlier source attributions in this file are preserved. -/
import Submission.Obl.k4_general_parent_narrow_contact_transfer.Dichotomy

/-!
# A velocity cap for the whole incidence law

Summing the joint cell caps at unit cell scale over the bounded base region
and the bounded native values gives, for every fixed mesh exponent `v > 0`,
eventually `μ {⌊b₃ / N^(-v)⌋ = j} ≤ 100 K⁴ π {⌊w / N^(-v)⌋ = j}`.
-/

namespace Submission.Obl.k4_general_parent_narrow_contact_transfer

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Model

variable {α : Type} [MeasurableSpace α]

/-- Integer points of a box. -/
def intBox (lo hi : ℤ) : Finset (Fin 3 → ℤ) := Fintype.piFinset fun _ => Finset.Icc lo hi

theorem card_intBox_le (lo hi : ℤ) (hlh : lo ≤ hi + 1) :
    ((intBox lo hi).card : ℝ) ≤ ((hi - lo + 1 : ℤ) : ℝ) ^ 3 := by
  unfold intBox
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  have h : ((hi + 1 - lo).toNat : ℝ) = ((hi - lo + 1 : ℤ) : ℝ) := by
    have h0 : 0 ≤ hi + 1 - lo := by omega
    rw [show hi - lo + 1 = hi + 1 - lo by ring]
    exact_mod_cast Int.toNat_of_nonneg h0
  rw [h]
  push_cast
  exact le_refl _

theorem floor_div_mem_Icc {x c B : ℝ} (hc : 0 < c) (hx : |x| ≤ B) :
    ⌊x / c⌋ ∈ Finset.Icc (-⌈B / c⌉ - 1) ⌈B / c⌉ := by
  rw [Finset.mem_Icc]
  rw [abs_le] at hx
  constructor
  · have h1 : -(B / c) ≤ x / c := by rw [← neg_div]; exact div_le_div_of_nonneg_right hx.1 hc.le
    have h2 : -(⌈B / c⌉ : ℝ) ≤ -(B / c) := neg_le_neg (Int.le_ceil _)
    have h3 : -(⌈B / c⌉ : ℝ) - 1 < x / c := by linarith
    have h4 : ((-⌈B / c⌉ - 1 : ℤ) : ℝ) ≤ x / c := by push_cast; linarith
    exact Int.le_floor.mpr h4
  · have h1 : x / c ≤ B / c := div_le_div_of_nonneg_right hx.2 hc.le
    exact Int.floor_le_iff.mpr (by linarith [Int.le_ceil (B / c)])

/-- **Velocity cap.** For every fixed mesh exponent `v > 0`, eventually the
whole incidence law of a velocity bin is at most `400 K⁵` times its palette
weight. -/
theorem velocity_cap_eventually (cfg : Model α) (hv : Valid cfg) {v : ℝ} (hv0 : 0 < v) :
    ∀ᶠ k in atTop, ∀ j : ℤ, cfg.μ k {p | ⌊cfg.b k p.1 3 / cfg.N k ^ (-v)⌋ = j} ≤
      ENNReal.ofReal (400 * cfg.K k ^ 5) * cfg.π k {w | ⌊w / cfg.N k ^ (-v)⌋ = j} := by
  set R : ℝ := max v v⁻¹ + 2 with hR
  have hR1 : 1 < R := by have := le_max_left v v⁻¹; linarith
  have hRv : v ≤ R := by have := le_max_left v v⁻¹; linarith
  have hRpos : 0 < R := by linarith
  have hRv' : R⁻¹ ≤ v := by
    have h1 : v⁻¹ ≤ R := by have := le_max_right v v⁻¹; linarith
    exact (inv_le_comm₀ hv0 hRpos).mp h1
  have hR1' : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1.le
  filter_upwards [hv.caps R hR1] with k hk
  intro j
  obtain ⟨-, -, hjoint⟩ := hk 1 0 v hR1' hR1.le le_rfl (by linarith) hRv' hRv
  have hb := hv.basic k
  obtain ⟨hbm, hνp, hπp, hμK, hρμ, hμsupp, -, -, hbound, hP⟩ := hb
  set N := cfg.N k with hN
  set K := cfg.K k with hK
  have hN2 : 2 ≤ N := hv.scale k
  have hNpos : 0 < N := by linarith
  have hK1 : 1 ≤ K := hv.subpower.1 k
  -- the good set has full measure
  have hgood : ∀ᵐ p ∂cfg.μ k, p.2 ∈ Icc (0 : ℝ) 1 ∧
      |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ K ∧
      |MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k)| ≤ K := by
    have h1 : ∀ᵐ p ∂cfg.μ k, p.2 ∈ Icc (0 : ℝ) 1 := by
      rw [ae_iff]
      refine measure_mono_null ?_ hμsupp
      intro p hp
      simp only [mem_setOf_eq] at hp
      simp only [mem_compl_iff, mem_prod, mem_univ, true_and]
      exact hp
    have h2 : ∀ᵐ p ∂cfg.μ k,
        |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ K := by
      rw [ae_iff] at hbound ⊢
      have hnull : ((cfg.ν k).prod volume) ({l | ¬ (|cfg.b k l 0| + |cfg.b k l 1| +
          |cfg.b k l 3| + |cfg.b k l 4| ≤ K)} ×ˢ (univ : Set ℝ)) = 0 := by
        rw [Measure.prod_prod, hbound, zero_mul]
      have hle := hμK ({l | ¬ (|cfg.b k l 0| + |cfg.b k l 1| +
          |cfg.b k l 3| + |cfg.b k l 4| ≤ K)} ×ˢ (univ : Set ℝ))
      rw [Measure.smul_apply, hnull, smul_zero] at hle
      have hsub' : {p : α × ℝ | ¬ (|cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| +
          |cfg.b k p.1 4| ≤ K)} ⊆ {l | ¬ (|cfg.b k l 0| + |cfg.b k l 1| +
          |cfg.b k l 3| + |cfg.b k l 4| ≤ K)} ×ˢ (univ : Set ℝ) :=
        fun p hp => ⟨hp, mem_univ _⟩
      exact measure_mono_null hsub' (le_antisymm hle zero_le)
    filter_upwards [h1, h2, hP] with p hp1 hp2 hp3
    exact ⟨hp1, hp2, (hp3.1 p.2 hp1).1⟩
  -- covering by finitely many cells and native bins
  set B : ℤ := ⌈K / N ^ (-(1 : ℝ))⌉ with hB
  set Bp : ℤ := ⌈K / N ^ (-(0 : ℝ))⌉ with hBp
  have hsub : {p | ⌊cfg.b k p.1 3 / N ^ (-v)⌋ = j} ∩
      {p | p.2 ∈ Icc (0 : ℝ) 1 ∧
        |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ K ∧
        |MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k)| ≤ K} ⊆
      ⋃ q ∈ intBox (-B - 1) B, ⋃ a ∈ Finset.Icc (-Bp - 1) Bp,
        {p | cfg.z k N 1 p = q ∧
          ⌊(if true then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k)
            else (cfg.x k p.1 p.2) 3) / N ^ (-(0 : ℝ))⌋ = a ∧
          ⌊cfg.b k p.1 3 / N ^ (-v)⌋ = j} := by
    rintro p ⟨hpj, hpt, hpb, hpP⟩
    have hc1 : 0 < N ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hNpos _
    have hc0 : 0 < N ^ (-(0 : ℝ)) := Real.rpow_pos_of_pos hNpos _
    have hx1 : |(cfg.x k p.1 p.2) 1| ≤ K := by
      simp only [Submission.Obl.k4_critical_intercept_concentration.Data.x,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      have := abs_add_le (cfg.b k p.1 0) (p.2 * cfg.b k p.1 3)
      rw [abs_mul, abs_of_nonneg hpt.1] at this
      have : p.2 * |cfg.b k p.1 3| ≤ |cfg.b k p.1 3| := by
        have := abs_nonneg (cfg.b k p.1 3); nlinarith [hpt.2]
      linarith [abs_nonneg (cfg.b k p.1 1), abs_nonneg (cfg.b k p.1 4)]
    have hx2 : |(cfg.x k p.1 p.2) 2| ≤ K := by
      simp only [Submission.Obl.k4_critical_intercept_concentration.Data.x,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      have := abs_add_le (cfg.b k p.1 1) (p.2 * cfg.b k p.1 4)
      rw [abs_mul, abs_of_nonneg hpt.1] at this
      have : p.2 * |cfg.b k p.1 4| ≤ |cfg.b k p.1 4| := by
        have := abs_nonneg (cfg.b k p.1 4); nlinarith [hpt.2]
      linarith [abs_nonneg (cfg.b k p.1 0), abs_nonneg (cfg.b k p.1 3)]
    have ht : |p.2| ≤ K := by rw [abs_of_nonneg hpt.1]; linarith [hpt.2]
    simp only [mem_iUnion]
    refine ⟨cfg.z k N 1 p, ?_, ⌊MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k) /
      N ^ (-(0 : ℝ))⌋, floor_div_mem_Icc hc0 hpP, rfl, ?_, hpj⟩
    · simp only [intBox, Fintype.mem_piFinset]
      intro e
      fin_cases e
      · exact floor_div_mem_Icc hc1 ht
      · exact floor_div_mem_Icc hc1 hx1
      · exact floor_div_mem_Icc hc1 hx2
    · simp
  have hbound_set := measure_mono (μ := cfg.μ k) hsub
  have hconull : cfg.μ k {p : α × ℝ | p.2 ∈ Icc (0 : ℝ) 1 ∧
        |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ K ∧
        |MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k)| ≤ K}ᶜ = 0 := by
    rw [compl_setOf]; exact ae_iff.mp hgood
  rw [measure_inter_conull hconull] at hbound_set
  refine hbound_set.trans ?_
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ q ∈ intBox (-B - 1) B, cfg.μ k (⋃ a ∈ Finset.Icc (-Bp - 1) Bp,
      {p | cfg.z k N 1 p = q ∧
          ⌊(if true then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k)
            else (cfg.x k p.1 p.2) 3) / N ^ (-(0 : ℝ))⌋ = a ∧
          ⌊cfg.b k p.1 3 / N ^ (-v)⌋ = j}) ≤
      ((Finset.Icc (-Bp - 1) Bp).card : ℝ≥0∞) *
        (ENNReal.ofReal (K * N ^ (-3 * 1 - cfg.d * 0)) *
          cfg.π k {w | ⌊w / N ^ (-v)⌋ = j}) := by
    intro q hq
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ a ∈ Finset.Icc (-Bp - 1) Bp, cfg.μ k {p | cfg.z k N 1 p = q ∧
          ⌊(if true then MvPolynomial.eval (cfg.x k p.1 p.2) (cfg.P k)
            else (cfg.x k p.1 p.2) 3) / N ^ (-(0 : ℝ))⌋ = a ∧
          ⌊cfg.b k p.1 3 / N ^ (-v)⌋ = j}
        ≤ ∑ _a ∈ Finset.Icc (-Bp - 1) Bp, ENNReal.ofReal (K * N ^ (-3 * 1 - cfg.d * 0)) *
            cfg.π k {w | ⌊w / N ^ (-v)⌋ = j} :=
          Finset.sum_le_sum fun a _ => hjoint true q a j
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
  apply mul_le_mul_left
  -- numerics
  have hc1 : N ^ (-(1 : ℝ)) = N⁻¹ := by rw [Real.rpow_neg_one]
  have hc0 : N ^ (-(0 : ℝ)) = 1 := by simp
  have hexp : N ^ (-3 * 1 - cfg.d * 0) = (N ^ 3)⁻¹ := by
    rw [show -3 * 1 - cfg.d * 0 = -(3 : ℝ) by ring, Real.rpow_neg hNpos.le]
    norm_cast
  have hBz : (0 : ℤ) ≤ B := Int.ceil_nonneg (div_nonneg (by linarith)
    (Real.rpow_nonneg hNpos.le _))
  have hBpz : (0 : ℤ) ≤ Bp := Int.ceil_nonneg (div_nonneg (by linarith)
    (Real.rpow_nonneg hNpos.le _))
  have hB1 : (B : ℝ) ≤ K * N + 1 := by
    have h := Int.ceil_lt_add_one (K / N ^ (-(1 : ℝ)))
    rw [← hB, hc1, div_inv_eq_mul] at h
    linarith
  have hBp1 : (Bp : ℝ) ≤ K + 1 := by
    have h := Int.ceil_lt_add_one (K / N ^ (-(0 : ℝ)))
    rw [← hBp, hc0, div_one] at h
    linarith
  have hB0 : (0 : ℝ) ≤ B := by exact_mod_cast hBz
  have hBp0 : (0 : ℝ) ≤ Bp := by exact_mod_cast hBpz
  have hcardbox : ((intBox (-B - 1) B).card : ℝ) ≤ (4 * K * N) ^ 3 := by
    have h := card_intBox_le (-B - 1) B (by omega)
    refine h.trans ?_
    have hcast : ((B - (-B - 1) + 1 : ℤ) : ℝ) = 2 * (B : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    apply pow_le_pow_left₀ (by linarith)
    nlinarith
  have hcardI : ((Finset.Icc (-Bp - 1) Bp).card : ℝ) ≤ 6 * K := by
    have hc : (Finset.Icc (-Bp - 1) Bp).card = (Bp + 1 - (-Bp - 1)).toNat := Int.card_Icc _ _
    have h0 : 0 ≤ Bp + 1 - (-Bp - 1) := by omega
    have hcast : (((Bp + 1 - (-Bp - 1)).toNat : ℕ) : ℝ) = 2 * (Bp : ℝ) + 2 := by
      have := Int.toNat_of_nonneg h0
      have h2 : (((Bp + 1 - (-Bp - 1)).toNat : ℕ) : ℤ) = Bp + 1 - (-Bp - 1) := this
      have h3 : (((Bp + 1 - (-Bp - 1)).toNat : ℕ) : ℝ) = ((Bp + 1 - (-Bp - 1) : ℤ) : ℝ) := by
        exact_mod_cast h2
      rw [h3]; push_cast; ring
    rw [hc, hcast]
    linarith
  rw [hexp]
  have hN3 : 0 < N ^ 3 := by positivity
  have hK0 : 0 ≤ K := by linarith
  have hreal : ((intBox (-B - 1) B).card : ℝ) * ((Finset.Icc (-Bp - 1) Bp).card : ℝ) *
      (K * (N ^ 3)⁻¹) ≤ 400 * K ^ 5 := by
    calc ((intBox (-B - 1) B).card : ℝ) * ((Finset.Icc (-Bp - 1) Bp).card : ℝ) *
          (K * (N ^ 3)⁻¹)
        ≤ (4 * K * N) ^ 3 * (6 * K) * (K * (N ^ 3)⁻¹) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hK0 (inv_nonneg.2 hN3.le))
          exact mul_le_mul hcardbox hcardI (Nat.cast_nonneg _) (by positivity)
      _ = 384 * K ^ 5 := by field_simp; ring
      _ ≤ 400 * K ^ 5 := by nlinarith [pow_pos (by linarith : (0:ℝ) < K) 5]
  have hc : 0 ≤ K * (N ^ 3)⁻¹ := mul_nonneg hK0 (inv_nonneg.2 hN3.le)
  calc ((intBox (-B - 1) B).card : ℝ≥0∞) * ((Finset.Icc (-Bp - 1) Bp).card : ℝ≥0∞) *
        ENNReal.ofReal (K * (N ^ 3)⁻¹)
      = ENNReal.ofReal (((intBox (-B - 1) B).card : ℝ) *
          ((Finset.Icc (-Bp - 1) Bp).card : ℝ) * (K * (N ^ 3)⁻¹)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (400 * K ^ 5) := ENNReal.ofReal_le_ofReal hreal

end Model

end

end Submission.Obl.k4_general_parent_narrow_contact_transfer
