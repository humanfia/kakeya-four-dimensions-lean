import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Input
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Blocks

set_option linter.unusedVariables false

/-!
# The normalized coordinates of a coarse block vary little on a deep block

Inside one deep atlas block (depth `s_e`, length `q_e`, width `g_e`, depth width `a_e`), the
four normalized coordinates `zt, zZ, tr, resid` of a coarse block frame vary by explicit
amounts.  The hidden coordinate is controlled through the deep affine graph and the
horizontal slope relations of both affine graphs: an affine form varies on a horizontal tilted
box only through the bracket `x' Δt - t' Δx + Δy`, which is quadratically small there.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

/-- An affine form varies through its horizontal slope combinations and the bracket. -/
theorem affine_variation {L : Fin 4 → ℝ} {t t' x x' y y' E₁ E₃ h r w : ℝ}
    (hslope : |L 1 - x' * L 3| + |L 2 + t' * L 3| ≤ E₁) (hL3 : |L 3| ≤ E₃)
    (ht : |t - t'| ≤ h) (hx : |x - x'| ≤ r)
    (hbr : |x' * (t - t') - t' * (x - x') + (y - y')| ≤ w) :
    |(L 0 + L 1 * t + L 2 * x + L 3 * y) - (L 0 + L 1 * t' + L 2 * x' + L 3 * y')| ≤
      E₁ * (h + r) + E₃ * w := by
  have hid : (L 0 + L 1 * t + L 2 * x + L 3 * y) - (L 0 + L 1 * t' + L 2 * x' + L 3 * y') =
      (L 1 - x' * L 3) * (t - t') + (L 2 + t' * L 3) * (x - x') +
        L 3 * (x' * (t - t') - t' * (x - x') + (y - y')) := by ring
  rw [hid]
  have h1 : |L 1 - x' * L 3| ≤ E₁ := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hslope
  have h2 : |L 2 + t' * L 3| ≤ E₁ := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hslope
  have hE₁ : 0 ≤ E₁ := (abs_nonneg _).trans h1
  have hE₃ : 0 ≤ E₃ := (abs_nonneg _).trans hL3
  calc |(L 1 - x' * L 3) * (t - t') + (L 2 + t' * L 3) * (x - x') +
        L 3 * (x' * (t - t') - t' * (x - x') + (y - y'))|
      ≤ |L 1 - x' * L 3| * |t - t'| + |L 2 + t' * L 3| * |x - x'| +
          |L 3| * |x' * (t - t') - t' * (x - x') + (y - y')| := by
        refine (abs_add_three _ _ _).trans ?_
        simp only [abs_mul, le_refl]
    _ ≤ E₁ * h + E₁ * r + E₃ * w := by
        gcongr
    _ = E₁ * (h + r) + E₃ * w := by ring

/-- On a horizontal tilted box the bracket is quadratically small. -/
theorem deep_bracket {c : Fin 5 → ℝ} {K q g tc t t' x x' y y' : ℝ} (hK : 1 ≤ K) (hq : 0 ≤ q)
    (hx : |x - c 0 - t * c 1| ≤ K * q) (hx' : |x' - c 0 - t' * c 1| ≤ K * q)
    (hy : |y - c 2 - t * c 3 - c 4 * x| ≤ K * q * g)
    (hy' : |y' - c 2 - t' * c 3 - c 4 * x'| ≤ K * q * g)
    (hcen : |c 3 + c 0 + tc * c 1| + |c 4 - tc| ≤ K * q)
    (ht : |t - tc| ≤ q) (ht' : |t' - tc| ≤ q) (hc1 : |c 1| ≤ K) :
    |x' * (t - t') - t' * (x - x') + (y - y')| ≤ 14 * K ^ 2 * q ^ 2 + 2 * K * q * g ∧
      |x - x'| ≤ 4 * K * q := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  set ξ := x - c 0 - t * c 1
  set ξ' := x' - c 0 - t' * c 1
  set ζ := y - c 2 - t * c 3 - c 4 * x
  set ζ' := y' - c 2 - t' * c 3 - c 4 * x'
  have hdt : |t - t'| ≤ 2 * q := by
    calc |t - t'| = |(t - tc) - (t' - tc)| := by ring_nf
      _ ≤ |t - tc| + |t' - tc| := abs_sub _ _
      _ ≤ 2 * q := by linarith
  have hdx : |x - x'| ≤ 4 * K * q := by
    have : x - x' = c 1 * (t - t') + (ξ - ξ') := by simp only [ξ, ξ']; ring
    rw [this]
    calc |c 1 * (t - t') + (ξ - ξ')| ≤ |c 1| * |t - t'| + (|ξ| + |ξ'|) := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul]
          exact add_le_add le_rfl (abs_sub _ _)
      _ ≤ K * (2 * q) + (K * q + K * q) := by gcongr
      _ = 4 * K * q := by ring
  refine ⟨?_, hdx⟩
  have hid : x' * (t - t') - t' * (x - x') + (y - y') =
      ((c 3 + c 0 + tc * c 1) + (t' - tc) * c 1 + ξ') * (t - t') +
        ((c 4 - tc) + (tc - t')) * (x - x') + (ζ - ζ') := by
    simp only [ξ', ζ, ζ']; ring
  rw [hid]
  have hA : |(c 3 + c 0 + tc * c 1) + (t' - tc) * c 1 + ξ'| ≤ 3 * K * q := by
    have h1 : |c 3 + c 0 + tc * c 1| ≤ K * q :=
      le_trans (le_add_of_nonneg_right (abs_nonneg _)) hcen
    calc _ ≤ |c 3 + c 0 + tc * c 1| + |t' - tc| * |c 1| + |ξ'| := by
          refine (abs_add_three _ _ _).trans ?_
          simp only [abs_mul, le_refl]
      _ ≤ K * q + q * K + K * q := by gcongr
      _ = 3 * K * q := by ring
  have hB : |(c 4 - tc) + (tc - t')| ≤ K * q + q := by
    have h1 : |c 4 - tc| ≤ K * q := le_trans (le_add_of_nonneg_left (abs_nonneg _)) hcen
    calc _ ≤ |c 4 - tc| + |tc - t'| := abs_add_le _ _
      _ ≤ K * q + q := by gcongr; rw [abs_sub_comm]; exact ht'
  calc |((c 3 + c 0 + tc * c 1) + (t' - tc) * c 1 + ξ') * (t - t') +
        ((c 4 - tc) + (tc - t')) * (x - x') + (ζ - ζ')|
      ≤ |(c 3 + c 0 + tc * c 1) + (t' - tc) * c 1 + ξ'| * |t - t'| +
          |(c 4 - tc) + (tc - t')| * |x - x'| + (|ζ| + |ζ'|) := by
        refine (abs_add_three _ _ _).trans ?_
        simp only [abs_mul]
        exact add_le_add le_rfl (abs_sub _ _)
    _ ≤ 3 * K * q * (2 * q) + (K * q + q) * (4 * K * q) + (K * q * g + K * q * g) := by
        gcongr
    _ ≤ 14 * K ^ 2 * q ^ 2 + 2 * K * q * g := by
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        nlinarith [mul_nonneg hK0 hq2, mul_nonneg (mul_nonneg hK0 hK0) hq2]


theorem le_sq_of_one_le {K : ℝ} (hK : 1 ≤ K) : K ≤ K ^ 2 := by
  have := mul_le_mul_of_nonneg_left hK (zero_le_one.trans hK)
  nlinarith

/-- A horizontal affine form of a polynomial is unique. -/
theorem horizontalForm_unique {F : MvPolynomial (Fin 4) ℝ} {L L' : Fin 4 → ℝ}
    (h : HorizontalForm F L) (h' : HorizontalForm F L') : L = L' := by
  have key : ∀ x : Fin 4 → ℝ, L 0 + L 1 * x 0 + L 2 * x 1 + L 3 * x 2 =
      L' 0 + L' 1 * x 0 + L' 2 * x 1 + L' 3 * x 2 := by
    intro x
    have e1 := eval_horizontalForm h x
    have e2 := eval_horizontalForm h' x
    linarith
  have h0 := key ![0, 0, 0, 0]
  have h1 := key ![1, 0, 0, 0]
  have h2 := key ![0, 1, 0, 0]
  have h3 := key ![0, 0, 1, 0]
  simp at h0 h1 h2 h3
  funext e
  fin_cases e <;> simp <;> linarith

variable {α : Type} [MeasurableSpace α]

theorem x_one (cfg : Data α) (k : ℕ) (l : α) (t : ℝ) :
    cfg.x k l t 1 = cfg.b k l 0 + t * cfg.b k l 3 := by simp [Data.x]

theorem x_two (cfg : Data α) (k : ℕ) (l : α) (t : ℝ) :
    cfg.x k l t 2 = cfg.b k l 1 + t * cfg.b k l 4 := by simp [Data.x]

theorem x_three (cfg : Data α) (k : ℕ) (l : α) (t : ℝ) :
    cfg.x k l t 3 = cfg.b k l 2 + t * cfg.b k l 5 := by simp [Data.x]

theorem I_sub_center {T : ℕ} {j : Fin (2 ^ T)} {t : ℝ} (ht : t ∈ Data.I T j) :
    |t - (((j : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ T)⁻¹| ≤ ((2 : ℝ) ^ T)⁻¹ := by
  simp only [Data.I, mem_Icc] at ht
  have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  rw [abs_le]
  constructor
  · have := ht.1
    rw [div_le_iff₀ hT] at this
    have : (((j : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ T)⁻¹ - ((2 : ℝ) ^ T)⁻¹ ≤ t := by
      rw [show (((j : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ T)⁻¹ - ((2 : ℝ) ^ T)⁻¹ =
        (((j : ℕ) : ℝ) - 1 / 2) / (2 : ℝ) ^ T by field_simp; ring]
      rw [div_le_iff₀ hT]; linarith
    linarith
  · have := ht.2
    have : t ≤ (((j : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ T)⁻¹ + ((2 : ℝ) ^ T)⁻¹ := by
      rw [show (((j : ℕ) : ℝ) + 1 / 2) * ((2 : ℝ) ^ T)⁻¹ + ((2 : ℝ) ^ T)⁻¹ =
        (((j : ℕ) : ℝ) + 3 / 2) / (2 : ℝ) ^ T by field_simp; ring]
      calc t ≤ (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T := this
        _ ≤ _ := by apply div_le_div_of_nonneg_right _ hT.le; linarith
    linarith

theorem I_sub_I {T : ℕ} {j : Fin (2 ^ T)} {t t' : ℝ} (ht : t ∈ Data.I T j)
    (ht' : t' ∈ Data.I T j) : |t - t'| ≤ ((2 : ℝ) ^ T)⁻¹ := by
  simp only [Data.I, mem_Icc] at ht ht'
  have hT : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  have e : (((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T - ((j : ℕ) : ℝ) / (2 : ℝ) ^ T = ((2 : ℝ) ^ T)⁻¹ := by
    field_simp; ring
  rw [abs_le]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]

/-- **Variation of the coarse normalized coordinates on one deep block.**  For incidences
`(l, t)`, `(l', t')` of one deep block `j` (the second also in the coarse block `i`), with deep
length `qe`, width `ge` and depth width `ae`. -/
theorem deep_coord_variation {cfg : Data α} {k : ℕ} {s se R : ℝ} (hK : 1 ≤ cfg.K k)
    (hN : 0 < cfg.N k)
    (hB : BlocksAt cfg k s R) (hBe : BlocksAt cfg k se R)
    (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (hL : HorizontalForm (cfg.F k s i) L)
    (j : Fin (cfg.n k se)) {l l' : α} {t t' : ℝ}
    (hl : l ∈ cfg.B k se j) (hl' : l' ∈ cfg.B k se j)
    (ht : t ∈ Data.I (cfg.T k se) (cfg.j k se j)) (ht' : t' ∈ Data.I (cfg.T k se) (cfg.j k se j))
    (hl'i : l' ∈ cfg.B k s i) (ht'i : t' ∈ Data.I (cfg.T k s) (cfg.j k s i))
    (F : Frame) (hF : F = blockFrame cfg k s i L)
    (qe ge ae K W : ℝ) (hqe : qe = ((2 : ℝ) ^ cfg.T k se)⁻¹) (hge : ge = cfg.N k ^ (-cfg.κ * se))
    (hae : ae = cfg.N k ^ (-se)) (hKd : K = cfg.K k)
    (hW : W = 14 * K ^ 2 * qe ^ 2 + 2 * K * qe * ge) :
    |F.zt t - F.zt t'| ≤ qe / F.q ∧
    |F.zZ (cfg.b k l) t - F.zZ (cfg.b k l') t'| ≤ 5 * K * qe / F.q ∧
    |F.tr (cfg.b k l) t - F.tr (cfg.b k l') t'| ≤ (10 * K ^ 2 * qe + 2 * K * qe * ge) / (F.q * F.g) ∧
    |F.resid (cfg.b k l) t - F.resid (cfg.b k l') t'| ≤
      (K * (1 + ae / qe) * (5 * K * qe) + K * (1 + ae / qe ^ 2) * W + 2 * K * ae +
        K * (1 + F.a / F.q) * (5 * K * qe) + K * (1 + F.a / F.q ^ 2) * W) / F.a := by
  subst hF hqe hge hae hKd hW
  have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK
  set Fr := blockFrame cfg k s i L with hFr
  set qe := ((2 : ℝ) ^ cfg.T k se)⁻¹ with hqedef
  set ge := cfg.N k ^ (-cfg.κ * se) with hgedef
  set ae := cfg.N k ^ (-se) with haedef
  have hq : 0 < Fr.q := by simp only [Fr, blockFrame]; positivity
  have hqe : 0 < qe := by positivity
  have hg : 0 < Fr.g := Real.rpow_pos_of_pos hN _
  have ha : 0 < Fr.a := Real.rpow_pos_of_pos hN _
  have hge0 : 0 ≤ ge := (Real.rpow_pos_of_pos hN _).le
  have hae0 : 0 ≤ ae := (Real.rpow_pos_of_pos hN _).le
  -- deep geometry
  obtain ⟨hx, hy, -⟩ := hBe.geom j l ((hBe.sets j).2.2 hl) t ht
  obtain ⟨hx', hy', -⟩ := hBe.geom j l' ((hBe.sets j).2.2 hl') t' ht'
  simp only [x_one, x_two] at hx hy hx' hy'
  have hcen := hBe.center j
  have hc1 := hBe.c_bd j 1
  obtain ⟨hbr, hdx⟩ := deep_bracket hK hqe.le hx hx' hy hy' hcen (I_sub_center ht)
    (I_sub_center ht') hc1
  have hdt : |t - t'| ≤ qe := I_sub_I ht ht'
  set x := cfg.b k l 0 + t * cfg.b k l 3 with hxdef
  set x' := cfg.b k l' 0 + t' * cfg.b k l' 3 with hx'def
  set y := cfg.b k l 1 + t * cfg.b k l 4 with hydef
  set y' := cfg.b k l' 1 + t' * cfg.b k l' 4 with hy'def
  have hci : ∀ e, |Fr.c e| ≤ cfg.K k := fun e => hB.c_bd i e
  have hcj : ∀ e, |cfg.c k se j e| ≤ cfg.K k := fun e => hBe.c_bd j e
  -- transverse variation
  have hdy : |y - y'| ≤ 2 * cfg.K k * qe * ge + cfg.K k * qe + 4 * cfg.K k ^ 2 * qe := by
    have hid : y - y' = (y - cfg.c k se j 2 - t * cfg.c k se j 3 - cfg.c k se j 4 * x) -
        (y' - cfg.c k se j 2 - t' * cfg.c k se j 3 - cfg.c k se j 4 * x') +
        cfg.c k se j 3 * (t - t') + cfg.c k se j 4 * (x - x') := by ring
    rw [hid]
    calc _ ≤ |y - cfg.c k se j 2 - t * cfg.c k se j 3 - cfg.c k se j 4 * x| +
          |y' - cfg.c k se j 2 - t' * cfg.c k se j 3 - cfg.c k se j 4 * x'| +
          |cfg.c k se j 3| * |t - t'| + |cfg.c k se j 4| * |x - x'| := by
          refine (abs_add_le _ _).trans ?_
          refine add_le_add ((abs_add_le _ _).trans (add_le_add (abs_sub _ _) ?_)) ?_
          · rw [abs_mul]
          · rw [abs_mul]
      _ ≤ cfg.K k * qe * ge + cfg.K k * qe * ge + cfg.K k * qe + cfg.K k * (4 * cfg.K k * qe) := by
          gcongr
          · exact hcj 3
          · exact hcj 4
      _ = _ := by ring
  -- the coarse affine graph is the one of the atlas
  obtain ⟨L', hL', hL'3, hL's⟩ := hB.affine i
  have hLL : L' = L := horizontalForm_unique hL' hL
  subst hLL
  obtain ⟨Lj, hLj, hLj3, hLjs⟩ := hBe.affine j
  have hfit := (hBe.fit j l hl t ht).1
  have hfit' := (hBe.fit j l' hl' t' ht').1
  rw [eval_horizontalForm hLj] at hfit hfit'
  simp only [Data.x, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hfit hfit'
  have hsj := hLjs l' hl' t' ht'
  have hsc := hL's l' hl'i t' ht'i
  rw [x_one] at hsj hsc
  have hvarj := affine_variation hsj hLj3 hdt hdx hbr
  have hvarc := affine_variation hsc hL'3 hdt hdx hbr
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- zt
    simp only [Frame.zt]
    rw [show (t - Fr.t₀) / Fr.q - (t' - Fr.t₀) / Fr.q = (t - t') / Fr.q by ring, abs_div,
      abs_of_pos hq]
    exact div_le_div_of_nonneg_right hdt hq.le
  · -- zZ
    simp only [Frame.zZ]
    rw [show (cfg.b k l 0 + t * cfg.b k l 3 - Fr.c 0 - t * Fr.c 1) / Fr.q -
        (cfg.b k l' 0 + t' * cfg.b k l' 3 - Fr.c 0 - t' * Fr.c 1) / Fr.q =
        ((x - x') - Fr.c 1 * (t - t')) / Fr.q by simp only [hxdef, hx'def]; ring,
      abs_div, abs_of_pos hq]
    apply div_le_div_of_nonneg_right _ hq.le
    calc |(x - x') - Fr.c 1 * (t - t')| ≤ |x - x'| + |Fr.c 1| * |t - t'| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 4 * cfg.K k * qe + cfg.K k * qe := by gcongr; exact hci 1
      _ = 5 * cfg.K k * qe := by ring
  · -- tr
    simp only [Frame.tr]
    rw [show (cfg.b k l 1 + t * cfg.b k l 4 - Fr.c 2 - t * Fr.c 3 - Fr.c 4 * (cfg.b k l 0 + t * cfg.b k l 3)) /
        (Fr.q * Fr.g) - (cfg.b k l' 1 + t' * cfg.b k l' 4 - Fr.c 2 - t' * Fr.c 3 -
          Fr.c 4 * (cfg.b k l' 0 + t' * cfg.b k l' 3)) / (Fr.q * Fr.g) =
        ((y - y') - Fr.c 3 * (t - t') - Fr.c 4 * (x - x')) / (Fr.q * Fr.g) by
          simp only [hxdef, hx'def, hydef, hy'def]; ring,
      abs_div, abs_of_pos (mul_pos hq hg)]
    apply div_le_div_of_nonneg_right _ (mul_pos hq hg).le
    calc |(y - y') - Fr.c 3 * (t - t') - Fr.c 4 * (x - x')|
        ≤ |y - y'| + |Fr.c 3| * |t - t'| + |Fr.c 4| * |x - x'| := by
          refine (abs_sub _ _).trans ?_
          refine add_le_add ((abs_sub _ _).trans (add_le_add le_rfl ?_)) ?_
          · rw [abs_mul]
          · rw [abs_mul]
      _ ≤ (2 * cfg.K k * qe * ge + cfg.K k * qe + 4 * cfg.K k ^ 2 * qe) + cfg.K k * qe +
            cfg.K k * (4 * cfg.K k * qe) := by
          gcongr
          · exact hci 3
          · exact hci 4
      _ ≤ 10 * cfg.K k ^ 2 * qe + 2 * cfg.K k * qe * ge := by
          have hKq : cfg.K k * qe ≤ cfg.K k ^ 2 * qe :=
            mul_le_mul_of_nonneg_right (le_sq_of_one_le hK) hqe.le
          linarith
  · -- resid
    simp only [Frame.resid]
    have hFL : Fr.L = L' := rfl
    have hFa : Fr.a = cfg.N k ^ (-s) := rfl
    have hFq : Fr.q = ((2 : ℝ) ^ cfg.T k s)⁻¹ := rfl
    rw [hFL]
    set A := (Lj 0 + Lj 1 * t + Lj 2 * x + Lj 3 * y) - (Lj 0 + Lj 1 * t' + Lj 2 * x' + Lj 3 * y')
    set B := (L' 0 + L' 1 * t + L' 2 * x + L' 3 * y) - (L' 0 + L' 1 * t' + L' 2 * x' + L' 3 * y')
    set E := (cfg.b k l 2 + t * cfg.b k l 5 - (Lj 0 + Lj 1 * t + Lj 2 * x + Lj 3 * y)) -
          (cfg.b k l' 2 + t' * cfg.b k l' 5 - (Lj 0 + Lj 1 * t' + Lj 2 * x' + Lj 3 * y'))
    have hid : (cfg.b k l 2 + t * cfg.b k l 5 - (L' 0 + L' 1 * t + L' 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
          L' 3 * (cfg.b k l 1 + t * cfg.b k l 4))) / Fr.a -
        (cfg.b k l' 2 + t' * cfg.b k l' 5 - (L' 0 + L' 1 * t' + L' 2 * (cfg.b k l' 0 + t' * cfg.b k l' 3) +
          L' 3 * (cfg.b k l' 1 + t' * cfg.b k l' 4))) / Fr.a = (A + E - B) / Fr.a := by
      simp only [A, B, E, hxdef, hx'def, hydef, hy'def]; ring
    rw [hid, abs_div, abs_of_pos ha]
    apply div_le_div_of_nonneg_right _ ha.le
    have he : |E| ≤ 2 * cfg.K k * ae := by
      calc |E| ≤ |cfg.b k l 2 + t * cfg.b k l 5 - (Lj 0 + Lj 1 * t + Lj 2 * x + Lj 3 * y)| +
            |cfg.b k l' 2 + t' * cfg.b k l' 5 - (Lj 0 + Lj 1 * t' + Lj 2 * x' + Lj 3 * y')| :=
            abs_sub _ _
        _ ≤ cfg.K k * ae + cfg.K k * ae := add_le_add hfit hfit'
        _ = 2 * cfg.K k * ae := by ring
    have hA : |A| ≤ cfg.K k * (1 + ae / qe) * (qe + 4 * cfg.K k * qe) +
        cfg.K k * (1 + ae / qe ^ 2) * (14 * cfg.K k ^ 2 * qe ^ 2 + 2 * cfg.K k * qe * ge) := hvarj
    have hBb : |B| ≤ cfg.K k * (1 + Fr.a / Fr.q) * (qe + 4 * cfg.K k * qe) +
        cfg.K k * (1 + Fr.a / Fr.q ^ 2) * (14 * cfg.K k ^ 2 * qe ^ 2 + 2 * cfg.K k * qe * ge) := by
      rw [hFa, hFq]; exact hvarc
    have h3 : qe + 4 * cfg.K k * qe ≤ 5 * cfg.K k * qe := by
      have := mul_le_mul_of_nonneg_right hK hqe.le
      linarith
    calc |A + E - B| ≤ |A| + |E| + |B| := by
          refine (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (cfg.K k * (1 + ae / qe) * (qe + 4 * cfg.K k * qe) +
            cfg.K k * (1 + ae / qe ^ 2) * (14 * cfg.K k ^ 2 * qe ^ 2 + 2 * cfg.K k * qe * ge)) +
          2 * cfg.K k * ae +
          (cfg.K k * (1 + Fr.a / Fr.q) * (qe + 4 * cfg.K k * qe) +
            cfg.K k * (1 + Fr.a / Fr.q ^ 2) * (14 * cfg.K k ^ 2 * qe ^ 2 + 2 * cfg.K k * qe * ge)) :=
          add_le_add (add_le_add hA he) hBb
      _ ≤ (cfg.K k * (1 + ae / qe) * (5 * cfg.K k * qe) +
            cfg.K k * (1 + ae / qe ^ 2) * (14 * cfg.K k ^ 2 * qe ^ 2 + 2 * cfg.K k * qe * ge)) +
          2 * cfg.K k * ae +
          (cfg.K k * (1 + Fr.a / Fr.q) * (5 * cfg.K k * qe) +
            cfg.K k * (1 + Fr.a / Fr.q ^ 2) * (14 * cfg.K k ^ 2 * qe ^ 2 + 2 * cfg.K k * qe * ge)) := by
          gcongr
      _ = _ := by ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
