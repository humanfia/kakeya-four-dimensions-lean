-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Frame.Point; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Frame.Residual

/-!
# Membership of one incidence in the residual lists

The pointwise part of the residual list construction: an incidence of the block `Q`
carried by a color-one sample event of `Q`, on which the common field holds, has its
scalar cell and residual floor in the residual list of its velocity bin.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent.FieldFrame

variable {α : Type} [MeasurableSpace α] (p : Parent α)

theorem x_one (k : ℕ) (l : α) (t : ℝ) : p.x k l t 1 = p.b k l 0 + t * p.b k l 3 := rfl

theorem base_two (k : ℕ) (l : α) (t : ℝ) : p.base k l t 2 = p.x k l t 2 := rfl

theorem base_eq (k : ℕ) (l : α) (t : ℝ) :
    p.base k l t = ![t, p.x k l t 1, p.x k l t 2] := by
  funext i
  fin_cases i <;> rfl

theorem blockWidth_eq (k : ℕ) (r : ℝ) :
    p.blockWidth k r = (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) := by
  rw [Parent.blockWidth, Parent.blockLen, zpow_neg, zpow_natCast]

/-- Variation of the coarse value inside one scalar cell. -/
theorem transA_cell_variation {G : MvPolynomial (Fin 2) ℝ} (hG : G.totalDegree ≤ 2)
    {M K q σ t tc Z Zc : ℝ} {c : Fin 5 → ℝ} (hM : ∀ e, |G.coeff e| ≤ M) (hK1 : 1 ≤ K)
    (hc : ∀ e, |c e| ≤ K) (hq0 : 0 < q) (hσ0 : 0 < σ) (hδ1 : 3 * K ^ 2 * q * σ ≤ 1)
    (ht : |t| ≤ 1) (hZ : |Z| ≤ K) (htc : |tc - t| ≤ q * σ) (hZc : |Zc - Z| ≤ (K + 1) * q * σ) :
    |transA G (fun t Z => c 2 + c 3 * t + c 4 * Z) tc Zc -
        transA G (fun t Z => c 2 + c 3 * t + c 4 * Z) t Z| ≤
      5832 * M * K ^ 6 * q * σ := by
  have hK0 : 0 ≤ K := by linarith
  have hqσ : 0 ≤ q * σ := by positivity
  have hR : 1 ≤ 3 * K ^ 2 := by nlinarith
  have hx : ∀ i, |(![t, c 2 + c 3 * t + c 4 * Z] : Fin 2 → ℝ) i| ≤ 3 * K ^ 2 := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      have h1 : |c 3 * t| ≤ K := by
        rw [abs_mul]
        calc |c 3| * |t| ≤ K * 1 := mul_le_mul (hc 3) ht (abs_nonneg _) hK0
          _ = K := mul_one K
      have h2 : |c 4 * Z| ≤ K * K := by
        rw [abs_mul]
        exact mul_le_mul (hc 4) hZ (abs_nonneg _) hK0
      calc |c 2 + c 3 * t + c 4 * Z| ≤ |c 2| + |c 3 * t| + |c 4 * Z| := by
            refine (abs_add_le _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ ≤ K + K + K * K := by gcongr; exact hc 2
        _ ≤ 3 * K ^ 2 := by nlinarith
  have hy : ∀ i, |(![tc, c 2 + c 3 * tc + c 4 * Zc] : Fin 2 → ℝ) i -
      (![t, c 2 + c 3 * t + c 4 * Z] : Fin 2 → ℝ) i| ≤ 3 * K ^ 2 * q * σ := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      calc |tc - t| ≤ q * σ := htc
        _ = 1 * (q * σ) := (one_mul _).symm
        _ ≤ 3 * K ^ 2 * (q * σ) := mul_le_mul_of_nonneg_right hR hqσ
        _ = 3 * K ^ 2 * q * σ := by ring
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      have heq : c 2 + c 3 * tc + c 4 * Zc - (c 2 + c 3 * t + c 4 * Z) =
          c 3 * (tc - t) + c 4 * (Zc - Z) := by ring
      rw [heq]
      have h1 : |c 3 * (tc - t)| ≤ K * (q * σ) := by
        rw [abs_mul]
        exact mul_le_mul (hc 3) htc (abs_nonneg _) hK0
      have h2 : |c 4 * (Zc - Z)| ≤ K * ((K + 1) * q * σ) := by
        rw [abs_mul]
        exact mul_le_mul (hc 4) hZc (abs_nonneg _) hK0
      calc |c 3 * (tc - t) + c 4 * (Zc - Z)| ≤ |c 3 * (tc - t)| + |c 4 * (Zc - Z)| :=
            abs_add_le _ _
        _ ≤ K * (q * σ) + K * ((K + 1) * q * σ) := add_le_add h1 h2
        _ = (K ^ 2 + 2 * K) * (q * σ) := by ring
        _ ≤ (3 * K ^ 2) * (q * σ) := by
            apply mul_le_mul_of_nonneg_right _ hqσ
            nlinarith
        _ = 3 * K ^ 2 * q * σ := by ring
  have h := eval2_variation G hG hM hR (by positivity) hδ1 _ _ hx hy
  unfold transA
  calc _ ≤ 216 * M * (3 * K ^ 2) ^ 2 * (3 * K ^ 2 * q * σ) := h
    _ = 5832 * M * K ^ 6 * q * σ := by ring

/-- An incidence of the block `Q` carried by a color-one sample event of `Q`, on which
the common field holds, has its scalar cell and residual floor in the residual list of
its velocity bin. -/
theorem mem_frameLists (k : ℕ) {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)
    (Q : Fin (p.n k r)) {ε₁ E : ℝ} (Cf : Fin 4 → ℝ)
    (hN : 0 < p.N k) (hK1 : 1 ≤ p.K k) (hKH : p.K k ≤ H)
    (hc : ∀ e, |p.c k r Q e| ≤ p.K k)
    (hfieldnum : 2 * p.K k ^ 2 * (p.N k ^ ε₁ * E) ≤ p.N k ^ (-r - v))
    (hvarnum : 5832 * p.N k ^ (m / 1000) * p.K k ^ 6 * p.N k ^ (-m) ≤ p.N k ^ (-r - v))
    (hσK : 3 * p.K k ^ 2 * p.N k ^ (-m) ≤ 1)
    {l : α} {t : ℝ} (ht : t ∈ block (p.T k r) (p.j k r Q)) (hgood : (l, t) ∈ p.baseGood k)
    (hζ : |p.x k l t 1 - p.c k r Q 0 - t * p.c k r Q 1| ≤ p.K k * p.blockLen k r)
    (hU : |p.x k l t 2 - p.c k r Q 2 - t * p.c k r Q 3 - p.c k r Q 4 * p.x k l t 1| ≤
      p.K k * p.blockWidth k r)
    {e : Fin (s.count 1)} (hev : (l, t) ∈ s.event 1 e) (hpar : s.parent 1 e = Q)
    (hfield : ∃ i, l ∈ (s.layers 0).C i ∧
      |p.transPair k r Q ((s.layers 0).G i) (l, t) 0 -
          (Cf 0 + Cf 1 * p.tauN k r Q (l, t) + Cf 2 * p.zetaN k r Q (l, t))| ≤
        p.N k ^ ε₁ * E ∧
      |p.transPair k r Q ((s.layers 0).G i) (l, t) 1 - Cf 3| ≤ p.N k ^ ε₁ * E) :
    ((![⌊((t - p.blockStart k r Q) / p.blockLen k r) / p.N k ^ (-m)⌋,
        ⌊p.zetaN k r Q (l, t) / p.N k ^ (-m)⌋] : Fin 2 → ℤ),
      ⌊(p.signal k l t - eval (p.base k l t)
          (bgPoly (p.blockStart k r Q) (p.blockLen k r) (p.blockWidth k r) (p.c k r Q) Cf)) /
          p.N k ^ (-r - v)⌋) ∈ frameLists p k s Q ⌊p.b k l 3 / p.N k ^ (-m)⌋ := by
  classical
  have hH2 : 2 ≤ H := s.loss_one
  have hσ0 : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
  have ha₂0 : 0 < p.N k ^ (-r - v) := Real.rpow_pos_of_pos hN _
  have hq0 : 0 < p.blockLen k r := blockLen_pos p k r
  have hq1 : p.blockLen k r ≤ 1 := blockLen_le_one p k r
  have hw0 : 0 < p.blockWidth k r := by
    unfold Parent.blockWidth
    exact mul_pos hq0 (Real.rpow_pos_of_pos hN _)
  have hK0 : 0 ≤ p.K k := by linarith
  have hK2 : 1 ≤ p.K k ^ 2 := one_le_pow₀ hK1
  have hσ1 : p.N k ^ (-m) ≤ 1 := by
    have h3 : p.N k ^ (-m) ≤ 3 * p.K k ^ 2 * p.N k ^ (-m) := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 * p.K k ^ 2 by linarith) hσ0.le
      linarith
    linarith
  -- the line and the time
  obtain ⟨htI, hclip⟩ := hgood
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [htI.1], htI.2⟩
  have hb0 : |p.b k l 0| ≤ p.K k := by
    linarith [abs_nonneg (p.b k l 1), abs_nonneg (p.b k l 3), abs_nonneg (p.b k l 4)]
  have hb3 : |p.b k l 3| ≤ p.K k := by
    linarith [abs_nonneg (p.b k l 1), abs_nonneg (p.b k l 0), abs_nonneg (p.b k l 4)]
  have hZ : |p.x k l t 1| ≤ p.K k := by
    rw [x_one]
    calc |p.b k l 0 + t * p.b k l 3| ≤ |p.b k l 0| + |t| * |p.b k l 3| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |p.b k l 0| + 1 * |p.b k l 3| := by gcongr
      _ ≤ p.K k := by
          linarith [abs_nonneg (p.b k l 1), abs_nonneg (p.b k l 4)]
  have hblock := block_eq_Icc p k r Q
  rw [hblock] at ht
  -- the sample event
  obtain ⟨-, -, -, hC0, hCj, -⟩ := s.event_data 1 e (l, t) hev
  obtain ⟨i, hi, hf0, hf1⟩ := hfield
  obtain ⟨-, -, -, -, hdisj0, hlab0, -⟩ := s.layer_valid 0
  have hii : i = s.coarse 1 e := by
    by_contra hne
    exact Set.disjoint_left.mp (hdisj0 i (s.coarse 1 e) hne) hi hC0
  obtain ⟨-, hdeg0, -, hl0, -⟩ := hlab0 i
  obtain ⟨htag0, htag1, -⟩ := hl0 l hi
  obtain ⟨-, -, -, -, -, hlab2, -⟩ := s.layer_valid (1 : Fin 2).succ
  obtain ⟨-, -, -, hl2, -⟩ := hlab2 (s.fine 1 e)
  obtain ⟨-, -, hfit2⟩ := hl2 l hCj
  have hA1 : |p.signal k l t - eval ![t, p.x k l t 2] ((s.layers (1 : Fin 2).succ).G (s.fine 1 e))|
      ≤ H * p.N k ^ (-r - v) := by
    have h := (hfit2 t htI).2
    have hexp : -(![r, r + u, r + v] ((1 : Fin 2).succ)) = -r - v := by
      simp only [Fin.succ_one_eq_two, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      ring
    rw [hexp] at h
    exact h
  -- the true fiber box
  have hz : p.base k l t ∈ p.trueFiberBox k r m H Q ((s.layers 0).tag i) := by
    refine ⟨?_, ?_, ?_⟩
    · show t ∈ block (p.T k r) (p.j k r Q)
      rw [hblock]
      exact ht
    · show |p.x k l t 1 - (((s.layers 0).tag i 1 : ℤ) * p.N k ^ (-m) +
          t * (((s.layers 0).tag i 0 : ℤ) * p.N k ^ (-m)))| ≤ H * p.N k ^ (-m)
      rw [← htag0, ← htag1, x_one]
      have e1 := abs_sub_floor_mul_le (y := p.b k l 0) hσ0
      have e2 := abs_sub_floor_mul_le (y := p.b k l 3) hσ0
      have heq : p.b k l 0 + t * p.b k l 3 - ((⌊p.b k l 0 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m) +
          t * ((⌊p.b k l 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m))) =
          (p.b k l 0 - (⌊p.b k l 0 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)) +
            t * (p.b k l 3 - (⌊p.b k l 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)) := by ring
      rw [heq]
      calc _ ≤ |p.b k l 0 - (⌊p.b k l 0 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)| +
            |t| * |p.b k l 3 - (⌊p.b k l 3 / p.N k ^ (-m)⌋ : ℝ) * p.N k ^ (-m)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ p.N k ^ (-m) + 1 * p.N k ^ (-m) := by gcongr
        _ ≤ H * p.N k ^ (-m) := by
            have := mul_le_mul_of_nonneg_right hH2 hσ0.le
            linarith
    · show |p.x k l t 2 - p.c k r Q 2 - t * p.c k r Q 3 - p.c k r Q 4 * p.x k l t 1| ≤
          H * ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
      rw [← blockWidth_eq]
      exact hU.trans (mul_le_mul_of_nonneg_right hKH hw0.le)
  have hj : s.fine 1 e ∈ s.fineChoices 1 Q i := by
    have := s.fine_mem 1 e
    rwa [hpar, ← hii] at this
  have hA2 : |eval ![t, p.x k l t 2] ((s.layers (1 : Fin 2).succ).G (s.fine 1 e)) -
      eval ![t, p.x k l t 2] ((s.layers 0).G i) - s.offset 1 Q i (s.fine 1 e)| ≤
      H * p.N k ^ (-r - v) := by
    have h := s.offset_fit 1 Q i (s.fine 1 e) hj (p.base k l t) hz
    have hexp : -r - ![u, v] 1 = -r - v := by simp
    rw [hexp] at h
    exact h
  -- the transverse Taylor identity and the common field
  have hY : p.x k l t 2 = p.tiltY k r Q t (p.x k l t 1) + p.blockWidth k r * p.uN k r Q (l, t) := by
    unfold Parent.uN
    field_simp
    ring
  have hA3 : eval ![t, p.x k l t 2] ((s.layers 0).G i) =
      transA ((s.layers 0).G i) (p.tiltY k r Q) t (p.x k l t 1) +
        p.uN k r Q (l, t) * transB ((s.layers 0).G i) (p.tiltY k r Q) (p.blockWidth k r) t
          (p.x k l t 1) +
        p.uN k r Q (l, t) ^ 2 * transD ((s.layers 0).G i) (p.blockWidth k r) := by
    rw [hY, eval_taylor_Y _ hdeg0]
    unfold transA transB transD
    ring
  have hA4 : eval (p.base k l t)
      (bgPoly (p.blockStart k r Q) (p.blockLen k r) (p.blockWidth k r) (p.c k r Q) Cf) =
      (Cf 0 + Cf 1 * p.tauN k r Q (l, t) + Cf 2 * p.zetaN k r Q (l, t)) * p.uN k r Q (l, t) +
        Cf 3 * p.uN k r Q (l, t) ^ 2 := by
    rw [base_eq, eval_bgPoly]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    unfold Parent.tauN Parent.zetaN Parent.uN Parent.tiltY
    ring
  have hUb : |p.uN k r Q (l, t)| ≤ p.K k := by
    unfold Parent.uN Parent.tiltY
    rw [abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
    have heq : p.x k l t 2 - (p.c k r Q 2 + p.c k r Q 3 * t + p.c k r Q 4 * p.x k l t 1) =
        p.x k l t 2 - p.c k r Q 2 - t * p.c k r Q 3 - p.c k r Q 4 * p.x k l t 1 := by ring
    rw [heq]
    exact hU
  have hf0' : |transB ((s.layers 0).G i) (p.tiltY k r Q) (p.blockWidth k r) t (p.x k l t 1) -
      (Cf 0 + Cf 1 * p.tauN k r Q (l, t) + Cf 2 * p.zetaN k r Q (l, t))| ≤ p.N k ^ ε₁ * E := by
    simpa [Parent.transPair] using hf0
  have hf1' : |transD ((s.layers 0).G i) (p.blockWidth k r) - Cf 3| ≤ p.N k ^ ε₁ * E := by
    simpa [Parent.transPair] using hf1
  have hη : 0 ≤ p.N k ^ ε₁ * E := (abs_nonneg _).trans hf1'
  have hres := residual_bound hA1 hA2 hA3 hA4 hf0' hf1' hUb
  -- the scalar cell and its reference point
  have hZ_eq : p.x k l t 1 = p.c k r Q 0 + p.c k r Q 1 * t +
      p.blockLen k r * p.zetaN k r Q (l, t) := by
    unfold Parent.zetaN
    field_simp
    ring
  have ht_eq : t = p.blockStart k r Q +
      p.blockLen k r * ((t - p.blockStart k r Q) / p.blockLen k r) := by
    field_simp
    ring
  set σ := p.N k ^ (-m) with hσ_def
  set a₂ := p.N k ^ (-r - v) with ha₂_def
  set K := p.K k with hK_def
  set t₀ := p.blockStart k r Q with ht₀_def
  set q := p.blockLen k r with hq_def
  set c := p.c k r Q with hc_def
  set uu := (t - t₀) / q with huu
  set ζ := p.zetaN k r Q (l, t) with hζ_def
  set Z := p.x k l t 1 with hZ_def
  set x : ℤ × ℤ := (⌊uu / σ⌋, ⌊ζ / σ⌋) with hx_def
  have htc : |cellTime t₀ q σ x - t| ≤ q * σ := by
    unfold cellTime
    rw [hx_def]
    have h := abs_sub_floor_mul_le (y := uu) hσ0
    have heq : t₀ + q * ((⌊uu / σ⌋ : ℝ) * σ) - t = -(q * (uu - (⌊uu / σ⌋ : ℝ) * σ)) := by
      rw [ht_eq]; ring
    rw [heq, abs_neg, abs_mul, abs_of_pos hq0]
    exact mul_le_mul_of_nonneg_left h hq0.le
  have hZc : |cellMajor t₀ q σ c x - Z| ≤ (K + 1) * q * σ := by
    have h := abs_sub_floor_mul_le (y := ζ) hσ0
    have heq : cellMajor t₀ q σ c x - Z =
        c 1 * (cellTime t₀ q σ x - t) - q * (ζ - (⌊ζ / σ⌋ : ℝ) * σ) := by
      unfold cellMajor
      rw [hZ_eq, hx_def]
      ring
    rw [heq]
    calc |c 1 * (cellTime t₀ q σ x - t) - q * (ζ - (⌊ζ / σ⌋ : ℝ) * σ)|
        ≤ |c 1 * (cellTime t₀ q σ x - t)| + |q * (ζ - (⌊ζ / σ⌋ : ℝ) * σ)| := abs_sub _ _
      _ ≤ K * (q * σ) + q * σ := by
          rw [abs_mul, abs_mul, abs_of_pos hq0]
          gcongr
          · exact hc 1
      _ = (K + 1) * q * σ := by ring
  have hδ1 : 3 * K ^ 2 * q * σ ≤ 1 := by
    calc 3 * K ^ 2 * q * σ = q * (3 * K ^ 2 * σ) := by ring
      _ ≤ 1 * 1 := mul_le_mul hq1 hσK (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hvar := transA_cell_variation hdeg0 (s.coefficient_bound 0 i) hK1 hc hq0 hσ0 hδ1 ht1
    hZ htc hZc
  -- the residual is close to a value of the cell, the coarse and the fine label
  set Xv := p.signal k l t - eval (p.base k l t) (bgPoly t₀ q (p.blockWidth k r) c Cf)
    with hXv
  set A₀ := transA ((s.layers 0).G i) (p.tiltY k r Q) t Z with hA₀
  set Aref := transA ((s.layers 0).G i) (p.tiltY k r Q) (cellTime t₀ q σ x)
    (cellMajor t₀ q σ c x) with hAref
  set off := s.offset 1 Q i (s.fine 1 e) with hoff
  have hclose : |Xv - (Aref + off)| ≤ 4 * H * a₂ := by
    have e1 : (K + K ^ 2) * (p.N k ^ ε₁ * E) ≤ a₂ := by
      have hKK : K + K ^ 2 ≤ 2 * K ^ 2 := by
        have : K ≤ K ^ 2 := by
          rw [sq]
          exact le_mul_of_one_le_left (by linarith) hK1
        linarith
      calc (K + K ^ 2) * (p.N k ^ ε₁ * E) ≤ (2 * K ^ 2) * (p.N k ^ ε₁ * E) :=
            mul_le_mul_of_nonneg_right hKK hη
        _ ≤ a₂ := hfieldnum
    have e2 : 5832 * p.N k ^ (m / 1000) * K ^ 6 * q * σ ≤ a₂ := by
      calc 5832 * p.N k ^ (m / 1000) * K ^ 6 * q * σ =
            q * (5832 * p.N k ^ (m / 1000) * K ^ 6 * σ) := by ring
        _ ≤ 1 * a₂ := mul_le_mul hq1 hvarnum (by positivity) zero_le_one
        _ = a₂ := one_mul _
    have hvar' : |Aref - A₀| ≤ 5832 * p.N k ^ (m / 1000) * K ^ 6 * q * σ := hvar
    have heq : Xv - (Aref + off) = (Xv - A₀ - off) - (Aref - A₀) := by ring
    rw [heq]
    calc _ ≤ |Xv - A₀ - off| + |Aref - A₀| := abs_sub _ _
      _ ≤ (2 * H * a₂ + (K + K ^ 2) * (p.N k ^ ε₁ * E)) +
          5832 * p.N k ^ (m / 1000) * K ^ 6 * q * σ := add_le_add hres hvar'
      _ ≤ 4 * H * a₂ := by
          have hHa : a₂ ≤ H * a₂ := le_mul_of_one_le_left ha₂0.le (by linarith)
          linarith only [e1, e2, hHa]
  have hk := floor_sub_mem ha₂0 hclose
  -- the intercept bin of the coarse label
  set a := ⌊p.b k l 3 / σ⌋ with ha_def
  have hZb : Z = p.b k l 0 + t * p.b k l 3 := x_one p k l t
  have h3 := abs_sub_floor_mul_le (y := p.b k l 3) hσ0
  have haσ : |(a : ℝ) * σ| ≤ K + 1 := by
    calc |(a : ℝ) * σ| = |p.b k l 3 - (p.b k l 3 - (a : ℝ) * σ)| := by ring_nf
      _ ≤ |p.b k l 3| + |p.b k l 3 - (a : ℝ) * σ| := abs_sub _ _
      _ ≤ K + 1 := by linarith
  have hb0 : |p.b k l 0 - cellIntercept t₀ q σ c x a| ≤ (2 * K + 4) * σ := by
    have heq : p.b k l 0 - cellIntercept t₀ q σ c x a =
        -(cellMajor t₀ q σ c x - Z) - t * (p.b k l 3 - a * σ) -
          (-(cellTime t₀ q σ x - t)) * (a * σ) := by
      unfold cellIntercept
      rw [hZb]
      ring
    rw [heq]
    have f1 : |-(cellMajor t₀ q σ c x - Z)| ≤ (K + 1) * σ := by
      rw [abs_neg]
      calc _ ≤ (K + 1) * q * σ := hZc
        _ = q * ((K + 1) * σ) := by ring
        _ ≤ 1 * ((K + 1) * σ) := mul_le_mul_of_nonneg_right hq1 (by positivity)
        _ = (K + 1) * σ := one_mul _
    have f2 : |t * (p.b k l 3 - a * σ)| ≤ σ := by
      rw [abs_mul]
      calc |t| * |p.b k l 3 - a * σ| ≤ 1 * σ :=
            mul_le_mul ht1 h3 (abs_nonneg _) zero_le_one
        _ = σ := one_mul _
    have f3 : |(-(cellTime t₀ q σ x - t)) * (a * σ)| ≤ (K + 1) * σ := by
      rw [abs_mul, abs_neg]
      calc |cellTime t₀ q σ x - t| * |(a : ℝ) * σ| ≤ (q * σ) * (K + 1) :=
            mul_le_mul htc haσ (abs_nonneg _) (by positivity)
        _ = q * ((K + 1) * σ) := by ring
        _ ≤ 1 * ((K + 1) * σ) := mul_le_mul_of_nonneg_right hq1 (by positivity)
        _ = (K + 1) * σ := one_mul _
    calc _ ≤ |-(cellMajor t₀ q σ c x - Z)| + |t * (p.b k l 3 - a * σ)| +
          |(-(cellTime t₀ q σ x - t)) * (a * σ)| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ (K + 1) * σ + σ + (K + 1) * σ := by gcongr
      _ ≤ (2 * K + 4) * σ := by linarith only [hσ0]
  have hbm := floor_sub_mem hσ0 hb0
  have hbmem : ⌊p.b k l 0 / σ⌋ ∈ Finset.Icc
      (⌊cellIntercept t₀ q σ c x a / σ⌋ - (⌈2 * K + 4⌉ + 1))
      (⌊cellIntercept t₀ q σ c x a / σ⌋ + (⌈2 * K + 4⌉ + 1)) := by
    rw [Finset.mem_Icc] at hbm ⊢
    constructor <;> omega
  -- the scalar cell lies in the cell box
  have hu0 : 0 ≤ uu := by
    rw [huu]
    exact div_nonneg (by linarith [ht.1]) hq0.le
  have hu1 : uu ≤ 1 := by
    rw [huu, div_le_one hq0]
    linarith [ht.2]
  have hζb : |ζ| ≤ K := by
    rw [hζ_def]
    unfold Parent.zetaN
    rw [abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    have heq : p.x k l t 1 - p.c k r Q 0 - p.c k r Q 1 * t =
        p.x k l t 1 - p.c k r Q 0 - t * p.c k r Q 1 := by ring
    rw [heq]
    exact hζ
  have hσi : 0 < σ⁻¹ := inv_pos.mpr hσ0
  have hxmem : x ∈ Finset.Icc 0 ⌈σ⁻¹⌉ ×ˢ Finset.Icc (-⌈K * σ⁻¹⌉) ⌈K * σ⁻¹⌉ := by
    rw [hx_def, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    have hζ1 : -K ≤ ζ := (abs_le.mp hζb).1
    have hζ2 : ζ ≤ K := (abs_le.mp hζb).2
    refine ⟨⟨Int.floor_nonneg.mpr (div_nonneg hu0 hσ0.le), ?_⟩, ?_, ?_⟩
    · refine (Int.floor_mono ?_).trans (Int.floor_le_ceil _)
      rw [div_eq_mul_inv]
      calc uu * σ⁻¹ ≤ 1 * σ⁻¹ := mul_le_mul_of_nonneg_right hu1 hσi.le
        _ = σ⁻¹ := one_mul _
    · rw [← Int.floor_neg]
      refine Int.floor_mono ?_
      rw [div_eq_mul_inv, ← neg_mul]
      exact mul_le_mul_of_nonneg_right hζ1 hσi.le
    · refine (Int.floor_mono ?_).trans (Int.floor_le_ceil _)
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hζ2 hσi.le
  -- the coarse label lies in the coarse menu of its tag
  have hi' : i ∈ s.coarseChoices Q ![a, ⌊p.b k l 0 / σ⌋] := by
    have h := s.coarse_mem 1 e
    rw [hpar, ← hii] at h
    have htag : (s.layers 0).tag i = ![a, ⌊p.b k l 0 / σ⌋] := by
      funext z
      fin_cases z
      · exact htag0.symm
      · exact htag1.symm
    rwa [htag] at h
  have hmem := mem_listBuild (cells := Finset.Icc 0 ⌈σ⁻¹⌉ ×ˢ Finset.Icc (-⌈K * σ⁻¹⌉) ⌈K * σ⁻¹⌉)
    (bRange := fun x a => Finset.Icc (⌊cellIntercept t₀ q σ c x a / σ⌋ - (⌈2 * K + 4⌉ + 1))
      (⌊cellIntercept t₀ q σ c x a / σ⌋ + (⌈2 * K + 4⌉ + 1)))
    (choices := s.coarseChoices Q) (fine := s.fineChoices 1 Q)
    (val := fun x i j => ⌊(transA ((s.layers 0).G i) (p.tiltY k r Q) (cellTime t₀ q σ x)
        (cellMajor t₀ q σ c x) + s.offset 1 Q i j) / a₂⌋)
    (L := ⌈4 * H⌉ + 1) (a := a) hxmem hbmem hi' hj hk
  have e : ⌊(Aref + off) / a₂⌋ + (⌊Xv / a₂⌋ - ⌊(Aref + off) / a₂⌋) = ⌊Xv / a₂⌋ := by ring
  unfold frameLists
  rw [← e]
  exact hmem

end Parent.FieldFrame

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
