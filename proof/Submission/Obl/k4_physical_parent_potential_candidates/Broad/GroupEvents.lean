-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/GroupEvents.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.GroupCells
import Submission.Obl.k4_physical_parent_potential_candidates.Broad.Extrapolation
import Submission.Lib.K4HiddenQuadratic

/-!
# Events of the group cells

A group cell of sign `σ` is an observation cell (base cube of side `p` times hidden bin of the
observation `obs B a`) containing a counted core incidence `q'` with `σ ∂₃R_b(q') > 0`. Every
counted incidence `q` of the same cell behaves like `q'`:

* its own intercept is within `ω` of `c₀` (`intercept_close_of_cell`, the cell being thin);
* its hidden derivative has the same sign, so `σ ∂₃R_b(q) ≥ B/κ`: across the cell `∂₃R_b`
  moves by at most `Lip(∂₃R_b)·3p + κ B a / δ` (crude base Lipschitz, constant hidden curvature),
  which is less than the gap `2B/κ` between the two signs.

Also, fitted points of one sign in one thin base cell have nearby hidden coordinates
(`hidden_close_of_fit`), which bounds the number of hidden bins a sign class uses in one cube.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

/-- A polynomial of total degree zero has the same value everywhere. -/
lemma eval_eq_of_totalDegree_eq_zero {n : ℕ} {Q : MvPolynomial (Fin n) ℝ}
    (hQ : Q.totalDegree = 0) (x y : Fin n → ℝ) : MvPolynomial.eval x Q = MvPolynomial.eval y Q := by
  rw [totalDegree_eq_zero_iff_eq_C.mp hQ]
  simp

/-- **Hidden coordinates of fitted points in a thin base cell.**  The fitted residual
`R_b - P - c₀` is quadratic in the hidden direction, so the two-point identity applies to it. -/
lemma hidden_close_of_fit {Rb : MvPolynomial (Fin 4) ℝ} (hR : Rb.totalDegree ≤ 2)
    (P : MvPolynomial (Fin 3) ℝ) (c₀ : ℝ) {Bx V D ϱ : ℝ} (hBx : 1 ≤ Bx) (w w' : Fin 4 → ℝ)
    (hbox : ∀ i, |w i| ≤ Bx) (hbox' : ∀ i, |w' i| ≤ Bx)
    (hbase : |w 0 - w' 0| + |w 1 - w' 1| + |w 2 - w' 2| ≤ ϱ)
    (hval : |MvPolynomial.eval w Rb - MvPolynomial.eval (fun i => w i.castSucc) P - c₀| ≤ V)
    (hval' : |MvPolynomial.eval w' Rb - MvPolynomial.eval (fun i => w' i.castSucc) P - c₀| ≤ V)
    (hder : D ≤ |MvPolynomial.eval w (pderiv 3 Rb)|)
    (hder' : D ≤ |MvPolynomial.eval w' (pderiv 3 Rb)|)
    (hsign : 0 ≤ MvPolynomial.eval w (pderiv 3 Rb) * MvPolynomial.eval w' (pderiv 3 Rb))
    (hsmall : lipBox (pderiv 3 Rb) Bx * ϱ ≤ D) :
    |w 3 - w' 3| * D ≤ 2 * (2 * V + lipBox (Rb - liftBase P) Bx * ϱ) := by
  have hϱ : 0 ≤ ϱ := le_trans (by positivity) hbase
  have hV : 0 ≤ V := le_trans (abs_nonneg _) hval
  have hL : 0 ≤ lipBox (Rb - liftBase P) Bx := lipBox_nonneg _ (by linarith)
  have hLD : 0 ≤ lipBox (pderiv 3 Rb) Bx := lipBox_nonneg _ (by linarith)
  rcases le_or_gt D 0 with hD | hD
  · have : |w 3 - w' 3| * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hD
    have : 0 ≤ 2 * (2 * V + lipBox (Rb - liftBase P) Bx * ϱ) := by positivity
    linarith
  set m := mixPoint w w' with hm
  have hboxm : ∀ i, |m i| ≤ Bx := by
    intro i
    by_cases hi : i = 3
    · subst hi; rw [hm, mixPoint_hidden]; exact hbox 3
    · rw [hm, mixPoint_base w w' i hi]; exact hbox' i
  set G : MvPolynomial (Fin 4) ℝ := Rb - liftBase P with hG
  have hGeval : ∀ x : Fin 4 → ℝ, MvPolynomial.eval x G =
      MvPolynomial.eval x Rb - MvPolynomial.eval (fun i => x i.castSucc) P := by
    intro x; simp [hG, eval_liftBase]
  -- base move on the fitted residual
  have h1 : |MvPolynomial.eval w G - MvPolynomial.eval m G| ≤ lipBox G Bx * ϱ := by
    have := abs_eval_sub_eval_le_box G hBx w m hbox hboxm
    rw [sum_abs_sub_mixPoint] at this
    exact this.trans (mul_le_mul_of_nonneg_left hbase hL)
  have h2 : |MvPolynomial.eval w (pderiv 3 Rb) - MvPolynomial.eval m (pderiv 3 Rb)| ≤ D := by
    have := abs_eval_sub_eval_le_box (pderiv 3 Rb) hBx w m hbox hboxm
    rw [sum_abs_sub_mixPoint] at this
    exact (this.trans (mul_le_mul_of_nonneg_left hbase hLD)).trans hsmall
  -- hidden move: the base points of `m` and `w'` agree
  have hmw' : ∀ i : Fin 4, i ≠ 3 → m i = w' i := fun i hi => mixPoint_base w w' i hi
  have key := hidden_two_point hR m w' hmw'
  have hm3 : m 3 = w 3 := mixPoint_hidden w w'
  rw [hm3] at key
  have hPm : MvPolynomial.eval (fun i => m i.castSucc) P = MvPolynomial.eval (fun i => w' i.castSucc) P := by
    have hfun : (fun i : Fin 3 => m i.castSucc) = (fun i => w' i.castSucc) := by
      funext i
      exact hmw' _ (by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega)
    rw [hfun]
  set a := MvPolynomial.eval w (pderiv 3 Rb) with ha
  set a' := MvPolynomial.eval w' (pderiv 3 Rb) with ha'
  set bb := MvPolynomial.eval m (pderiv 3 Rb) with hbb
  have hsum2 : 2 * D ≤ |a + a'| := by
    rcases lt_trichotomy a 0 with h | h | h
    · have ha'0 : a' ≤ 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      rw [abs_of_neg h] at hder
      rw [abs_of_nonpos ha'0] at hder'
      rw [abs_of_nonpos (by linarith)]
      linarith
    · rw [h, abs_zero] at hder; linarith
    · have ha'0 : 0 ≤ a' := by
        by_contra hc
        push Not at hc
        nlinarith
      rw [abs_of_pos h] at hder
      rw [abs_of_nonneg ha'0] at hder'
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hsum : D ≤ |bb + a'| := by
    have := abs_sub_abs_le_abs_sub (a + a') (bb + a')
    have h3 : (a + a') - (bb + a') = a - bb := by ring
    rw [h3] at this
    linarith
  have hkey : (w 3 - w' 3) * (bb + a') =
      2 * (MvPolynomial.eval m Rb - MvPolynomial.eval w' Rb) := by
    rw [key]; ring
  -- the fitted residual at `m` and at `w'` differ as `R_b` does
  have hFm : MvPolynomial.eval m Rb - MvPolynomial.eval w' Rb =
      (MvPolynomial.eval m G - MvPolynomial.eval w G) +
      (MvPolynomial.eval w Rb - MvPolynomial.eval (fun i => w i.castSucc) P - c₀) -
      (MvPolynomial.eval w' Rb - MvPolynomial.eval (fun i => w' i.castSucc) P - c₀) := by
    rw [hGeval m, hGeval w, hPm]; ring
  calc |w 3 - w' 3| * D ≤ |w 3 - w' 3| * |bb + a'| :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = 2 * |MvPolynomial.eval m Rb - MvPolynomial.eval w' Rb| := by
        rw [← abs_mul, hkey, abs_mul, abs_two]
    _ ≤ 2 * (lipBox G Bx * ϱ + V + V) := by
        gcongr
        rw [hFm]
        calc |(MvPolynomial.eval m G - MvPolynomial.eval w G) +
              (MvPolynomial.eval w Rb - MvPolynomial.eval (fun i => w i.castSucc) P - c₀) -
              (MvPolynomial.eval w' Rb - MvPolynomial.eval (fun i => w' i.castSucc) P - c₀)|
            ≤ |(MvPolynomial.eval m G - MvPolynomial.eval w G) +
              (MvPolynomial.eval w Rb - MvPolynomial.eval (fun i => w i.castSucc) P - c₀)| +
              |MvPolynomial.eval w' Rb - MvPolynomial.eval (fun i => w' i.castSucc) P - c₀| :=
              abs_sub _ _
          _ ≤ (|MvPolynomial.eval m G - MvPolynomial.eval w G| +
              |MvPolynomial.eval w Rb - MvPolynomial.eval (fun i => w i.castSucc) P - c₀|) +
              |MvPolynomial.eval w' Rb - MvPolynomial.eval (fun i => w' i.castSucc) P - c₀| := by
              gcongr; exact abs_add_le _ _
          _ ≤ (lipBox G Bx * ϱ + V) + V := by
              gcongr
              rw [abs_sub_comm]; exact h1
    _ = 2 * (2 * V + lipBox (Rb - liftBase P) Bx * ϱ) := by rw [hG]; ring

/-- **Hidden derivatives across an observation cell.**  Two points of a chart's trajectories in
one observation cell have hidden derivatives within `Lip(∂₃R_b)·3p + κ B a / δ`. -/
lemma abs_pderiv_sub_le_of_cell {Nk : ℝ} {Mp Dp : ℕ} {κ : ℝ} {T : ℕ} {jj rr Bv : ℝ}
    {Evs : Set Ev} {c u : P2} {Qm : Matrix (Fin 2) (Fin 2) ℝ} {Rb : Po} {A : Set Ln}
    {F : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ T jj rr Bv Evs c u Qm Rb A F ex) (hjj : jj + 1 ≤ (2:ℝ) ^ T)
    (hjj0 : 0 ≤ jj) (hN : 1 ≤ Nk) (hBv : 0 < Bv) {p a : ℝ} (hp : 0 < p) (ha : 0 < a)
    {q q' : Ev} (hq : q.1 ∈ A) (hq' : q'.1 ∈ A)
    (hqt : q.2 ∈ Icc (jj / (2:ℝ) ^ T) ((jj + 1) / (2:ℝ) ^ T))
    (hqt' : q'.2 ∈ Icc (jj / (2:ℝ) ^ T) ((jj + 1) / (2:ℝ) ^ T))
    (hcell : cellIdx p Bv a q = cellIdx p Bv a q') :
    |MvPolynomial.eval (xp q.1 q.2) (pderiv 3 Rb) - MvPolynomial.eval (xp q'.1 q'.2) (pderiv 3 Rb)|
      ≤ lipBox (pderiv 3 Rb) (2 * Nk ^ Mp) * (3 * p) + κ * Bv * a / δ Nk rr := by
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hA, _, _⟩ := hch
  have hNM : 1 ≤ Nk ^ Mp := one_le_pow₀ hN
  have hBx1 : (1:ℝ) ≤ 2 * Nk ^ Mp := by linarith
  have h2T : (0:ℝ) < (2:ℝ) ^ T := by positivity
  have hunit : ∀ t ∈ Icc (jj / (2:ℝ) ^ T) ((jj + 1) / (2:ℝ) ^ T), t ∈ Icc (0:ℝ) 1 := by
    intro t ht
    refine ⟨le_trans (by positivity) ht.1, ht.2.trans ?_⟩
    rw [div_le_one h2T]; exact hjj
  have hbox : ∀ i, |xp q.1 q.2 i| ≤ 2 * Nk ^ Mp := fun i => by
    rw [xp_eq_x]; exact abs_x_le hNM (hA q.1 hq).2.1 (hunit q.2 hqt) i
  have hbox' : ∀ i, |xp q'.1 q'.2 i| ≤ 2 * Nk ^ Mp := fun i => by
    rw [xp_eq_x]; exact abs_x_le hNM (hA q'.1 hq').2.1 (hunit q'.2 hqt') i
  set w := xp q.1 q.2 with hw
  set w' := xp q'.1 q'.2 with hw'
  set m := mixPoint w w' with hm
  have hboxm : ∀ i, |m i| ≤ 2 * Nk ^ Mp := by
    intro i
    by_cases hi : i = 3
    · subst hi; rw [hm, mixPoint_hidden]; exact hbox 3
    · rw [hm, mixPoint_base w w' i hi]; exact hbox' i
  -- base distance within the cube
  have hcube : cubeIdx p q = cubeIdx p q' := congrArg Prod.fst hcell
  have hbase : |w 0 - w' 0| + |w 1 - w' 1| + |w 2 - w' 2| ≤ 3 * p := by
    have h0 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 0
    have h1 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 1
    have h2 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 2
    rw [basePoint_apply_zero, basePoint_apply_zero] at h0
    rw [basePoint_apply_one, basePoint_apply_one] at h1
    rw [basePoint_apply_two, basePoint_apply_two] at h2
    have hx0 : ∀ q : Ev, xp q.1 q.2 0 = q.2 := fun q => by simp [xp]
    rw [hw, hw', hx0, hx0]
    linarith
  -- hidden distance within the bin
  have hbin : binIdx Bv a q = binIdx Bv a q' := congrArg Prod.snd hcell
  have hhid : |w 3 - w' 3| ≤ a / Bv := by
    have hk : ⌊Bv * xp q.1 q.2 3 / a⌋ = ⌊Bv * xp q'.1 q'.2 3 / a⌋ := hbin
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hk
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hBv,
      div_lt_one ha] at h1
    rw [le_div_iff₀ hBv, hw, hw']
    linarith
  -- base move: crude Lipschitz
  have hb1 : |MvPolynomial.eval w (pderiv 3 Rb) - MvPolynomial.eval m (pderiv 3 Rb)| ≤
      lipBox (pderiv 3 Rb) (2 * Nk ^ Mp) * (3 * p) := by
    have := abs_eval_sub_eval_le_box (pderiv 3 Rb) hBx1 w m hbox hboxm
    rw [sum_abs_sub_mixPoint] at this
    exact this.trans (mul_le_mul_of_nonneg_left hbase (lipBox_nonneg _ (by linarith)))
  -- hidden move: constant hidden curvature, bounded by the chart
  have hdeg1 : (pderiv 3 Rb).totalDegree ≤ 2 := by
    have := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred Rb 3
    omega
  have hdeg0 : (pderiv 3 (pderiv 3 Rb)).totalDegree = 0 := by
    have h1 := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred (pderiv 3 Rb) 3
    have h2 := Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred Rb 3
    omega
  have hcurv : ∀ x : Fin 4 → ℝ, |MvPolynomial.eval x (pderiv 3 (pderiv 3 Rb))| ≤
      κ * Bv ^ 2 / δ Nk rr := by
    intro x
    rw [eval_eq_of_totalDegree_eq_zero hdeg0 x w', hw', xp_eq_x]
    exact ((hA q'.1 hq').2.2 q'.2 hqt').2.2.2
  have hmw' : ∀ i : Fin 4, i ≠ 3 → m i = w' i := fun i hi => mixPoint_base w w' i hi
  have hb2 := Submission.Obl.k4_physical_parent_potential_candidates.Broad.abs_eval_sub_le_of_hidden
    hdeg1 m w' hmw' (hcurv m) (hcurv w')
  rw [show m 3 = w 3 from mixPoint_hidden w w'] at hb2
  have hδ := δ_pos Nk rr
  have hb2' : |MvPolynomial.eval m (pderiv 3 Rb) - MvPolynomial.eval w' (pderiv 3 Rb)| ≤
      κ * Bv * a / δ Nk rr := by
    refine hb2.trans ?_
    have hκ0 : 0 ≤ κ * Bv ^ 2 / δ Nk rr := le_trans (abs_nonneg _) (hcurv w')
    calc κ * Bv ^ 2 / δ Nk rr * |w 3 - w' 3| ≤ κ * Bv ^ 2 / δ Nk rr * (a / Bv) := by
          gcongr
      _ = κ * Bv * a / δ Nk rr := by field_simp
  calc |MvPolynomial.eval w (pderiv 3 Rb) - MvPolynomial.eval w' (pderiv 3 Rb)|
      ≤ |MvPolynomial.eval w (pderiv 3 Rb) - MvPolynomial.eval m (pderiv 3 Rb)| +
        |MvPolynomial.eval m (pderiv 3 Rb) - MvPolynomial.eval w' (pderiv 3 Rb)| :=
        abs_sub_le _ _ _
    _ ≤ _ := add_le_add hb1 hb2'

/-- Two incidences of one observation cell: base points within `3p` in `ℓ¹`, hidden coordinates
within `a / Bv`. -/
lemma cell_close {p Bv a : ℝ} (hp : 0 < p) (hBv : 0 < Bv) (ha : 0 < a) {q q' : Ev}
    (hcell : cellIdx p Bv a q = cellIdx p Bv a q') :
    |xp q.1 q.2 0 - xp q'.1 q'.2 0| + |xp q.1 q.2 1 - xp q'.1 q'.2 1| +
        |xp q.1 q.2 2 - xp q'.1 q'.2 2| ≤ 3 * p ∧
      |xp q.1 q.2 3 - xp q'.1 q'.2 3| ≤ a / Bv := by
  have hcube : cubeIdx p q = cubeIdx p q' := congrArg Prod.fst hcell
  constructor
  · have h0 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 0
    have h1 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 1
    have h2 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 2
    rw [basePoint_apply_zero, basePoint_apply_zero] at h0
    rw [basePoint_apply_one, basePoint_apply_one] at h1
    rw [basePoint_apply_two, basePoint_apply_two] at h2
    have hx0 : ∀ q : Ev, xp q.1 q.2 0 = q.2 := fun q => by simp [xp]
    rw [hx0, hx0]
    linarith
  · have hbin : binIdx Bv a q = binIdx Bv a q' := congrArg Prod.snd hcell
    have hk : ⌊Bv * xp q.1 q.2 3 / a⌋ = ⌊Bv * xp q'.1 q'.2 3 / a⌋ := hbin
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hk
    rw [← sub_div, ← mul_sub, abs_div, abs_mul, abs_of_pos ha, abs_of_pos hBv,
      div_lt_one ha] at h1
    rw [le_div_iff₀ hBv]
    linarith

/-- **Events of a group cell.**  A counted incidence of a retained line in a group cell of sign
`σ` has its own intercept within `ω` of `c₀` and `σ ∂₃R_b ≥ B/κ`. -/
theorem groupCell_event {Nk : ℝ} {Mp Dp : ℕ} {κ : ℝ} {T : ℕ} {jj : ℕ} {rr Bv : ℝ}
    {Evs : Set Ev} {c u : P2} {Qm : Matrix (Fin 2) (Fin 2) ℝ} {Rb : Po} {A : Set Ln}
    {F : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ T (jj : ℝ) rr Bv Evs c u Qm Rb A F ex) (hjj : jj < 2 ^ T)
    (hN : 1 ≤ Nk) (hκ1 : 1 ≤ κ) (hBv : 0 < Bv)
    (P : MvPolynomial (Fin 3) ℝ) (cpt : Ln → ℝ) (εfit c₀ ω₀ ω : ℝ)
    (Aret : Set Ln) (hAret : Aret ⊆ A)
    (hfit : ∀ l ∈ Aret, ∀ t ∈ Icc ((jj : ℝ) / (2:ℝ) ^ T) (((jj : ℝ) + 1) / (2:ℝ) ^ T),
      |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P -
        cpt l| ≤ εfit)
    (Λ : Set Ln) (hΛ : ∀ l ∈ Λ, |cpt l - c₀| ≤ ω₀)
    {p a σ : ℝ} (hp : 0 < p) (ha : 0 < a) (hσ : σ ^ 2 = 1)
    (hω : ω₀ + 2 * εfit + lipBox (Rb - liftBase P) (2 * Nk ^ Mp) * (3 * p) +
      (κ * Bv + lipBox (pderiv 3 Rb) (2 * Nk ^ Mp) * (3 * p)) * (a / Bv) ≤ ω)
    (hsignC : lipBox (pderiv 3 Rb) (2 * Nk ^ Mp) * (3 * p) + κ * Bv * a / δ Nk rr ≤ Bv / κ)
    {q : Ev} (hqcell : cellIdx p Bv a q ∈ signCells p Bv a Λ Aret
      (Icc ((jj : ℝ) / (2:ℝ) ^ T) (((jj : ℝ) + 1) / (2:ℝ) ^ T)) F Rb σ)
    (hqA : q.1 ∈ Aret) (hqt : q.2 ∈ Icc ((jj : ℝ) / (2:ℝ) ^ T) (((jj : ℝ) + 1) / (2:ℝ) ^ T))
    (hqF : q ∈ F) :
    |cpt q.1 - c₀| ≤ ω ∧ Bv / κ ≤ σ * MvPolynomial.eval (xp q.1 q.2) (pderiv 3 Rb) := by
  obtain ⟨q', hq'cell, hq'Λ, hq'A, hq't, hq'F, hq'sign⟩ := hqcell
  have hch' := hch
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hAch, hFch, _⟩ := hch'
  have hNM : 1 ≤ Nk ^ Mp := one_le_pow₀ hN
  have hBx1 : (1:ℝ) ≤ 2 * Nk ^ Mp := by linarith
  have h2T : (0:ℝ) < (2:ℝ) ^ T := by positivity
  have hj1 : ((jj : ℝ) + 1) ≤ (2:ℝ) ^ T := by exact_mod_cast hjj
  have hunit : ∀ t ∈ Icc ((jj : ℝ) / (2:ℝ) ^ T) (((jj : ℝ) + 1) / (2:ℝ) ^ T),
      t ∈ Icc (0:ℝ) 1 := by
    intro t ht
    refine ⟨le_trans (by positivity) ht.1, ht.2.trans ?_⟩
    rw [div_le_one h2T]; exact hj1
  have hbox : ∀ q : Ev, q.1 ∈ Aret → q.2 ∈ Icc ((jj : ℝ) / (2:ℝ) ^ T)
      (((jj : ℝ) + 1) / (2:ℝ) ^ T) → ∀ i, |xp q.1 q.2 i| ≤ 2 * Nk ^ Mp := by
    intro q hq hqt i
    rw [xp_eq_x]; exact abs_x_le hNM (hAch q.1 (hAret hq)).2.1 (hunit q.2 hqt) i
  have hderub : ∀ q : Ev, q.1 ∈ Aret → q.2 ∈ Icc ((jj : ℝ) / (2:ℝ) ^ T)
      (((jj : ℝ) + 1) / (2:ℝ) ^ T) →
      |MvPolynomial.eval (xp q.1 q.2) (pderiv 3 Rb)| ≤ κ * Bv := by
    intro q hq hqt
    rw [xp_eq_x]; exact ((hAch q.1 (hAret hq)).2.2 q.2 hqt).2.2.1
  have hcell : cellIdx p Bv a q = cellIdx p Bv a q' := hq'cell.symm
  obtain ⟨hbase, hhid⟩ := cell_close hp hBv ha hcell
  constructor
  · have hclose := intercept_close_of_cell hdeg P cpt hBx1 (hfit q.1 hqA q.2 hqt)
      (hfit q'.1 hq'A q'.2 hq't) (hbox q hqA hqt) (hbox q' hq'A hq't) hbase hhid
      (hderub q hqA hqt) (hderub q' hq'A hq't)
    have hq'c := hΛ q'.1 hq'Λ
    have hL1 : lipBox (Rb - liftBase P) (2 * Nk ^ Mp) =
        (Rb - liftBase P).totalDegree * coeffL1 (Rb - liftBase P) *
          (2 * Nk ^ Mp) ^ (Rb - liftBase P).totalDegree := rfl
    have hL2 : lipBox (pderiv 3 Rb) (2 * Nk ^ Mp) =
        (pderiv 3 Rb).totalDegree * coeffL1 (pderiv 3 Rb) *
          (2 * Nk ^ Mp) ^ (pderiv 3 Rb).totalDegree := rfl
    rw [← hL1, ← hL2] at hclose
    calc |cpt q.1 - c₀| ≤ |cpt q.1 - cpt q'.1| + |cpt q'.1 - c₀| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hclose hq'c
      _ ≤ ω := by linarith
  · have hdiff := abs_pderiv_sub_le_of_cell hch (by exact_mod_cast hj1) (by positivity) hN hBv
      hp ha (hAret hqA) (hAret hq'A) hqt hq't hcell
    have hdq := (hFch q hqF).2.2.2
    have hdq' := (hFch q' hq'F).2.2.2
    rw [← xp_eq_x] at hdq hdq'
    have hσabs : |σ| = 1 := by
      have : |σ| ^ 2 = 1 := by rw [sq_abs]; exact hσ
      nlinarith [abs_nonneg σ, sq_nonneg (|σ| - 1), sq_nonneg (|σ| + 1)]
    set d := MvPolynomial.eval (xp q.1 q.2) (pderiv 3 Rb) with hd
    set d' := MvPolynomial.eval (xp q'.1 q'.2) (pderiv 3 Rb) with hd'
    have hσd' : Bv / κ ≤ σ * d' := by
      have : |σ * d'| = |d'| := by rw [abs_mul, hσabs, one_mul]
      have hpos : 0 < σ * d' := hq'sign
      rw [abs_of_pos hpos] at this
      linarith
    have hσd : |σ * d| = |d| := by rw [abs_mul, hσabs, one_mul]
    have hsd : |σ * d - σ * d'| ≤ Bv / κ := by
      rw [← mul_sub, abs_mul, hσabs, one_mul]; exact hdiff.trans hsignC
    by_contra hcon
    push Not at hcon
    -- `σ d` is below `B/κ` but has modulus at least `B/κ`, so it is at most `-B/κ`
    have hneg : σ * d ≤ -(Bv / κ) := by
      rcases le_or_gt 0 (σ * d) with h | h
      · rw [← hσd, abs_of_nonneg h] at hdq; linarith
      · rw [← hσd, abs_of_neg h] at hdq; linarith
    have hκpos : 0 < Bv / κ := by positivity
    have := (abs_le.mp hsd).1
    linarith

/-- **Few hidden bins per cube.**  Above one base cube, the group cells of one sign use at most
`4κ(2(εfit + ω₀) + Lip·3p)/a + 2` hidden bins: their witnesses are fitted points of one sign in
one thin base cell (`hidden_close_of_fit`). -/
theorem signCells_bins {Nk : ℝ} {Mp Dp : ℕ} {κ : ℝ} {T : ℕ} {jj : ℕ} {rr Bv : ℝ}
    {Evs : Set Ev} {c u : P2} {Qm : Matrix (Fin 2) (Fin 2) ℝ} {Rb : Po} {A : Set Ln}
    {F : Set Ev} {ex : Prop}
    (hch : ch Nk Mp Dp κ T (jj : ℝ) rr Bv Evs c u Qm Rb A F ex) (hjj : jj < 2 ^ T)
    (hN : 1 ≤ Nk) (hκ1 : 1 ≤ κ) (hBv : 0 < Bv)
    (P : MvPolynomial (Fin 3) ℝ) (cpt : Ln → ℝ) (εfit c₀ ω₀ : ℝ) (hε : 0 ≤ εfit)
    (hω₀ : 0 ≤ ω₀) (Aret : Set Ln) (hAret : Aret ⊆ A)
    (hfit : ∀ l ∈ Aret, ∀ t ∈ Icc ((jj : ℝ) / (2:ℝ) ^ T) (((jj : ℝ) + 1) / (2:ℝ) ^ T),
      |MvPolynomial.eval (xp l t) Rb - MvPolynomial.eval (fun i => xp l t i.castSucc) P -
        cpt l| ≤ εfit)
    (Λ : Set Ln) (hΛ : ∀ l ∈ Λ, |cpt l - c₀| ≤ ω₀)
    {p a σ : ℝ} (hp : 0 < p) (ha : 0 < a)
    (hsmall : lipBox (pderiv 3 Rb) (2 * Nk ^ Mp) * (3 * p) ≤ Bv / κ)
    (cube : Fin 3 → ℤ) :
    ∃ Fc : Finset ℤ, (Fc.card : ℝ) ≤
        4 * κ * (2 * (εfit + ω₀) + lipBox (Rb - liftBase P) (2 * Nk ^ Mp) * (3 * p)) / a + 2 ∧
      ∀ k, (cube, k) ∈ signCells p Bv a Λ Aret
        (Icc ((jj : ℝ) / (2:ℝ) ^ T) (((jj : ℝ) + 1) / (2:ℝ) ^ T)) F Rb σ → k ∈ Fc := by
  classical
  have hch' := hch
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hAch, hFch, _⟩ := hch'
  have hNM : 1 ≤ Nk ^ Mp := one_le_pow₀ hN
  have hBx1 : (1:ℝ) ≤ 2 * Nk ^ Mp := by linarith
  have h2T : (0:ℝ) < (2:ℝ) ^ T := by positivity
  have hj1 : ((jj : ℝ) + 1) ≤ (2:ℝ) ^ T := by exact_mod_cast hjj
  set blk := Icc ((jj : ℝ) / (2:ℝ) ^ T) (((jj : ℝ) + 1) / (2:ℝ) ^ T) with hblk
  have hunit : ∀ t ∈ blk, t ∈ Icc (0:ℝ) 1 := by
    intro t ht
    refine ⟨le_trans (by positivity) ht.1, ht.2.trans ?_⟩
    rw [div_le_one h2T]; exact hj1
  -- the witnesses above the cube
  set X : Set Ev := {q | cubeIdx p q = cube ∧ q.1 ∈ Λ ∧ q.1 ∈ Aret ∧ q.2 ∈ blk ∧ q ∈ F ∧
    0 < σ * MvPolynomial.eval (xp q.1 q.2) (pderiv 3 Rb)} with hX
  set V := εfit + ω₀ with hV
  set Lp := lipBox (Rb - liftBase P) (2 * Nk ^ Mp) with hLp
  have hL0 : 0 ≤ Lp := lipBox_nonneg _ (by linarith)
  set ℓh : ℝ := 2 * (2 * V + Lp * (3 * p)) / (Bv / κ) with hℓh
  have hκB : 0 < Bv / κ := by positivity
  have hℓh0 : 0 ≤ ℓh := by positivity
  have hclose : ∀ y ∈ X, ∀ y' ∈ X, |xp y.1 y.2 3 - xp y'.1 y'.2 3| ≤ ℓh := by
    intro y hy y' hy'
    obtain ⟨hyc, hyΛ, hyA, hyt, hyF, hys⟩ := hy
    obtain ⟨hyc', hyΛ', hyA', hyt', hyF', hys'⟩ := hy'
    have hcube : cubeIdx p y = cubeIdx p y' := hyc.trans hyc'.symm
    have hbase : |xp y.1 y.2 0 - xp y'.1 y'.2 0| + |xp y.1 y.2 1 - xp y'.1 y'.2 1| +
        |xp y.1 y.2 2 - xp y'.1 y'.2 2| ≤ 3 * p := by
      have h0 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 0
      have h1 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 1
      have h2 := abs_basePoint_sub_lt_of_cubeIdx_eq hp hcube 2
      rw [basePoint_apply_zero, basePoint_apply_zero] at h0
      rw [basePoint_apply_one, basePoint_apply_one] at h1
      rw [basePoint_apply_two, basePoint_apply_two] at h2
      have hx0 : ∀ q : Ev, xp q.1 q.2 0 = q.2 := fun q => by simp [xp]
      rw [hx0, hx0]
      linarith
    have hbox : ∀ q : Ev, q.1 ∈ Aret → q.2 ∈ blk → ∀ i, |xp q.1 q.2 i| ≤ 2 * Nk ^ Mp := by
      intro q hq hqt i
      rw [xp_eq_x]; exact abs_x_le hNM (hAch q.1 (hAret hq)).2.1 (hunit q.2 hqt) i
    have hval : ∀ q : Ev, q.1 ∈ Λ → q.1 ∈ Aret → q.2 ∈ blk →
        |MvPolynomial.eval (xp q.1 q.2) Rb -
          MvPolynomial.eval (fun i => xp q.1 q.2 i.castSucc) P - c₀| ≤ V := by
      intro q hqΛ hqA hqt
      have h1 := hfit q.1 hqA q.2 hqt
      have h2 := hΛ q.1 hqΛ
      calc |MvPolynomial.eval (xp q.1 q.2) Rb -
            MvPolynomial.eval (fun i => xp q.1 q.2 i.castSucc) P - c₀|
          = |(MvPolynomial.eval (xp q.1 q.2) Rb -
              MvPolynomial.eval (fun i => xp q.1 q.2 i.castSucc) P - cpt q.1) +
            (cpt q.1 - c₀)| := by ring_nf
        _ ≤ εfit + ω₀ := (abs_add_le _ _).trans (add_le_add h1 h2)
    have hder : ∀ q : Ev, q ∈ F → Bv / κ ≤ |MvPolynomial.eval (xp q.1 q.2) (pderiv 3 Rb)| := by
      intro q hqF
      rw [xp_eq_x]; exact (hFch q hqF).2.2.2
    have hsign : 0 ≤ MvPolynomial.eval (xp y.1 y.2) (pderiv 3 Rb) *
        MvPolynomial.eval (xp y'.1 y'.2) (pderiv 3 Rb) := by
      have : 0 < (σ * MvPolynomial.eval (xp y.1 y.2) (pderiv 3 Rb)) *
          (σ * MvPolynomial.eval (xp y'.1 y'.2) (pderiv 3 Rb)) := mul_pos hys hys'
      have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
      by_contra hneg
      push Not at hneg
      have : (σ * MvPolynomial.eval (xp y.1 y.2) (pderiv 3 Rb)) *
          (σ * MvPolynomial.eval (xp y'.1 y'.2) (pderiv 3 Rb)) =
          σ ^ 2 * (MvPolynomial.eval (xp y.1 y.2) (pderiv 3 Rb) *
            MvPolynomial.eval (xp y'.1 y'.2) (pderiv 3 Rb)) := by ring
      nlinarith
    have hc := hidden_close_of_fit hdeg P c₀ hBx1 (xp y.1 y.2) (xp y'.1 y'.2)
      (hbox y hyA hyt) (hbox y' hyA' hyt') hbase (hval y hyΛ hyA hyt) (hval y' hyΛ' hyA' hyt')
      (hder y hyF) (hder y' hyF') hsign hsmall
    rw [hℓh, le_div_iff₀ hκB]
    exact hc
  obtain ⟨Fc, hFc, hFcard⟩ := exists_floor_finset_of_close X (fun q => xp q.1 q.2 3)
    (c := Bv / a) (by positivity) hℓh0 hclose
  refine ⟨Fc, ?_, ?_⟩
  · refine hFcard.trans (le_of_eq ?_)
    rw [hℓh]
    field_simp
    ring
  · intro k hk
    obtain ⟨q, hqk, hqΛ, hqA, hqt, hqF, hqs⟩ := hk
    have hq : q ∈ X := ⟨congrArg Prod.fst hqk, hqΛ, hqA, hqt, hqF, hqs⟩
    have := hFc q hq
    have hbin : binIdx Bv a q = k := congrArg Prod.snd hqk
    rw [← hbin]
    have : binIdx Bv a q = ⌊Bv / a * xp q.1 q.2 3⌋ := by
      simp only [binIdx]; congr 1; ring
    rw [this]
    exact hFc q hq

end

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
