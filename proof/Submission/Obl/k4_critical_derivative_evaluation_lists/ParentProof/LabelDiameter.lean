/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, LabelDiameter.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupBudget

/-! Inside one true label, a sufficiently fine normalized base cell and velocity
bin determine the initial-position group, the time subbin and the hidden bin up
to a subpower number of neighbors (paper: "p is recovered using Z = p + t v; Y is
bounded to K H² accuracy using Q_s, z; ... the L_s-lists restrict x_a"). -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

theorem abs_floor_sub_floor_le (x y : ℝ) : |((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ)| ≤ |x - y| + 1 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  push_cast
  rw [abs_le]
  constructor <;> cases abs_cases (x - y) <;> linarith

theorem abs_floor_div_sub_le {x y a : ℝ} (ha : 0 < a) :
    |((⌊x / a⌋ - ⌊y / a⌋ : ℤ) : ℝ)| ≤ |x - y| / a + 1 := by
  refine (abs_floor_sub_floor_le _ _).trans (le_of_eq ?_)
  rw [← sub_div, abs_div, abs_of_pos ha]

theorem abs_sub_lt_mul_of_floor_eq {x y ξ : ℝ} (hξ : 0 < ξ) (h : ⌊x / ξ⌋ = ⌊y / ξ⌋) :
    |x - y| < ξ := by
  have hh := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hξ, div_lt_one hξ] at hh
  exact hh

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- The normalized base cell of `p` in true label `i`, at mesh `ξ`: time from
the left block endpoint and horizontal position from the label center, both
divided by the true block length. -/
def labelCell (k : ℕ) (s ξ : ℝ) (i : Fin (cfg.n k s)) (p : α × ℝ) : Fin 2 → ℤ :=
  (fun (H t₀ Z₀ : ℝ) => fun e : Fin 2 =>
    ⌊(![(p.2 - t₀) / H, (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - Z₀) / H] : Fin 2 → ℝ) e / ξ⌋)
    (((2 : ℝ) ^ cfg.T k s)⁻¹)
    (((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s)
    (cfg.c k s i 0 + (((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s) * cfg.c k s i 1)

/-- The label-i data used by the diameter argument, at one sample. -/
structure LabelDiameterInputs (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ) : Prop where
  c_bound : ∀ e, |cfg.c k s i e| ≤ cfg.K k
  plane : ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
    |cfg.b k l 1 + t * cfg.b k l 4 - cfg.c k s i 2 - t * cfg.c k s i 3 -
      cfg.c k s i 4 * (cfg.b k l 0 + t * cfg.b k l 3)| ≤ cfg.K k ^ 2 * cfg.N k ^ (-s)
  slopes : ∀ e : Fin 3, |L e.succ| ≤ 8 * cfg.K k ^ 4
  fit : ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
    |(cfg.b k l 2 + t * cfg.b k l 5) - (L 0 + L 1 * t + L 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
      L 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * cfg.N k ^ (-s)

set_option maxHeartbeats 1000000 in
/-- Two good incidences of one true label in the same normalized base cell and
velocity bin have all five group/subbin/hidden coordinates within `M`. -/
theorem label_tuple_close (k : ℕ) {s ξ : ℝ} (i : Fin (cfg.n k s)) (L : Fin 4 → ℝ)
    (hin : cfg.LabelDiameterInputs k s i L)
    (hK : 1 ≤ cfg.K k) (hN : 1 < cfg.N k) (hs : 0 < s) (hξ : 0 < ξ)
    (hξδ : ξ ≤ cfg.N k ^ (-(2 * s))) (hξa : 3 * cfg.K k * ξ ≤ cfg.N k ^ (-s))
    (he₀ : cfg.N k ^ (-cfg.e₀) ≤ cfg.N k ^ (-s))
    {p p' : α × ℝ} (hp : p ∈ cfg.goodSet k s) (hp' : p' ∈ cfg.goodSet k s)
    (hpi : p.1 ∈ cfg.B k s i ∧ p.2 ∈ I (cfg.T k s) (cfg.j k s i))
    (hp'i : p'.1 ∈ cfg.B k s i ∧ p'.2 ∈ I (cfg.T k s) (cfg.j k s i))
    (hcell : cfg.labelCell k s ξ i p = cfg.labelCell k s ξ i p')
    (hv : ⌊cfg.b k p.1 3 / ξ⌋ = ⌊cfg.b k p'.1 3 / ξ⌋) :
    let a := cfg.N k ^ (-s)
    let δ := cfg.N k ^ (-(2 * s))
    let M := 60 * cfg.K k ^ 6 + 4
    |((⌊cfg.b k p.1 0 / a⌋ - ⌊cfg.b k p'.1 0 / a⌋ : ℤ) : ℝ)| ≤ M ∧
    |((⌊cfg.b k p.1 1 / a⌋ - ⌊cfg.b k p'.1 1 / a⌋ : ℤ) : ℝ)| ≤ M ∧
    |((⌊cfg.b k p.1 3 / δ⌋ - ⌊cfg.b k p'.1 3 / δ⌋ : ℤ) : ℝ)| ≤ M ∧
    |((⌊p.2 / δ⌋ - ⌊p'.2 / δ⌋ : ℤ) : ℝ)| ≤ M ∧
    |((⌊cfg.hidden k p / a⌋ - ⌊cfg.hidden k p' / a⌋ : ℤ) : ℝ)| ≤ M := by
  intro a δ M
  have hNpos : 0 < cfg.N k := by linarith
  have ha : 0 < a := Real.rpow_pos_of_pos hNpos _
  have hδ : 0 < δ := Real.rpow_pos_of_pos hNpos _
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hK6 : 1 ≤ cfg.K k ^ 6 := one_le_pow₀ hK
  have hMge : 4 ≤ M := by have := pow_nonneg hK0 6; show (4 : ℝ) ≤ 60 * cfg.K k ^ 6 + 4; linarith
  have hH : 0 < (2 : ℝ) ^ cfg.T k s := by positivity
  set H := ((2 : ℝ) ^ cfg.T k s)⁻¹ with hHdef
  have hHpos : 0 < H := inv_pos.mpr hH
  have hH1 : H ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨ht, hb0, hb1, hb3, hb4, hb2, hb5, hdef, -⟩ := hp
  obtain ⟨ht', hb0', hb1', hb3', hb4', hb2', hb5', hdef', -⟩ := hp'
  -- the cell gives time and horizontal closeness
  have hcell0 := congrFun hcell 0
  have hcell1 := congrFun hcell 1
  simp only [labelCell, Matrix.cons_val_zero, Matrix.cons_val_one] at hcell0 hcell1
  have hξH : 0 < ξ * H := mul_pos hξ hHpos
  have htt : |p.2 - p'.2| ≤ ξ := by
    have hh := abs_sub_lt_mul_of_floor_eq hξ hcell0
    rw [show (p.2 - _) / H - (p'.2 - _) / H = (p.2 - p'.2) / H by ring, abs_div,
      abs_of_pos hHpos, div_lt_iff₀ hHpos] at hh
    have := mul_le_of_le_one_right hξ.le hH1
    linarith
  have hZZ : |(cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) - (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3)| ≤ ξ := by
    have hh := abs_sub_lt_mul_of_floor_eq hξ hcell1
    rw [show (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3 - _) / H -
        (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3 - _) / H =
        ((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) - (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3)) / H by ring,
      abs_div, abs_of_pos hHpos, div_lt_iff₀ hHpos] at hh
    have := mul_le_of_le_one_right hξ.le hH1
    linarith
  have hvv : |cfg.b k p.1 3 - cfg.b k p'.1 3| ≤ ξ := (abs_sub_lt_mul_of_floor_eq hξ hv).le
  have ht1 : |p.2| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have ht1' : |p'.2| ≤ 1 := by rw [abs_of_nonneg ht'.1]; exact ht'.2
  -- initial horizontal position
  have hb00 : |cfg.b k p.1 0 - cfg.b k p'.1 0| ≤ 3 * cfg.K k * ξ := by
    have heq : cfg.b k p.1 0 - cfg.b k p'.1 0 =
        ((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) - (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3)) -
          p.2 * (cfg.b k p.1 3 - cfg.b k p'.1 3) - (p.2 - p'.2) * cfg.b k p'.1 3 := by ring
    rw [heq]
    have e1 : |p.2 * (cfg.b k p.1 3 - cfg.b k p'.1 3)| ≤ ξ := by
      rw [abs_mul]
      calc |p.2| * |cfg.b k p.1 3 - cfg.b k p'.1 3| ≤ 1 * ξ :=
            mul_le_mul ht1 hvv (abs_nonneg _) zero_le_one
        _ = ξ := one_mul _
    have e2 : |(p.2 - p'.2) * cfg.b k p'.1 3| ≤ ξ * cfg.K k := by
      rw [abs_mul]; exact mul_le_mul htt hb3' (abs_nonneg _) hξ.le
    calc
      _ ≤ |((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) - (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3)) -
            p.2 * (cfg.b k p.1 3 - cfg.b k p'.1 3)| + |(p.2 - p'.2) * cfg.b k p'.1 3| := abs_sub _ _
      _ ≤ (ξ + ξ) + ξ * cfg.K k := add_le_add ((abs_sub _ _).trans (add_le_add hZZ e1)) e2
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right hK hξ.le
        linarith
  -- transverse position Y = b1 + t b4 from the label plane
  have hplane := hin.plane p.1 hpi.1 p.2 hpi.2
  have hplane' := hin.plane p'.1 hp'i.1 p'.2 hp'i.2
  have hc3 := hin.c_bound 3
  have hc4 := hin.c_bound 4
  have hYY : |(cfg.b k p.1 1 + p.2 * cfg.b k p.1 4) - (cfg.b k p'.1 1 + p'.2 * cfg.b k p'.1 4)| ≤
      2 * cfg.K k ^ 2 * a + 2 * cfg.K k * ξ := by
    have heq : (cfg.b k p.1 1 + p.2 * cfg.b k p.1 4) - (cfg.b k p'.1 1 + p'.2 * cfg.b k p'.1 4) =
        (cfg.b k p.1 1 + p.2 * cfg.b k p.1 4 - cfg.c k s i 2 - p.2 * cfg.c k s i 3 -
          cfg.c k s i 4 * (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3)) -
        (cfg.b k p'.1 1 + p'.2 * cfg.b k p'.1 4 - cfg.c k s i 2 - p'.2 * cfg.c k s i 3 -
          cfg.c k s i 4 * (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3)) +
        cfg.c k s i 3 * (p.2 - p'.2) +
        cfg.c k s i 4 * ((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) -
          (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3)) := by ring
    rw [heq]
    have e3 : |cfg.c k s i 3 * (p.2 - p'.2)| ≤ cfg.K k * ξ := by
      rw [abs_mul]; exact mul_le_mul hc3 htt (abs_nonneg _) hK0
    have e4 : |cfg.c k s i 4 * ((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) -
        (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3))| ≤ cfg.K k * ξ := by
      rw [abs_mul]; exact mul_le_mul hc4 hZZ (abs_nonneg _) hK0
    calc
      _ ≤ |(cfg.b k p.1 1 + p.2 * cfg.b k p.1 4 - cfg.c k s i 2 - p.2 * cfg.c k s i 3 -
            cfg.c k s i 4 * (cfg.b k p.1 0 + p.2 * cfg.b k p.1 3)) -
          (cfg.b k p'.1 1 + p'.2 * cfg.b k p'.1 4 - cfg.c k s i 2 - p'.2 * cfg.c k s i 3 -
            cfg.c k s i 4 * (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3))| +
          |cfg.c k s i 3 * (p.2 - p'.2)| +
          |cfg.c k s i 4 * ((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) -
            (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (cfg.K k ^ 2 * a + cfg.K k ^ 2 * a) + cfg.K k * ξ + cfg.K k * ξ :=
        add_le_add (add_le_add ((abs_sub _ _).trans (add_le_add hplane hplane')) e3) e4
      _ = _ := by ring
  -- initial transverse position b1 = Y - t b4, with b4 = -b0 + defect
  have hb11 : |cfg.b k p.1 1 - cfg.b k p'.1 1| ≤ 2 * cfg.K k ^ 2 * a + 8 * cfg.K k * ξ + 2 * a := by
    have hb44 : |cfg.b k p.1 4 - cfg.b k p'.1 4| ≤ 2 * a + 3 * cfg.K k * ξ := by
      have heq : cfg.b k p.1 4 - cfg.b k p'.1 4 =
          (cfg.b k p.1 4 + cfg.b k p.1 0) - (cfg.b k p'.1 4 + cfg.b k p'.1 0) -
            (cfg.b k p.1 0 - cfg.b k p'.1 0) := by ring
      rw [heq]
      calc
        _ ≤ |(cfg.b k p.1 4 + cfg.b k p.1 0) - (cfg.b k p'.1 4 + cfg.b k p'.1 0)| +
            |cfg.b k p.1 0 - cfg.b k p'.1 0| := abs_sub _ _
        _ ≤ (a + a) + 3 * cfg.K k * ξ :=
          add_le_add ((abs_sub _ _).trans (add_le_add (hdef.trans he₀) (hdef'.trans he₀))) hb00
        _ = _ := by ring
    have heq : cfg.b k p.1 1 - cfg.b k p'.1 1 =
        ((cfg.b k p.1 1 + p.2 * cfg.b k p.1 4) - (cfg.b k p'.1 1 + p'.2 * cfg.b k p'.1 4)) -
          p.2 * (cfg.b k p.1 4 - cfg.b k p'.1 4) - (p.2 - p'.2) * cfg.b k p'.1 4 := by ring
    rw [heq]
    have e1 : |p.2 * (cfg.b k p.1 4 - cfg.b k p'.1 4)| ≤ 2 * a + 3 * cfg.K k * ξ := by
      rw [abs_mul]
      calc
        |p.2| * |cfg.b k p.1 4 - cfg.b k p'.1 4| ≤ 1 * (2 * a + 3 * cfg.K k * ξ) :=
          mul_le_mul ht1 hb44 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have e2 : |(p.2 - p'.2) * cfg.b k p'.1 4| ≤ ξ * cfg.K k := by
      rw [abs_mul]; exact mul_le_mul htt hb4' (abs_nonneg _) hξ.le
    calc
      _ ≤ |((cfg.b k p.1 1 + p.2 * cfg.b k p.1 4) - (cfg.b k p'.1 1 + p'.2 * cfg.b k p'.1 4)) -
            p.2 * (cfg.b k p.1 4 - cfg.b k p'.1 4)| + |(p.2 - p'.2) * cfg.b k p'.1 4| := abs_sub _ _
      _ ≤ ((2 * cfg.K k ^ 2 * a + 2 * cfg.K k * ξ) + (2 * a + 3 * cfg.K k * ξ)) + ξ * cfg.K k :=
        add_le_add ((abs_sub _ _).trans (add_le_add hYY e1)) e2
      _ ≤ _ := by
        have := mul_nonneg hK0 hξ.le
        linarith
  -- hidden value from the affine fit
  have hfit := hin.fit p.1 hpi.1 p.2 hpi.2
  have hfit' := hin.fit p'.1 hp'i.1 p'.2 hp'i.2
  have hL1 := hin.slopes 0
  have hL2 := hin.slopes 1
  have hL3 := hin.slopes 2
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hL1 hL2 hL3
  have hL3' : |L 3| ≤ 8 * cfg.K k ^ 4 := hL3
  have hww : |cfg.hidden k p - cfg.hidden k p'| ≤
      2 * cfg.K k * a + 8 * cfg.K k ^ 4 * (ξ + ξ + (2 * cfg.K k ^ 2 * a + 2 * cfg.K k * ξ)) := by
    unfold hidden
    have heq : (cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) - (cfg.b k p'.1 2 + p'.2 * cfg.b k p'.1 5) =
        ((cfg.b k p.1 2 + p.2 * cfg.b k p.1 5) - (L 0 + L 1 * p.2 + L 2 * (cfg.b k p.1 0 +
          p.2 * cfg.b k p.1 3) + L 3 * (cfg.b k p.1 1 + p.2 * cfg.b k p.1 4))) -
        ((cfg.b k p'.1 2 + p'.2 * cfg.b k p'.1 5) - (L 0 + L 1 * p'.2 + L 2 * (cfg.b k p'.1 0 +
          p'.2 * cfg.b k p'.1 3) + L 3 * (cfg.b k p'.1 1 + p'.2 * cfg.b k p'.1 4))) +
        L 1 * (p.2 - p'.2) +
        L 2 * ((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) - (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3)) +
        L 3 * ((cfg.b k p.1 1 + p.2 * cfg.b k p.1 4) - (cfg.b k p'.1 1 + p'.2 * cfg.b k p'.1 4)) := by
      ring
    rw [heq]
    have f1 : |L 1 * (p.2 - p'.2)| ≤ 8 * cfg.K k ^ 4 * ξ := by
      rw [abs_mul]; exact mul_le_mul hL1 htt (abs_nonneg _) (by positivity)
    have f2 : |L 2 * ((cfg.b k p.1 0 + p.2 * cfg.b k p.1 3) -
        (cfg.b k p'.1 0 + p'.2 * cfg.b k p'.1 3))| ≤ 8 * cfg.K k ^ 4 * ξ := by
      rw [abs_mul]; exact mul_le_mul hL2 hZZ (abs_nonneg _) (by positivity)
    have f3 : |L 3 * ((cfg.b k p.1 1 + p.2 * cfg.b k p.1 4) -
        (cfg.b k p'.1 1 + p'.2 * cfg.b k p'.1 4))| ≤
        8 * cfg.K k ^ 4 * (2 * cfg.K k ^ 2 * a + 2 * cfg.K k * ξ) := by
      rw [abs_mul]; exact mul_le_mul hL3' hYY (abs_nonneg _) (by positivity)
    have hsum := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add hfit hfit')) f1)) f2)) f3)
    refine hsum.trans (le_of_eq ?_)
    ring
  -- convert to bins
  have hKξ := mul_le_mul_of_nonneg_right hK hξ.le
  have hKξ0 := mul_nonneg hK0 hξ.le
  have hξa' : ξ ≤ a := by linarith
  have hξK : cfg.K k * ξ ≤ a := by linarith
  have hK2 : cfg.K k ≤ cfg.K k ^ 6 := by
    calc cfg.K k = cfg.K k ^ 1 := (pow_one _).symm
      _ ≤ cfg.K k ^ 6 := pow_le_pow_right₀ hK (by norm_num)
  have hK5 : cfg.K k ^ 5 ≤ cfg.K k ^ 6 := pow_le_pow_right₀ hK (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (abs_floor_div_sub_le ha).trans ?_
    have : |cfg.b k p.1 0 - cfg.b k p'.1 0| / a ≤ 1 := by
      rw [div_le_one ha]; linarith
    linarith
  · refine (abs_floor_div_sub_le ha).trans ?_
    have : |cfg.b k p.1 1 - cfg.b k p'.1 1| / a ≤ 2 * cfg.K k ^ 2 + 8 + 2 := by
      rw [div_le_iff₀ ha]; linarith
    have hK26 : cfg.K k ^ 2 ≤ cfg.K k ^ 6 := pow_le_pow_right₀ hK (by norm_num)
    linarith
  · refine (abs_floor_div_sub_le hδ).trans ?_
    have : |cfg.b k p.1 3 - cfg.b k p'.1 3| / δ ≤ 1 := by
      rw [div_le_one hδ]; linarith
    linarith
  · refine (abs_floor_div_sub_le hδ).trans ?_
    have : |p.2 - p'.2| / δ ≤ 1 := by
      rw [div_le_one hδ]; linarith
    linarith
  · refine (abs_floor_div_sub_le ha).trans ?_
    have hK4 : cfg.K k ^ 4 * (cfg.K k * a) = cfg.K k ^ 5 * a := by ring
    have : |cfg.hidden k p - cfg.hidden k p'| / a ≤ 2 * cfg.K k + 8 * cfg.K k ^ 4 * 2 +
        8 * cfg.K k ^ 4 * (2 * cfg.K k ^ 2 + 2) := by
      rw [div_le_iff₀ ha]
      refine hww.trans ?_
      have hK4p : 0 ≤ cfg.K k ^ 4 := by positivity
      have h1 := mul_le_mul_of_nonneg_left hξa' hK4p
      have h2 := mul_le_mul_of_nonneg_left hξK hK4p
      have h3 : cfg.K k ^ 4 * (cfg.K k * ξ) = cfg.K k ^ 5 * ξ := by ring
      have h4 : cfg.K k ^ 4 * (cfg.K k ^ 2 * a) = cfg.K k ^ 6 * a := by ring
      nlinarith only [h1, h2, h3, h4]
    have hK4 : cfg.K k ^ 4 ≤ cfg.K k ^ 6 := pow_le_pow_right₀ hK (by norm_num)
    linarith

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
