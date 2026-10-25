-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Iteration.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open MeasureTheory

/-- Product-metric balls in the projection plane are squares. -/
theorem planar_ball_volume (p : ℝ × ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball p r) = ENNReal.ofReal (4 * r ^ 2) := by
  rw [← ball_prod_same, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
    Real.volume_ball, Real.volume_ball, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Every nonempty planar thickening contains a square of side `2 * r`. -/
theorem thickening_area_lower {E : Set (ℝ × ℝ)} (hE : E.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (r ^ 2) ≤ volume (Metric.thickening r E) := by
  obtain ⟨p, hp⟩ := hE
  have hball := planar_ball_volume p hr
  calc
    ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (4 * r ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_nonneg r]
    _ = volume (Metric.ball p r) := hball.symm
    _ ≤ volume (Metric.thickening r E) :=
      measure_mono (Metric.ball_subset_thickening hp r)

/-- A geometric improvement reaches any fixed positive exponent in finitely many steps. -/
theorem exists_iteration_depth {q a : ℝ} (hq : q < 1) (ha : 0 < a) :
    ∃ N : ℕ, q ^ N < a :=
  exists_pow_lt_of_lt_one ha hq

/-- Lower bounds for all scales in a chain with a fixed power gain. -/
theorem scale_chain_bound {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ)
    (r : ℕ → ℝ) (hzero : r 0 = δ) {N : ℕ}
    (hstep : ∀ j < N, (r j) ^ q ≤ r (j + 1)) :
    ∀ j ≤ N, δ ^ (q ^ j) ≤ r j := by
  intro j hj
  induction j with
  | zero => simp [hzero]
  | succ j ih =>
    have hle := ih (Nat.le_of_succ_le hj)
    have hpos : 0 < r j := (Real.rpow_pos_of_pos hδ _).trans_le hle
    calc
      δ ^ (q ^ (j + 1)) = (δ ^ (q ^ j)) ^ q := by
        rw [pow_succ, Real.rpow_mul hδ.le]
      _ ≤ (r j) ^ q := Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hle hq
      _ ≤ r (j + 1) := hstep j (Nat.lt_of_succ_le hj)

/-- The number of coarse-scale steps depends only on the two exponents. -/
theorem scale_chain_stops {q a : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (ha : 0 < a) :
    ∃ N : ℕ, ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ r : ℕ → ℝ, r 0 = δ →
      (∀ j < N, (r j) ^ q ≤ r (j + 1)) → δ ^ a ≤ r N := by
  obtain ⟨N, hN⟩ := exists_iteration_depth hq1 ha
  refine ⟨N, fun δ hδ hδ1 r hzero hstep => ?_⟩
  exact (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hN.le).trans
    (scale_chain_bound hq0 hδ r hzero hstep N le_rfl)

/-- Real-power scale factors telescope without finiteness assumptions on the areas. -/
theorem area_chain_bound {e : ℝ} {N : ℕ} (r : ℕ → ℝ)
    (hr : ∀ j ≤ N, 0 < r j) (A : ℕ → ENNReal)
    (hstep : ∀ j < N,
      ENNReal.ofReal ((r j / r (j + 1)) ^ e) * A (j + 1) ≤ A j) :
    ENNReal.ofReal ((r 0 / r N) ^ e) * A N ≤ A 0 := by
  have h : ∀ j ≤ N, ENNReal.ofReal ((r 0 / r j) ^ e) * A j ≤ A 0 := by
    intro j hj
    induction j with
    | zero => simp [(hr 0 (Nat.zero_le N)).ne']
    | succ j ih =>
      have hj' : j ≤ N := Nat.le_of_succ_le hj
      have hr0 := hr 0 (Nat.zero_le N)
      have hrj := hr j hj'
      have hrj1 := hr (j + 1) hj
      have hfactor : (r 0 / r (j + 1)) ^ e =
          (r 0 / r j) ^ e * (r j / r (j + 1)) ^ e := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        field_simp [(hr j hj').ne']
      rw [hfactor, ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _), mul_assoc]
      exact (mul_le_mul_right (hstep j (Nat.lt_of_succ_le hj)) _).trans (ih hj')
  exact h N le_rfl

/-- Once the terminal scale exceeds `δ ^ a`, a nonempty thickening gives the area bound. -/
theorem terminal_area_bound {δ r e a : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (hr1 : r ≤ 1) (he : 0 ≤ e) (hscale : δ ^ a ≤ r)
    {E : Set (ℝ × ℝ)} (hE : E.Nonempty) :
    ENNReal.ofReal (δ ^ (e + 2 * a)) ≤
      ENNReal.ofReal ((δ / r) ^ e) * volume (Metric.thickening r E) := by
  have hbase : δ ≤ δ / r := (le_div_iff₀ hr).2 (mul_le_of_le_one_right hδ.le hr1)
  have hfactor : δ ^ e ≤ (δ / r) ^ e := Real.rpow_le_rpow hδ.le hbase he
  have hsquare : δ ^ (2 * a) ≤ r ^ 2 := by
    calc
      δ ^ (2 * a) = (δ ^ a) ^ (2 : ℕ) := by
        rw [mul_comm (2 : ℝ) a, Real.rpow_mul hδ.le, Real.rpow_two]
      _ ≤ r ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hδ.le _) hscale 2
  calc
    ENNReal.ofReal (δ ^ (e + 2 * a)) =
        ENNReal.ofReal (δ ^ e) * ENNReal.ofReal (δ ^ (2 * a)) := by
      rw [Real.rpow_add hδ, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    _ ≤ ENNReal.ofReal ((δ / r) ^ e) * volume (Metric.thickening r E) :=
      mul_le_mul (ENNReal.ofReal_le_ofReal hfactor)
        ((ENNReal.ofReal_le_ofReal hsquare).trans (thickening_area_lower hE hr.le))
        zero_le zero_le

/-- Telescoping, a terminal nonempty set, and a coarse terminal scale suffice. -/
theorem projection_bound_of_chain {δ e a : ℝ} (hδ : 0 < δ) (he : 0 ≤ e)
    {N : ℕ} (r : ℕ → ℝ) (hr : ∀ j ≤ N, 0 < r j) (hzero : r 0 = δ)
    (hlast : r N ≤ 1) (hscale : δ ^ a ≤ r N)
    (A : ℕ → ENNReal)
    (hstep : ∀ j < N,
      ENNReal.ofReal ((r j / r (j + 1)) ^ e) * A (j + 1) ≤ A j)
    {E : Set (ℝ × ℝ)} (hE : E.Nonempty)
    (hterminal : volume (Metric.thickening (r N) E) ≤ A N) :
    ENNReal.ofReal (δ ^ (e + 2 * a)) ≤ A 0 := by
  have h := area_chain_bound r hr A hstep
  rw [hzero] at h
  exact (terminal_area_bound hδ (hr N le_rfl) hlast he hscale hE).trans
    ((mul_le_mul_right hterminal _).trans h)

end WangZahlLot.Obl.wz_normalized_projection_iteration
