/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/GridCrossing.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/GridCrossing.lean. Earlier provenance is retained below. -/
import Submission.Lib.K4QuadraticSublevel

/-! Finite tests for the hidden-coordinate bins crossed by a quadratic chart.

The supplied paper's Lemma `a01:saturation` uses these crossings to make chart
labels known by the current observation.  The finite sub-bin construction was
suggested in session x0357's post on o118, 2026-10-21 05:49Z.  Here the tests
are explicit evaluations, so their later pullbacks have Boolean polynomial format.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Set

/-- The left endpoint of one of the `m` equal subdivisions of hidden bin `n`. -/
noncomputable def subBinPoint (δ : ℝ) (m : ℕ) (n : ℤ) (i : Fin m) : ℝ :=
  δ * ((n : ℝ) + (i : ℝ) / m)

theorem floor_subBinPoint {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (n : ℤ) (i : Fin m) :
    ⌊subBinPoint δ m n i / δ⌋ = n := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by
    intro h
    simpa [h] using i.isLt))
  rw [subBinPoint, mul_div_cancel_left₀ _ hδ.ne']
  apply Int.floor_eq_iff.mpr
  have hi : (i : ℝ) < m := by exact_mod_cast i.isLt
  constructor
  · linarith [div_nonneg (show (0 : ℝ) ≤ i by positivity) hm.le]
  · have : (i : ℝ) / m < 1 := (div_lt_one hm).mpr hi
    linarith

/-- Every point has a nearby tested point in its own hidden bin. -/
theorem exists_subBinPoint {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) (w : ℝ) :
    ∃ i : Fin m, |subBinPoint δ m ⌊w / δ⌋ i - w| ≤ δ / m := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let n : ℤ := ⌊w / δ⌋
  let u : ℝ := w / δ - n
  have hu0 : 0 ≤ u := sub_nonneg.mpr (Int.floor_le _)
  have hu1 : u < 1 := by
    have := Int.lt_floor_add_one (w / δ)
    change w / δ < (n : ℝ) + 1 at this
    change w / δ - (n : ℝ) < 1
    linarith
  let j : ℤ := ⌊(m : ℝ) * u⌋
  have hj0 : 0 ≤ j := Int.floor_nonneg.mpr (mul_nonneg hmR.le hu0)
  have hjm : j < m := by
    apply Int.floor_lt.mpr
    exact_mod_cast mul_lt_of_lt_one_right hmR hu1
  let i : Fin m := ⟨j.toNat, by omega⟩
  have hi : (i : ℝ) = j := by
    change (j.toNat : ℝ) = (j : ℝ)
    exact_mod_cast Int.toNat_of_nonneg hj0
  refine ⟨i, ?_⟩
  have hjle : (j : ℝ) ≤ (m : ℝ) * u := Int.floor_le _
  have hjgt : (m : ℝ) * u < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hw : w = δ * (n + u) := by
    dsimp [u]
    field_simp
    <;> ring
  have hd : subBinPoint δ m n i - w = δ / m * ((j : ℝ) - m * u) := by
    dsimp only [subBinPoint]
    rw [hi]
    calc
      _ = δ * (n + (j : ℝ) / m) - δ * (n + u) := by rw [← hw]
      _ = _ := by field_simp <;> ring
  change |subBinPoint δ m n i - w| ≤ δ / m
  rw [hd, abs_mul, abs_of_pos (div_pos hδ hmR)]
  apply mul_le_of_le_one_right (by positivity)
  rw [abs_le]
  constructor <;> linarith

/-- The derivative of a quadratic has constant slope. -/
theorem quadratic_derivative_eval_sub (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    (w z : ℝ) :
    p.derivative.eval z - p.derivative.eval w =
      p.derivative.derivative.eval w * (z - w) := by
  obtain ⟨a, b, c, rfl⟩ := Submission.Lib.K4QuadraticSublevel.quadratic_eq_coefficients p hp
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one]
  norm_num
  ring

/-- Finite value and derivative tests for a hidden bin. -/
def QuadraticCrosses (p : Polynomial ℝ) (a B κ : ℝ) (m : ℕ) (n : ℤ) : Prop :=
  ∃ i : Fin m, |p.eval (subBinPoint (a / B) m n i)| ≤ 2 * κ * a ∧
    B / (2 * κ) ≤ |p.derivative.eval (subBinPoint (a / B) m n i)|

/-- The relaxed tests persist at a nearby sub-bin endpoint. -/
theorem quadratic_tests_nearby (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {a B κ m w z : ℝ} (ha : 0 < a) (hB : 0 < B) (hκ : 1 ≤ κ)
    (hmesh : 4 * κ ^ 2 ≤ m)
    (hw : |p.eval w| ≤ κ * a)
    (hlo : B / κ ≤ |p.derivative.eval w|)
    (hhi : |p.derivative.eval w| ≤ κ * B)
    (hcurv : |p.derivative.derivative.eval w| ≤ κ * B ^ 2 / a)
    (hdist : |z - w| ≤ (a / B) / m) :
    |p.eval z| ≤ 2 * κ * a ∧ B / (2 * κ) ≤ |p.derivative.eval z| := by
  have hκ0 : 0 < κ := by linarith
  have hκsq : 1 ≤ κ ^ 2 := by nlinarith
  have hm : 0 < m := by nlinarith
  have hm2 : 2 ≤ m := by nlinarith
  have hdiff : |p.derivative.eval z - p.derivative.eval w| ≤ B / (2 * κ) := by
    rw [quadratic_derivative_eval_sub p hp, abs_mul]
    calc
      _ ≤ (κ * B ^ 2 / a) * ((a / B) / m) :=
        mul_le_mul hcurv hdist (abs_nonneg _) (by positivity)
      _ = κ * B / m := by field_simp
      _ ≤ B / (2 * κ) := by
        apply (div_le_div_iff₀ hm (by positivity : 0 < 2 * κ)).mpr
        have := mul_le_mul_of_nonneg_left hmesh hB.le
        nlinarith
  have hhalf : B / (2 * κ) ≤ κ * B := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * κ)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hκsq hB.le]
  have hdz : |p.derivative.eval z| ≤ 2 * κ * B := by
    have ht := abs_add_le (p.derivative.eval z - p.derivative.eval w)
      (p.derivative.eval w)
    rw [sub_add_cancel] at ht
    linarith
  have hdzlo : B / (2 * κ) ≤ |p.derivative.eval z| := by
    have ht := abs_sub_abs_le_abs_sub (p.derivative.eval w) (p.derivative.eval z)
    rw [abs_sub_comm] at ht
    have heq : B / κ = 2 * (B / (2 * κ)) := by field_simp
    linarith
  refine ⟨?_, hdzlo⟩
  have heq := congrArg abs
    (Submission.Lib.K4QuadraticSublevel.quadratic_eval_sub p hp w z)
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at heq
  have hsum : |p.derivative.eval w + p.derivative.eval z| ≤ 3 * κ * B :=
    (abs_add_le _ _).trans (by linarith)
  have hdiffval : |p.eval z - p.eval w| ≤ κ * a := by
    have hbound : 2 * |p.eval z - p.eval w| ≤ ((a / B) / m) * (3 * κ * B) := by
      rw [heq]
      exact mul_le_mul hdist hsum (abs_nonneg _) (by positivity)
    have hid : ((a / B) / m) * (3 * κ * B) = 3 * κ * a / m := by
      field_simp
    rw [hid] at hbound
    have hb : 3 * κ * a / m ≤ 2 * κ * a := by
      apply (div_le_iff₀ hm).mpr
      nlinarith [mul_le_mul_of_nonneg_left hm2 (show 0 ≤ κ * a by positivity)]
    linarith
  have ht := abs_add_le (p.eval z - p.eval w) (p.eval w)
  rw [sub_add_cancel] at ht
  linarith

/-- Every selected hidden point passes the finite tests in its observed bin. -/
theorem quadratic_crosses_of_tests (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {a B κ : ℝ} {m : ℕ} (ha : 0 < a) (hB : 0 < B) (hκ : 1 ≤ κ)
    (hmesh : 4 * κ ^ 2 ≤ (m : ℝ)) {w : ℝ}
    (hw : |p.eval w| ≤ κ * a)
    (hlo : B / κ ≤ |p.derivative.eval w|)
    (hhi : |p.derivative.eval w| ≤ κ * B)
    (hcurv : |p.derivative.derivative.eval w| ≤ κ * B ^ 2 / a) :
    QuadraticCrosses p a B κ m ⌊w / (a / B)⌋ := by
  have hm : 0 < m := by
    have : 0 < (m : ℝ) := lt_of_lt_of_le (by nlinarith : 0 < 4 * κ ^ 2) hmesh
    exact_mod_cast this
  obtain ⟨i, hi⟩ := exists_subBinPoint (div_pos ha hB) hm w
  exact ⟨i, quadratic_tests_nearby p hp ha hB hκ hmesh hw hlo hhi hcurv hi⟩

/-- At a fixed base point the finite tests cross only subpower many hidden bins. -/
theorem quadratic_crossing_bins (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {a B κ : ℝ} (ha : 0 < a) (hB : 0 < B) (hκ : 0 < κ) (m : ℕ) :
    {n : ℤ | QuadraticCrosses p a B κ m n}.Finite ∧
      ({n : ℤ | QuadraticCrosses p a B κ m n}.ncard : ℝ) ≤
        8 * (1 + 4 * κ ^ 2) := by
  have h := Submission.Lib.K4QuadraticSublevel.grid_bins_quadratic_sublevel p hp
    (show 0 ≤ 2 * κ * a by positivity) (div_pos hB (by positivity : 0 < 2 * κ))
    (div_pos ha hB) 0
  have hsub : {n : ℤ | QuadraticCrosses p a B κ m n} ⊆
      (fun w : ℝ => ⌊(w - 0) / (a / B)⌋) ''
        {w : ℝ | |p.eval w| ≤ 2 * κ * a ∧ B / (2 * κ) ≤ |p.derivative.eval w|} := by
    rintro n ⟨i, hi⟩
    refine ⟨subBinPoint (a / B) m n i, hi, ?_⟩
    simpa only [sub_zero] using floor_subBinPoint (div_pos ha hB) n i
  refine ⟨h.1.subset hsub, ?_⟩
  calc
    _ ≤ (((fun w : ℝ => ⌊(w - 0) / (a / B)⌋) ''
        {w : ℝ | |p.eval w| ≤ 2 * κ * a ∧ B / (2 * κ) ≤ |p.derivative.eval w|}).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub h.1
    _ ≤ 8 * (1 + (2 * κ * a) / ((B / (2 * κ)) * (a / B))) := h.2
    _ = _ := by field_simp <;> ring

end Submission.Obl.k4_balanced_native_packet_transport.CPF
