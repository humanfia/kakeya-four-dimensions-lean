/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/QuadraticSampling.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Lib.K4QuadraticSublevel

/-! Finite polynomial tests for crossing an observed hidden bin.
The midpoint construction was described in x0357's o118 post of 2026-10-21
05:49 UTC. The proofs below are written here and reuse the accepted quadratic
sublevel library. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Set
open Submission.Lib.K4QuadraticSublevel

theorem quadratic_derivative_sub (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    (x z : ℝ) : p.derivative.eval z - p.derivative.eval x =
      (z - x) * p.derivative.derivative.eval x := by
  obtain ⟨a, b, c, rfl⟩ := quadratic_eq_coefficients p hp
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_pow,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one]
  norm_num
  ring

/-- The regular small-value conditions of a quadratic persist at the midpoint
of a sufficiently fine subdivision of its observed unit bin. -/
theorem quadratic_sampling_stability (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {κ x z : ℝ} (hκ : 1 ≤ κ) (hval : |p.eval x| ≤ κ)
    (hlower : 1 / κ ≤ |p.derivative.eval x|)
    (hupper : |p.derivative.eval x| ≤ κ)
    (hsecond : |p.derivative.derivative.eval x| ≤ κ)
    (hnear : |z - x| ≤ 1 / (4 * κ ^ 2)) :
    |p.eval z| ≤ 2 * κ ∧ 1 / (2 * κ) ≤ |p.derivative.eval z| := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hfrac : (1 : ℝ) / (4 * κ) ≤ κ := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * κ)).mpr
    nlinarith [sq_nonneg (κ - 1)]
  have hchange : |p.derivative.eval z - p.derivative.eval x| ≤ 1 / (4 * κ) := by
    rw [quadratic_derivative_sub p hp, abs_mul]
    calc
      _ ≤ (1 / (4 * κ ^ 2)) * κ := mul_le_mul hnear hsecond (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hderupper : |p.derivative.eval z| ≤ 2 * κ := by
    calc
      _ = |p.derivative.eval x + (p.derivative.eval z - p.derivative.eval x)| := by
        congr 1
        ring
      _ ≤ |p.derivative.eval x| + |p.derivative.eval z - p.derivative.eval x| := abs_add_le _ _
      _ ≤ κ + 1 / (4 * κ) := add_le_add hupper hchange
      _ ≤ 2 * κ := by linarith
  have hderlower : 1 / (2 * κ) ≤ |p.derivative.eval z| := by
    have htri : |p.derivative.eval x| ≤
        |p.derivative.eval z| + |p.derivative.eval z - p.derivative.eval x| := by
      calc
        _ = |p.derivative.eval z - (p.derivative.eval z - p.derivative.eval x)| := by
          congr 1
          ring
        _ ≤ _ := abs_sub _ _
    have hfrac' : (1 : ℝ) / (2 * κ) + 1 / (4 * κ) ≤ 1 / κ := by
      field_simp
      nlinarith
    linarith
  refine ⟨?_, hderlower⟩
  have hdiff : 2 * |p.eval z - p.eval x| ≤ 2 * κ := by
    have hsec := congrArg abs (quadratic_eval_sub p hp x z)
    simp only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at hsec
    calc
      _ = |z - x| * |p.derivative.eval x + p.derivative.eval z| := hsec
      _ ≤ |z - x| * (|p.derivative.eval x| + |p.derivative.eval z|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
      _ ≤ (1 / (4 * κ ^ 2)) * (κ + 2 * κ) :=
        mul_le_mul hnear (add_le_add hupper hderupper) (by positivity) (by positivity)
      _ = 3 / (4 * κ) := by field_simp <;> ring
      _ ≤ 2 * κ := by
        apply (div_le_iff₀ (by positivity : 0 < 4 * κ)).mpr
        nlinarith [sq_nonneg (κ - 1)]
  calc
    _ = |p.eval x + (p.eval z - p.eval x)| := by congr 1; ring
    _ ≤ |p.eval x| + |p.eval z - p.eval x| := abs_add_le _ _
    _ ≤ 2 * κ := by linarith

noncomputable def binMidpoint (m : ℕ) (n : ℤ) (i : Fin m) : ℝ :=
  (n : ℝ) + ((i : ℝ) + 1 / 2) / m

theorem floor_binMidpoint {m : ℕ} (hm : 0 < m) (n : ℤ) (i : Fin m) :
    ⌊binMidpoint m n i⌋ = n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hi : (i : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  apply Int.floor_eq_iff.mpr
  dsimp [binMidpoint]
  constructor
  · linarith [div_nonneg (show (0 : ℝ) ≤ (i : ℝ) + 1 / 2 by positivity) hmR.le]
  · have hfrac : ((i : ℝ) + 1 / 2) / m < 1 := (div_lt_one hmR).mpr (by linarith)
    linarith

/-- Every real number is close to a midpoint in its own integer observation bin. -/
theorem exists_binMidpoint_near {m : ℕ} (hm : 0 < m) (x : ℝ) :
    ∃ i : Fin m, |binMidpoint m ⌊x⌋ i - x| ≤ 1 / (2 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let y := x - (⌊x⌋ : ℝ)
  have hy0 : 0 ≤ y := sub_nonneg.mpr (Int.floor_le x)
  have hy1 : y < 1 := Int.fract_lt_one x
  let i := ⌊(m : ℝ) * y⌋₊
  have hprod : 0 ≤ (m : ℝ) * y := mul_nonneg hmR.le hy0
  have hlo : (i : ℝ) ≤ (m : ℝ) * y := Nat.floor_le hprod
  have hhi : (m : ℝ) * y < (i : ℝ) + 1 := Nat.lt_floor_add_one _
  have hiR : (i : ℝ) < m := hlo.trans_lt (by nlinarith)
  have hi : i < m := by exact_mod_cast hiR
  refine ⟨⟨i, hi⟩, ?_⟩
  have habs : |(m : ℝ) * y - i - 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have heq : binMidpoint m ⌊x⌋ ⟨i, hi⟩ - x =
      -((m : ℝ) * y - i - 1 / 2) / m := by
    dsimp [binMidpoint, y]
    field_simp
    simp only [Int.fract]
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hmR]
  calc
    _ ≤ ((1 : ℝ) / 2) / (m : ℝ) := div_le_div_of_nonneg_right habs hmR.le
    _ = _ := by ring

noncomputable def sampledQuadraticBins (p : Polynomial ℝ) (κ : ℝ) (m : ℕ) : Set ℤ :=
  {n | ∃ i : Fin m, |p.eval (binMidpoint m n i)| ≤ 2 * κ ∧
    1 / (2 * κ) ≤ |p.derivative.eval (binMidpoint m n i)|}

theorem mem_sampledQuadraticBins (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {κ x : ℝ} (hκ : 1 ≤ κ) {m : ℕ} (hm : 4 * κ ^ 2 ≤ m)
    (hval : |p.eval x| ≤ κ) (hlower : 1 / κ ≤ |p.derivative.eval x|)
    (hupper : |p.derivative.eval x| ≤ κ)
    (hsecond : |p.derivative.derivative.eval x| ≤ κ) :
    ⌊x⌋ ∈ sampledQuadraticBins p κ m := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hmR : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hmpos : 0 < m := by exact_mod_cast hmR
  obtain ⟨i, hi⟩ := exists_binMidpoint_near hmpos x
  refine ⟨i, quadratic_sampling_stability p hp hκ hval hlower hupper hsecond (hi.trans ?_)⟩
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith : 4 * κ ^ 2 ≤ 2 * (m : ℝ))

/-- The finite midpoint test accepts only quadratically many hidden bins. -/
theorem sampledQuadraticBins_card (p : Polynomial ℝ) (hp : p.natDegree ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) {m : ℕ} (hm : 0 < m) :
    (sampledQuadraticBins p κ m).Finite ∧
      ((sampledQuadraticBins p κ m).ncard : ℝ) ≤ 32 * κ ^ 2 + 8 := by
  have hgrid := grid_bins_quadratic_sublevel p hp (show 0 ≤ 2 * κ by positivity)
    (show 0 < 1 / (2 * κ) by positivity) (show (0 : ℝ) < 1 by norm_num) 0
  simp only [sub_zero, div_one] at hgrid
  have hsub : sampledQuadraticBins p κ m ⊆ Int.floor ''
      {x : ℝ | |p.eval x| ≤ 2 * κ ∧ 1 / (2 * κ) ≤ |p.derivative.eval x|} := by
    rintro n ⟨i, hi⟩
    exact ⟨binMidpoint m n i, hi, floor_binMidpoint hm n i⟩
  refine ⟨hgrid.1.subset hsub, ?_⟩
  have hc : ((sampledQuadraticBins p κ m).ncard : ℝ) ≤
      ((Int.floor '' {x : ℝ | |p.eval x| ≤ 2 * κ ∧
        1 / (2 * κ) ≤ |p.derivative.eval x|}).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hgrid.1
  apply (hc.trans hgrid.2).trans_eq
  field_simp
  ring

end Submission.Obl.k4_balanced_native_packet_transport.CPF
