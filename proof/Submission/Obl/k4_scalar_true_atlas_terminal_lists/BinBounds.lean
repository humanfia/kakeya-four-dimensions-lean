import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Basic
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Raw

/-! A polynomial number of hidden bins suffices on every raw selected chart. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable def hiddenBins (R : ℝ) : Finset ℤ := Finset.Icc ⌈-R⌉ ⌊R⌋

theorem mem_hiddenBins {R : ℝ} {b : ℤ} : b ∈ hiddenBins R ↔ |(b : ℝ)| ≤ R := by
  simp only [hiddenBins, Finset.mem_Icc, Int.ceil_le, Int.le_floor, abs_le]

theorem hiddenBins_card_le {R : ℝ} (hR : 0 ≤ R) :
    ((hiddenBins R).card : ℝ) ≤ 2 * R + 1 := by
  have hcount := Submission.Obl.k4_scalar_terminal_chart_packet_extraction.count_int_near_le 0 R hR
  have hsub : (↑(hiddenBins R) : Set ℤ) ⊆ {b : ℤ | |(b : ℝ) - 0| ≤ R} := by
    intro b hb
    change |(b : ℝ) - 0| ≤ R
    simpa only [sub_zero] using mem_hiddenBins.mp hb
  have h := (measure_mono (μ := Measure.count) hsub).trans hcount
  rw [Measure.count_apply_finset] at h
  simpa using ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ 2 * R + 1) h

theorem trajectory_hidden_bound (l : Trajectory) (t R : ℝ) (hR : 0 ≤ R)
    (hl : ∀ e, |l.2 e| ≤ R) (ht : t ∈ Icc (0 : ℝ) 1) : |x l t| ≤ 3 * R := by
  have h1 : |t * l.2 3| ≤ R := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul ht.2 (hl 3) (abs_nonneg _) zero_le_one).trans_eq (one_mul R)
  have h2 : |t ^ 2 * l.2 4| ≤ R := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    exact (mul_le_mul ht2 (hl 4) (abs_nonneg _) zero_le_one).trans_eq (one_mul R)
  exact (abs_add_three _ _ _).trans (by change |l.2 2| + _ + _ ≤ _; linarith [hl 2])

theorem hidden_floor_bound {x N a : ℝ} (ha : 0 < a) (hx : |x| ≤ 3 * N) :
    |((⌊x / a⌋ : ℤ) : ℝ)| ≤ 3 * N / a + 1 := by
  have hlo := Int.floor_le (x / a)
  have hhi := Int.lt_floor_add_one (x / a)
  have hx' : |x / a| ≤ 3 * N / a := by
    rw [abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right hx ha.le
  rw [abs_le] at hx' ⊢
  constructor <;> linarith [hx'.1, hx'.2]

/-- The hidden bin bound depends only on length, and not on the raw time
exponent or on any subsequent list tolerance. -/
theorem RawChartData.hidden_bins {p : Data} (hp : Exact p)
    {B k T n : ℕ} {r b h δ : ℝ} {isTrue : Bool}
    {γ : Fin n → Fin (worlds p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Trajectory} {C : Fin n → Set Incidence} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    (hd : RawChartData p B r b h δ isTrue k T n γ j A C u v J P) (hδ : δ ≤ 1) :
    ∀ i q, q ∈ C i → ⌊x q.1 q.2 / (N p k ^ (-r))⌋ ∈
      hiddenBins (3 * N p k / (N p k ^ (-r)) + 1) := by
  rcases hd with ⟨hT, hn, hm, hdisj, hsub, hchart, hmass⟩
  intro i q hq
  have hN : 1 ≤ N p k := le_trans (by norm_num) (hp.resolution_ge k)
  have hpow : N p k ^ δ ≤ N p k := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN hδ
  have hAq := (hsub i hq).2.1
  have hcoef : ∀ e, |q.1.2 e| ≤ N p k := fun e =>
    (((hchart i).2.2.2.2.2.2.2.1 q.1 hAq).2 e).trans hpow
  have ht := I_subset_unit T (j i) (hsub i hq).2.2
  exact mem_hiddenBins.mpr (hidden_floor_bound (Real.rpow_pos_of_pos (by linarith [hN]) _)
    (trajectory_hidden_bound q.1 q.2 (N p k) (by linarith) hcoef ht))

theorem hiddenBins_polynomial_bound {N L : ℝ} (hN : 2 ≤ N) (hL : 0 ≤ L) :
    ((hiddenBins (3 * N / (N ^ (-L)) + 1)).card : ℝ) ≤
      N ^ (⌈L⌉₊ + 5 : ℕ) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have heq : N / N ^ (-L) = N ^ (L + 1) := by
    calc
      _ = N * N ^ L := by rw [Real.rpow_neg hN0.le, div_eq_mul_inv, inv_inv]
      _ = N ^ (1 + L) := by rw [Real.rpow_add hN0, Real.rpow_one]
      _ = _ := by congr 1; ring
  have hx : 2 ≤ N ^ (L + 1) := by
    apply hN.trans
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (1 : ℝ) ≤ L + 1)
  have hceil : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hpow : N ^ (L + 1) ≤ N ^ (⌈L⌉₊ + 1 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by exact_mod_cast (by linarith : L + 1 ≤ (⌈L⌉₊ : ℝ) + 1))
  have h8 : (8 : ℝ) ≤ N ^ 3 := by
    calc
      8 = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN 3
  calc
    _ ≤ 2 * (3 * N / (N ^ (-L)) + 1) + 1 := hiddenBins_card_le (by positivity)
    _ = 6 * N ^ (L + 1) + 3 := by rw [mul_div_assoc, heq]; ring
    _ ≤ 8 * N ^ (L + 1) := by linarith
    _ ≤ N ^ 3 * N ^ (⌈L⌉₊ + 1 : ℕ) := mul_le_mul h8 hpow (by positivity) (by positivity)
    _ = N ^ (⌈L⌉₊ + 4 : ℕ) := by rw [← pow_add]; congr 1; omega
    _ ≤ N ^ (⌈L⌉₊ + 5 : ℕ) := pow_le_pow_right₀ hN1 (by omega)

/-- A uniform polynomial atom budget for all original-copy slices. -/
theorem crossing_atom_budget {N m n : ℝ} {A B : ℕ}
    (hN : 2 ≤ N) (hm : m ≤ N ^ (A + 5)) (hm0 : 0 ≤ m) (hn : n ≤ N ^ B)
    (hn0 : 0 ≤ n) :
    N ^ B + m * (2 + n * 6) ≤ N ^ (B + A + 12) := by
  have hN1 : 1 ≤ N := by linarith
  have hx : 1 ≤ N ^ B := one_le_pow₀ hN1
  have hy : 1 ≤ N ^ (A + 5) := one_le_pow₀ hN1
  have h9 : (9 : ℝ) ≤ N ^ 4 := by
    apply le_trans (by norm_num : (9 : ℝ) ≤ 2 ^ 4)
    exact pow_le_pow_left₀ (by norm_num) hN 4
  calc
    _ ≤ N ^ B + N ^ (A + 5) * (2 + N ^ B * 6) := by gcongr
    _ ≤ 9 * (N ^ B * N ^ (A + 5)) := by nlinarith
    _ ≤ N ^ 4 * (N ^ B * N ^ (A + 5)) := by gcongr
    _ = N ^ (B + A + 9) := by simp only [← pow_add]; congr 1; omega
    _ ≤ N ^ (B + A + 12) := pow_le_pow_right₀ hN1 (by omega)

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
