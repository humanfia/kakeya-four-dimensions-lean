import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.Basic

/-!
# Jets of a quadratic signal against a row sequence

For a row sequence `R : ℕ → ℝ` (the values `F_0 = F(t), F_1, …, F_m` at one time `t`), the jets are
`J_j = x^{(j)}(t) - R_j y(t) - j R_{j-1} y'` (`jet`).  Exact identities:
* `zS_sub_eq`: `S(s) - S(t) = (s - t) J_1(t) + (s - t)² (c₂ - R₁ c₄) - e y(s)` with
  `e = F(s) - F(t) - (s - t) R₁` (paper `a04:scalar-first-expansion`);
* `jet_sub_eq`: for `j ≥ 1`, `J_j(s) - J_j(t) = (s - t) (x^{(j+1)}(t) - g_j y(t) - R'_j y' - j g_{j-1} y')`
  where `g_i = (R'_i - R_i)/(s - t)` (paper `a04:jet-difference`);
* `zS_eq_taylor`: the final expansion `a04:final-jet-expansion`.
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open Finset

noncomputable section

/-- The derivatives `x^{(j)}(t)` of the quadratic `x`. -/
def xder (c : Fin 5 → ℝ) (t : ℝ) : ℕ → ℝ
  | 0 => zx c t
  | 1 => c 1 + 2 * c 2 * t
  | 2 => 2 * c 2
  | _ => 0

/-- The jet `J_j = x^{(j)}(t) - R_j y(t) - j R_{j-1} y'`. -/
def jet (R : ℕ → ℝ) (c : Fin 5 → ℝ) (t : ℝ) (j : ℕ) : ℝ :=
  xder c t j - R j * zy c t - (j : ℝ) * R (j - 1) * c 4

theorem jet_zero {F : ℝ → ℝ} {R : ℕ → ℝ} {c : Fin 5 → ℝ} {t : ℝ} (hR : R 0 = F t) :
    jet R c t 0 = zS F c t := by
  simp [jet, xder, zS, hR]

theorem xder_succ_sub {c : Fin 5 → ℝ} {s t : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    xder c s j - xder c t j = (s - t) * xder c t (j + 1) := by
  match j, hj with
  | 1, _ => simp [xder]; ring
  | 2, _ => simp [xder]
  | (n + 3), _ => simp [xder]

/-- `a04:scalar-first-expansion` (exact form). -/
theorem zS_sub_eq {F : ℝ → ℝ} {R : ℕ → ℝ} {c : Fin 5 → ℝ} {s t : ℝ} (hR : R 0 = F t) :
    zS F c s - zS F c t = (s - t) * jet R c t 1 + (s - t) ^ 2 * (c 2 - R 1 * c 4) -
      (F s - F t - (s - t) * R 1) * zy c s := by
  simp only [zS, zx, zy, jet, xder, hR]
  ring

/-- `a04:jet-difference` (exact form, multiplied out). -/
theorem jet_sub_eq {R R' : ℕ → ℝ} {c : Fin 5 → ℝ} {s t : ℝ} {j : ℕ} (hj : 1 ≤ j) :
    jet R' c s j - jet R c t j = (s - t) * xder c t (j + 1) - (R' j - R j) * zy c t -
      (s - t) * R' j * c 4 - (j : ℝ) * (R' (j - 1) - R (j - 1)) * c 4 := by
  have hx := xder_succ_sub (c := c) (s := s) (t := t) hj
  simp only [jet]
  have hy : zy c s = zy c t + (s - t) * c 4 := by simp only [zy]; ring
  rw [hy]
  linear_combination hx

/-- The Taylor polynomial of a row sequence at `u`. -/
def rowPoly (R : ℕ → ℝ) (M : ℕ) (u v : ℝ) : ℝ :=
  ∑ i ∈ range (M + 1), R i * (v - u) ^ i / (i.factorial : ℝ)

theorem xder_taylor {c : Fin 5 → ℝ} {u v : ℝ} {M : ℕ} (hM : 2 ≤ M) :
    ∑ i ∈ range (M + 1), xder c u i * (v - u) ^ i / (i.factorial : ℝ) = zx c v := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
  have hrest : ∑ i ∈ range k, xder c u (i + 1 + 1 + 1) * (v - u) ^ (i + 1 + 1 + 1) /
      ((i + 1 + 1 + 1).factorial : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [xder]
  rw [hrest]
  simp [xder, zx, Nat.factorial]
  ring

/-- `a04:final-jet-expansion` (exact form). -/
theorem zS_eq_taylor {F : ℝ → ℝ} {R : ℕ → ℝ} {c : Fin 5 → ℝ} {u v : ℝ} {M : ℕ} (hM : 2 ≤ M) :
    zS F c v = ∑ i ∈ range (M + 1), jet R c u i * (v - u) ^ i / (i.factorial : ℝ) -
      (F v - rowPoly R M u v) * zy c v - c 4 * R M * (v - u) ^ (M + 1) / (M.factorial : ℝ) := by
  have hsplit : ∀ i ∈ range (M + 1), jet R c u i * (v - u) ^ i / (i.factorial : ℝ) =
      xder c u i * (v - u) ^ i / (i.factorial : ℝ) - zy c u * (R i * (v - u) ^ i / (i.factorial : ℝ)) -
        c 4 * ((i : ℝ) * R (i - 1) * (v - u) ^ i / (i.factorial : ℝ)) := by
    intro i _; simp only [jet]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    xder_taylor hM, ← Finset.mul_sum, ← Finset.mul_sum]
  -- the shifted sum
  have hshift : ∑ i ∈ range (M + 1), (i : ℝ) * R (i - 1) * (v - u) ^ i / (i.factorial : ℝ) =
      (v - u) * (rowPoly R M u v - R M * (v - u) ^ M / (M.factorial : ℝ)) := by
    rw [Finset.sum_range_succ']
    simp only [CharP.cast_eq_zero, zero_mul, zero_div, add_zero]
    have : rowPoly R M u v - R M * (v - u) ^ M / (M.factorial : ℝ) =
        ∑ i ∈ range M, R i * (v - u) ^ i / (i.factorial : ℝ) := by
      rw [rowPoly, Finset.sum_range_succ]; ring
    rw [this, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    have hf : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hshift]
  simp only [rowPoly] at *
  have hy : zy c v = zy c u + (v - u) * c 4 := by simp only [zy]; ring
  simp only [zS]
  rw [hy]
  have hf : (M.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Coefficient-Lipschitz bound for the jets at a time in `[0,1]`. -/
theorem abs_jet_sub_le {R : ℕ → ℝ} {c c' : Fin 5 → ℝ} {t B r : ℝ} {j : ℕ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hB : ∀ i, |R i| ≤ B) (h : ‖c - c'‖ ≤ r) :
    |jet R c t j - jet R c' t j| ≤ (3 + 2 * B + j * B) * r := by
  have hc : ∀ e, |c e - c' e| ≤ r := fun e => by
    have := norm_le_pi_norm (c - c') e; rw [Real.norm_eq_abs] at this; simpa using this.trans h
  have hr : 0 ≤ r := le_trans (abs_nonneg _) (hc 0)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hxd : |xder c t j - xder c' t j| ≤ 3 * r := by
    match j with
    | 0 =>
      have := abs_zx_le (c := c - c') (K := r) (fun e => by simpa using hc e) ht
      have e : zx (c - c') t = zx c t - zx c' t := by simp only [zx, Pi.sub_apply]; ring
      simpa [xder, e] using this
    | 1 =>
      simp only [xder]
      have h1 := hc 1; have h2 := hc 2
      have : c 1 + 2 * c 2 * t - (c' 1 + 2 * c' 2 * t) = (c 1 - c' 1) + 2 * t * (c 2 - c' 2) := by
        ring
      rw [this]
      calc |(c 1 - c' 1) + 2 * t * (c 2 - c' 2)| ≤ |c 1 - c' 1| + |2 * t * (c 2 - c' 2)| :=
            abs_add_le _ _
        _ = |c 1 - c' 1| + 2 * t * |c 2 - c' 2| := by
            rw [abs_mul, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ 2 * t)]
        _ ≤ r + 2 * 1 * r := by
            have := mul_le_mul (by linarith [ht.2] : 2 * t ≤ 2 * 1) h2 (abs_nonneg _) (by norm_num)
            linarith
        _ = 3 * r := by ring
    | 2 =>
      simp only [xder]
      rw [← mul_sub, abs_mul]; norm_num; linarith [hc 2]
    | (n + 3) => simp [xder]; positivity
  have hyd : |zy c t - zy c' t| ≤ 2 * r := by
    have h3 := hc 3; have h4 := hc 4
    simp only [zy]
    have : c 3 + c 4 * t - (c' 3 + c' 4 * t) = (c 3 - c' 3) + (c 4 - c' 4) * t := by ring
    rw [this]
    calc |(c 3 - c' 3) + (c 4 - c' 4) * t| ≤ |c 3 - c' 3| + |(c 4 - c' 4) * t| := abs_add_le _ _
      _ = |c 3 - c' 3| + |c 4 - c' 4| * t := by rw [abs_mul, abs_of_nonneg ht.1]
      _ ≤ r + r * 1 := by
          have := mul_le_mul h4 ht.2 ht.1 hr
          linarith
      _ = 2 * r := by ring
  have e : jet R c t j - jet R c' t j = (xder c t j - xder c' t j) - R j * (zy c t - zy c' t) -
      (j : ℝ) * R (j - 1) * (c 4 - c' 4) := by simp only [jet]; ring
  rw [e]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  calc |(xder c t j - xder c' t j) - R j * (zy c t - zy c' t) - (j : ℝ) * R (j - 1) * (c 4 - c' 4)|
      ≤ |xder c t j - xder c' t j| + |R j| * |zy c t - zy c' t| +
          (j : ℝ) * |R (j - 1)| * |c 4 - c' 4| := by
        have h1 := abs_sub (xder c t j - xder c' t j - R j * (zy c t - zy c' t))
          ((j : ℝ) * R (j - 1) * (c 4 - c' 4))
        have h2 := abs_sub (xder c t j - xder c' t j) (R j * (zy c t - zy c' t))
        rw [abs_mul (R j), abs_mul ((j : ℝ) * R (j - 1)), abs_mul (j : ℝ),
          abs_of_nonneg hj] at *
        linarith
    _ ≤ 3 * r + B * (2 * r) + (j : ℝ) * B * r := by
        gcongr
        · exact hB j
        · exact hB (j - 1)
        · exact hc 4
    _ = (3 + 2 * B + j * B) * r := by ring

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
