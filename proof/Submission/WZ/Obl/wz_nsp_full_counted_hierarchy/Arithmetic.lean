-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

open scoped BigOperators

/-- The lower copy-count estimate forces a nonempty family of motions. -/
theorem copies_pos {N : ℕ} {ρ M r : ℝ} (hρ : 0 < ρ)
    (h : ρ ^ 2 ≤ (N : ℝ) * M * r ^ 2) : 0 < N := by
  by_contra hn
  have he : N = 0 := by omega
  simp only [he, Nat.cast_zero, zero_mul] at h
  nlinarith

/-- Upper copy counts telescope using the total mass at consecutive layers.
No division by a possibly empty layer is needed. -/
theorem copy_mass_step {N n k : ℕ} {r ρ M L : ℝ}
    (hcount : (n : ℝ) ≤ (k : ℝ) * M)
    (hlocal : M * r ^ 2 ≤ L * ρ ^ 2)
    (hupper : (N : ℝ) * M * r ^ 2 ≤ ρ ^ 2 + M * r ^ 2) :
    (N : ℝ) * ((n : ℝ) * r ^ 2) ≤ (1 + L) * ((k : ℝ) * ρ ^ 2) := by
  calc
    (N : ℝ) * ((n : ℝ) * r ^ 2) ≤ (k : ℝ) * ((N : ℝ) * M * r ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hcount
        (mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sq_nonneg r))]
    _ ≤ (k : ℝ) * (ρ ^ 2 + M * r ^ 2) :=
      mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg _)
    _ ≤ (1 + L) * ((k : ℝ) * ρ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg (α := ℝ) k)]

/-- Multiply a bounded number of copy steps; the intermediate masses cancel. -/
theorem copy_mass_telescopes (N : ℕ → ℕ) (q : ℕ → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (J : ℕ)
    (hstep : ∀ j, j < J → (N j : ℝ) * q (j + 1) ≤ L * q j) :
    ((∏ j ∈ Finset.range J, N j : ℕ) : ℝ) * q J ≤ L ^ J * q 0 := by
  induction J with
  | zero => simp
  | succ J ih =>
      have hi := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
      have hs := hstep J (Nat.lt_succ_self J)
      rw [Finset.prod_range_succ, Nat.cast_mul]
      calc
        ((∏ j ∈ Finset.range J, N j : ℕ) : ℝ) * (N J : ℝ) * q (J + 1) =
            ((∏ j ∈ Finset.range J, N j : ℕ) : ℝ) * ((N J : ℝ) * q (J + 1)) := by ring
        _ ≤ ((∏ j ∈ Finset.range J, N j : ℕ) : ℝ) * (L * q J) :=
          mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
        _ = L * (((∏ j ∈ Finset.range J, N j : ℕ) : ℝ) * q J) := by ring
        _ ≤ L * (L ^ J * q 0) := mul_le_mul_of_nonneg_left hi hL
        _ = L ^ (J + 1) * q 0 := by rw [pow_succ]; ring

/-- A polynomial bound on the number of parents costs an arbitrarily small
power in the logarithmic factor of the single-scale theorem. -/
theorem log_count_power_bound {p θ : ℝ} (hp : 0 < p) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ K : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ K →
      K ≤ δ ^ (-p) → Real.log (2 + K) ≤ C * δ ^ (-θ) := by
  let q := θ / p
  have hq : 0 < q := div_pos hθ hp
  refine ⟨3 ^ q / q, by positivity, ?_⟩
  intro δ K hδ hδ1 hK hbound
  have hpow : 1 ≤ δ ^ (-p) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show -p ≤ 0 by linarith)
  have hsum : 2 + K ≤ 3 * δ ^ (-p) := by linarith
  have hexp : -p * q = -θ := by dsimp [q]; field_simp
  calc
    Real.log (2 + K) ≤ (2 + K) ^ q / q :=
      Real.log_le_rpow_div (by linarith) hq
    _ ≤ (3 * δ ^ (-p)) ^ q / q := by
      apply div_le_div_of_nonneg_right _ hq.le
      exact Real.rpow_le_rpow (by linarith) hsum hq.le
    _ = (3 ^ q / q) * δ ^ (-θ) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hδ.le _),
        ← Real.rpow_mul hδ.le, hexp]
      ring

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
