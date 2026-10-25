-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_convex_count_composition.Arithmetic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_tower_convex_count_composition

/-- A fixed loss at each of finitely many levels is absorbed into an exponent margin. -/
theorem power_budget (C : ℝ) (hC : 1 ≤ C) (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ ε ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d₀ →
        ∀ j : ℕ, j ≤ B → (C * δ ^ (-θ)) ^ j ≤ δ ^ (-ε) := by
  let θ : ℝ := ε / (2 * ((B : ℝ) + 1))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : 2 * θ * ((B : ℝ) + 1) = ε := by
    dsimp [θ]
    field_simp
  have hθε : θ ≤ ε := by nlinarith [Nat.cast_nonneg (α := ℝ) B]
  let d₀ : ℝ := C ^ (-1 / θ)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hd₀ : 0 < d₀ := Real.rpow_pos_of_pos hCpos _
  refine ⟨θ, hθ, hθε, d₀, hd₀, ?_⟩
  intro δ hδ hδ1 hδd j hj
  have hd₀pow : d₀ ^ (-θ) = C := by
    dsimp [d₀]
    rw [← Real.rpow_mul hCpos.le]
    have he : (-1 / θ) * (-θ) = 1 := by field_simp
    rw [he, Real.rpow_one]
  have hCL : C ≤ δ ^ (-θ) := by
    rw [← hd₀pow]
    exact Real.rpow_le_rpow_of_nonpos hδ hδd (by linarith)
  have hbase : C * δ ^ (-θ) ≤ δ ^ (-2 * θ) := by
    calc
      C * δ ^ (-θ) ≤ δ ^ (-θ) * δ ^ (-θ) := by gcongr
      _ = δ ^ (-2 * θ) := by rw [← Real.rpow_add hδ]; congr 1; ring
  calc
    (C * δ ^ (-θ)) ^ j ≤ (δ ^ (-2 * θ)) ^ j :=
      pow_le_pow_left₀ (mul_nonneg hCpos.le (Real.rpow_nonneg hδ.le _)) hbase j
    _ = δ ^ (-2 * θ * (j : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    _ ≤ δ ^ (-ε) := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      have hj' : (j : ℝ) ≤ B := by exact_mod_cast hj
      nlinarith

end WangZahlLot.Obl.wz_tower_convex_count_composition
