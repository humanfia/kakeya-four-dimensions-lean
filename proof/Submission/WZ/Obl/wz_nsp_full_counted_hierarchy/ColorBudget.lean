-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nsp_full_counted_hierarchy.ColorBudget.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nsp_full_counted_hierarchy.Budgets
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize

namespace WangZahlLot.Obl.wz_nsp_full_counted_hierarchy

/-- A fixed multiplicative ratio needs only logarithmically many size colors;
the color count costs an arbitrarily small power of the scale. -/
theorem size_color_power {p θ R : ℝ} (hp : 0 < p) (hθ : 0 < θ) (hR : 1 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) (n : ℕ), 0 < δ → δ ≤ 1 → 0 < n →
      (n : ℝ) ≤ δ ^ (-p) → ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C * δ ^ (-θ) ∧
        ∃ color : ℕ → Fin q, ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
          color a = color b → (a : ℝ) ≤ R * b := by
  obtain ⟨C, hC, hlog⟩ := log_count_power_bound hp hθ
  have hlogR : 0 < Real.log R := Real.log_pos hR
  refine ⟨C / Real.log R + 1, by positivity, ?_⟩
  intro δ n hδ hδ1 hn hbound
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨k, hlo, hhi⟩ := exists_nat_pow_near hn1 hR
  have hklog : (k : ℝ) * Real.log R ≤ Real.log (n : ℝ) := by
    simpa only [Real.log_pow] using
      Real.log_le_log (pow_pos (by linarith : 0 < R) k) hlo
  have hnlog : Real.log (n : ℝ) ≤ C * δ ^ (-θ) := by
    apply le_trans (Real.log_le_log (by exact_mod_cast hn) (by linarith))
      (hlog δ n hδ hδ1 (Nat.cast_nonneg _) hbound)
  have hk : (k : ℝ) ≤ (C / Real.log R) * δ ^ (-θ) := by
    apply (le_div_iff₀ hlogR).mpr at hklog
    calc
      (k : ℝ) ≤ Real.log (n : ℝ) / Real.log R := hklog
      _ ≤ (C * δ ^ (-θ)) / Real.log R := div_le_div_of_nonneg_right hnlog hlogR.le
      _ = _ := by ring
  have hpow : 1 ≤ δ ^ (-θ) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show -θ ≤ 0 by linarith)
  refine ⟨k + 1, by omega, ?_, ?_⟩
  · push_cast
    nlinarith
  · exact WangZahlLot.Obl.wz_tower_balanced_refinement.exists_size_color n (k + 1) R
      (by omega) hR hhi

/-- A bounded number of fixed-ratio regularizations costs at most a prescribed
small power, uniformly for polynomially bounded original family sizes. -/
theorem regularization_color_budget {u : ℝ} (hu : 0 < u) (B : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∀ (δ : ℝ) (n : ℕ), 0 < δ → δ ≤ 1 → δ ≤ d →
      0 < n → (n : ℝ) ≤ δ ^ (-7 : ℝ) →
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ^ B ≤ δ ^ (-u) ∧
        ∃ color : ℕ → Fin q, ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
          color a = color b → (a : ℝ) ≤ (4 / 3 : ℝ) * b := by
  let θ := u / (2 * ((B : ℝ) + 1))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  obtain ⟨C, hC, hcolor⟩ := size_color_power (show (0 : ℝ) < 7 by norm_num) hθ
    (show (1 : ℝ) < 4 / 3 by norm_num)
  obtain ⟨d, hd, hconstant⟩ := constant_power_cutoff hC hθ
  refine ⟨d, hd, ?_⟩
  intro δ n hδ hδ1 hδd hn hbound
  obtain ⟨q, hq, hqbound, color, hc⟩ := hcolor δ n hδ hδ1 hn hbound
  have hq' : (q : ℝ) ≤ δ ^ (-2 * θ) := by
    calc
      (q : ℝ) ≤ C * δ ^ (-θ) := hqbound
      _ ≤ δ ^ (-θ) * δ ^ (-θ) :=
        mul_le_mul_of_nonneg_right (hconstant δ hδ hδd) (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (-2 * θ) := by rw [← Real.rpow_add hδ]; congr 1; ring
  refine ⟨q, hq, ?_, color, hc⟩
  calc
    (q : ℝ) ^ B ≤ (δ ^ (-2 * θ)) ^ B := pow_le_pow_left₀ (Nat.cast_nonneg _) hq' B
    _ = δ ^ ((-2 * θ) * B) := (Real.rpow_mul_natCast hδ.le _ _).symm
    _ ≤ δ ^ (-u) := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      have hden : 0 < (B : ℝ) + 1 := by positivity
      have he : 2 * θ * ((B : ℝ) + 1) = u := by dsimp [θ]; field_simp
      nlinarith

end WangZahlLot.Obl.wz_nsp_full_counted_hierarchy
