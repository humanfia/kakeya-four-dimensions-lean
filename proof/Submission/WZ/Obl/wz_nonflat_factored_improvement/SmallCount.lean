-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.SmallCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Counts
import Submission.WZ.Obl.wz_nonflat_factored_improvement.Weight

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

open MeasureTheory

/-- The small convex-count regime follows directly from `D`, with no factoring or rescaling. -/
theorem improvement_of_small_count {σ ω u : ℝ} (hσ : σ ≤ 1 / 2) (hgap : ω < u)
    (hD : EstimateD σ ω) :
    ∃ A : ℝ, 0 < A ∧ ∃ η : ℝ, 0 < η ∧
      ∀ ε : ℝ, 0 < ε → ∀ ν : ℝ, 0 < ν → ν ≤ η →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ m : ℝ, 1 ≤ m → m ≤ δ ^ (-η) →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        FamilyHypotheses ν δ n x v Y (CountHypotheses δ m (δ ^ (-ν)) n x v
          (target σ (u - (u - ω) / 2) ε A δ m n ≤ volume (⋃ i, Y i))) := by
  obtain ⟨A, hA, η, hη, H⟩ := hD ((u - ω) / 4) (by positivity)
  refine ⟨A, hA, η, hη, ?_⟩
  intro ε hε ν hν hνη δ hδ hδ100 m hm hmδ n x v Y
    hn hv hball hdist hYm hYT hden hconv hslab
  have hδ1 : δ ≤ 1 := by linarith
  have hden' : ENNReal.ofReal (δ ^ η * n * δ ^ 2) ≤ ∑ i, volume (Y i) := by
    apply le_trans (ENNReal.ofReal_le_ofReal _) hden
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hνη)
        (Nat.cast_nonneg n)) (sq_nonneg δ)
  have hslab' : SlabCount δ (δ ^ (-η)) x v :=
    slabCount_mono (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hνη)) hslab
  have hD' := H δ hδ hδ100 n x v Y hn hv hball hdist hYm hYT hden'
    (convexCount_mono hmδ hconv) hslab'
  rw [target_eq_weight]
  apply le_trans (ENNReal.ofReal_le_ofReal _) hD'
  calc
    _ ≤ A * δ ^ (ω + (u - ω) / 4) *
        ((n : ℝ) * δ ^ 2 * ((n : ℝ) * δ) ^ (-σ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)) hA.le
      · exact weight_le_normalized hδ hm (by linarith) n
      · exact weight_nonneg hδ.le (by linarith) σ n
      · positivity
    _ = _ := by ring

end WangZahlLot.Obl.wz_nonflat_factored_improvement
