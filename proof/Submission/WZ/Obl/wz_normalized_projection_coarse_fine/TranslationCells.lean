-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.TranslationCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.DyadicCells
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.TranslationAverage
import Submission.WZ.Obl.wz_nsp_translation_model.Counting

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_nsp_translation_model

noncomputable section

def dyadicCorner (k : ℕ) (l : Fin 3 → ℤ) : Space :=
  WithLp.toLp 2 (fun i => (l i : ℝ) * ((2 : ℝ) ^ k)⁻¹)

lemma dyadicLabel_corner (k : ℕ) (l : Fin 3 → ℤ) :
    dyadicLabel k (dyadicCorner k l) = l := by
  funext i
  simp only [dyadicLabel, dyadicCorner, WithLp.ofLp_toLp]
  have he : (2 : ℝ) ^ k * ((l i : ℝ) * ((2 : ℝ) ^ k)⁻¹) = l i := by
    field_simp
  rw [he, Int.floor_intCast]

lemma dyadic_cell_subset_ball {k : ℕ} {l : Fin 3 → ℤ} {p : Space}
    (hp : dyadicLabel k p = l) : p ∈ ball (dyadicCorner k l) (2 * ((2 : ℝ) ^ k)⁻¹) := by
  have hd := dist_le_of_dyadicLabel_eq (hp.trans (dyadicLabel_corner k l).symm)
  have hs : Real.sqrt (3 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  exact hd.trans_lt (mul_lt_mul_of_pos_right hs (by positivity))

/-- Cubic translation averages also control each dyadic cell, uniformly in the cell label. -/
theorem translated_cell_average {δ : ℝ} {m n : ℕ} (t : Fin m → Space) (q : Fin n → Space)
    (havg : ∀ (q q₀ : Space) (r : ℝ), δ ≤ r →
      (Set.ncard {s | q + t s ∈ ball q₀ r} : ℝ) ≤ 65536 * (m : ℝ) * r ^ 3)
    (k : ℕ) (l : Fin 3 → ℤ) (hδk : δ ≤ ((2 : ℝ) ^ k)⁻¹) :
    (∑ s, (Set.ncard {i | dyadicLabel k (q i + t s) = l} : ℝ)) ≤
      524288 * (m : ℝ) * (n : ℝ) * (((2 : ℝ) ^ k)⁻¹) ^ 3 := by
  classical
  have hswap : (∑ s, (Set.ncard {i | dyadicLabel k (q i + t s) = l} : ℝ)) =
      ∑ i, (Set.ncard {s | dyadicLabel k (q i + t s) = l} : ℝ) := by
    simp only [ncard_eq_sum]
    exact Finset.sum_comm
  rw [hswap]
  calc
    _ ≤ ∑ _i : Fin n, 65536 * (m : ℝ) * (2 * ((2 : ℝ) ^ k)⁻¹) ^ 3 := by
      apply Finset.sum_le_sum
      intro i hi
      have hc : Set.ncard {s | dyadicLabel k (q i + t s) = l} ≤
          Set.ncard {s | q i + t s ∈ ball (dyadicCorner k l) (2 * ((2 : ℝ) ^ k)⁻¹)} :=
        Set.ncard_mono (fun _ hs => dyadic_cell_subset_ball hs)
      exact (show (Set.ncard {s | dyadicLabel k (q i + t s) = l} : ℝ) ≤
          (Set.ncard {s | q i + t s ∈ ball (dyadicCorner k l) (2 * ((2 : ℝ) ^ k)⁻¹)} : ℝ)
        by exact_mod_cast hc).trans (havg (q i) _ _ (by
          have hp : (0 : ℝ) < ((2 : ℝ) ^ k)⁻¹ := by positivity
          linarith))
    _ = _ := by simp; ring

/-- A translated cell inherits the original family's linear count, including the coarse scales. -/
theorem translated_cell_count {δ A : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    {n : ℕ} (q : Fin n → Space) (hn : (n : ℝ) ≤ A / δ)
    (hcount : ∀ (q₀ : Space) (r : ℝ), δ ≤ r → r ≤ 1 →
      (Set.ncard {i | q i ∈ ball q₀ r} : ℝ) ≤ A * (r / δ))
    (k : ℕ) (l : Fin 3 → ℤ) (t : Space) (hδk : δ ≤ ((2 : ℝ) ^ k)⁻¹) :
    (Set.ncard {i | dyadicLabel k (q i + t) = l} : ℝ) ≤
      2 * A * (((2 : ℝ) ^ k)⁻¹ / δ) := by
  let r := 2 * ((2 : ℝ) ^ k)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have hδr : δ ≤ r := by dsimp [r]; linarith
  by_cases hr1 : r ≤ 1
  · have hc : Set.ncard {i | dyadicLabel k (q i + t) = l} ≤
        Set.ncard {i | q i ∈ ball (dyadicCorner k l - t) r} := by
      apply Set.ncard_mono
      intro i hi
      have hh := dyadic_cell_subset_ball hi
      change dist (q i) (dyadicCorner k l - t) < r
      change dist (q i + t) (dyadicCorner k l) < r at hh
      have he : dist (q i) (dyadicCorner k l - t) =
          dist (q i + t) (dyadicCorner k l) := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        module
      rwa [he]
    have hbound := hcount (dyadicCorner k l - t) r hδr hr1
    calc
      _ ≤ (Set.ncard {i | q i ∈ ball (dyadicCorner k l - t) r} : ℝ) := by exact_mod_cast hc
      _ ≤ A * (r / δ) := hbound
      _ = _ := by dsimp [r]; ring
  · have hc : Set.ncard {i : Fin n | dyadicLabel k (q i + t) = l} ≤ n := by
      simpa using Set.ncard_le_card ({i : Fin n | dyadicLabel k (q i + t) = l})
    calc
      _ ≤ (n : ℝ) := by exact_mod_cast hc
      _ ≤ A / δ := hn
      _ ≤ A * (r / δ) := by
        have h1 : 1 ≤ r := (not_le.mp hr1).le
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left h1 (div_nonneg hA hδ.le)
      _ = _ := by dsimp [r]; ring

end

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
