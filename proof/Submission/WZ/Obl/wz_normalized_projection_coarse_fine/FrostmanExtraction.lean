-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.FrostmanExtraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.LaminarExtraction

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Finset

/-- A Frostman count of dimension at most one gives a subset satisfying linear cell quotas. -/
theorem laminar_frostman_extraction {α : Type*} [DecidableEq α]
    (U : Finset α) (F : Finset (Finset α)) (r : Finset α → ℝ)
    {δ K s : ℝ} (hδ : 0 < δ) (hK : 0 < K) (hs : s ≤ 1)
    (hmin : 1 ≤ K * δ ^ s * U.card)
    (hFU : ∀ C ∈ F, C ⊆ U)
    (hlam : ∀ C ∈ F, ∀ D ∈ F, C ⊆ D ∨ D ⊆ C ∨ Disjoint C D)
    (hr : ∀ C ∈ F, δ ≤ r C)
    (hcount : ∀ C ∈ F, (C.card : ℝ) ≤ K * r C ^ s * U.card) :
    ∃ Q ⊆ U, 1 / (2 * K * δ ^ s) ≤ (Q.card : ℝ) ∧
      ∀ C ∈ F, ((Q ∩ C).card : ℝ) ≤ r C / δ := by
  classical
  have hpow : 0 < δ ^ s := Real.rpow_pos_of_pos hδ _
  have hU : 0 < (U.card : ℝ) := by
    by_contra h
    have hz : (U.card : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [hz, mul_zero] at hmin
    norm_num at hmin
  let D := 2 * K * δ ^ s * (U.card : ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith
  have hw : ∀ a ∈ U, 0 ≤ 1 / D ∧ 1 / D ≤ 1 := by
    intro a ha
    exact ⟨by positivity, (div_le_one hD).mpr hD1⟩
  have hcap : ∀ C ∈ F, (∑ _a ∈ C, 1 / D) ≤ (⌊r C / δ⌋₊ : ℝ) := by
    intro C hC
    have hrpos : 0 < r C := hδ.trans_le (hr C hC)
    have hratio : 1 ≤ r C / δ := (one_le_div hδ).mpr (hr C hC)
    have hfloor : (1 : ℝ) ≤ ⌊r C / δ⌋₊ := by
      exact_mod_cast (Nat.one_le_floor_iff _).mpr hratio
    have hhalf : r C / δ / 2 ≤ (⌊r C / δ⌋₊ : ℝ) := by
      linarith [Nat.lt_floor_add_one (r C / δ)]
    have hgrowth : (r C / δ) ^ s ≤ r C / δ :=
      Real.rpow_le_self_of_one_le hratio hs
    calc
      (∑ _a ∈ C, 1 / D) = (C.card : ℝ) / D := by simp [div_eq_mul_inv]
      _ ≤ (K * r C ^ s * U.card) / D := div_le_div_of_nonneg_right (hcount C hC) hD.le
      _ = (r C / δ) ^ s / 2 := by
        rw [Real.div_rpow hrpos.le hδ.le]
        dsimp [D]
        field_simp
      _ ≤ r C / δ / 2 := by gcongr
      _ ≤ (⌊r C / δ⌋₊ : ℝ) := hhalf
  obtain ⟨Q, hQU, hmass, hQcap⟩ := laminar_weighted_extraction U F
    (fun C => ⌊r C / δ⌋₊) (fun _ => 1 / D) hFU hlam hw hcap
  refine ⟨Q, hQU, ?_, ?_⟩
  · calc
      1 / (2 * K * δ ^ s) = ∑ _a ∈ U, 1 / D := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        dsimp [D]
        field_simp
      _ ≤ Q.card := hmass
  · intro C hC
    calc
      ((Q ∩ C).card : ℝ) ≤ (⌊r C / δ⌋₊ : ℝ) := by exact_mod_cast hQcap C hC
      _ ≤ r C / δ := Nat.floor_le (div_nonneg (hδ.le.trans (hr C hC)) hδ.le)

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
