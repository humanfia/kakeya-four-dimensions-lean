-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.PowerBudgets.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SmallPowers

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

/-- A single scale cutoff absorbs a bounded constant whenever two exponents
are separated by a fixed positive margin. -/
lemma uniform_small_power_comparison {C gap : ℝ} (hC : 0 < C) (hgap : 0 < gap) :
    ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → δ ≤ d →
      ∀ c p q : ℝ, c ≤ C → q + gap ≤ p → c * δ ^ p ≤ δ ^ q := by
  obtain ⟨d, hd, H⟩ := constant_power_bound hC hgap
  refine ⟨d, hd, ?_⟩
  intro δ hδ hδ1 hδd c p q hc hp
  calc
    _ ≤ δ ^ (-gap) * δ ^ p :=
      mul_le_mul_of_nonneg_right (hc.trans (H δ hδ hδd)) (Real.rpow_nonneg hδ.le _)
    _ = δ ^ (-gap + p) := (Real.rpow_add hδ _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)

lemma square_rpow {δ : ℝ} (hδ : 0 < δ) (p : ℝ) : (δ ^ (2 : ℕ)) ^ p = δ ^ (2 * p) := by
  rw [← Real.rpow_ofNat δ 2, ← Real.rpow_mul hδ.le]

lemma power_count_bound {δ h : ℝ} {n : ℕ} (hδ : 0 < δ)
    (hn : (n : ℝ) * δ ^ 2 ≤ 8 * δ ^ (-h)) :
    (n : ℝ) ≤ 8 * δ ^ (-(h + 2)) := by
  have hh := (le_div_iff₀ (sq_pos_of_pos hδ)).mpr hn
  apply hh.trans_eq
  rw [div_eq_mul_inv, ← Real.rpow_ofNat δ 2, ← Real.rpow_neg hδ.le, mul_assoc,
    ← Real.rpow_add hδ]
  congr 2
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
