-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.PowerDepth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Dyadic
import Submission.WZ.Obl.wz_measurable_angular_selection

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

/-- A logarithmic number of dyadic scales is absorbed by any prescribed positive
power, while reaching an arbitrary fixed polynomial lower scale. -/
lemma dyadic_depth_with_power_budget (N p C : ℝ) (hN : 0 ≤ N)
    (hp : 0 < p) (hC : 0 < C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ K : ℕ, (1 / 2 : ℝ) ^ K ≤ δ ^ N ∧
        C * ((K : ℝ) + 1) * δ ^ p ≤ 1 := by
  let β : ℝ := p / (2 * (N + 1))
  have hβ : 0 < β := by dsimp [β]; positivity
  let z₀ : ℝ := min 1 (1 / C)
  have hz₀ : 0 < z₀ := lt_min (by norm_num) (by positivity)
  let δ₀ : ℝ := min (1 / 100) (min (Real.exp (-(4 / β ^ 2))) (z₀ ^ (p / 2)⁻¹))
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  refine ⟨δ₀, hδ₀, min_le_left _ _, ?_⟩
  intro δ hδ hδsmall
  have hδ100 : δ ≤ 1 / 100 := hδsmall.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := by linarith
  have hδexp : δ ≤ Real.exp (-(4 / β ^ 2)) :=
    hδsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδroot : δ ≤ z₀ ^ (p / 2)⁻¹ :=
    hδsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have ha : 0 < δ ^ (N + 1) := Real.rpow_pos_of_pos hδ _
  have ha1 : δ ^ (N + 1) ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by linarith)
  obtain ⟨K, hKlo, hKhi⟩ := exists_dyadic_bottom ha ha1
  have haδ : δ ^ (N + 1) ≤ δ :=
    Real.rpow_le_self_of_le_one hδ.le hδ1 (by linarith)
  have hlog := WangZahlLot.Obl.wz_measurable_angular_selection.log_count_bound
    hβ ha (haδ.trans hδexp) hKlo
  rw [← Real.rpow_mul hδ.le] at hlog
  have he : (N + 1) * β = p / 2 := by dsimp [β]; field_simp
  rw [he] at hlog
  have hsmall : δ ^ (p / 2) ≤ 1 / C := by
    have h := (Real.le_rpow_inv_iff_of_pos hδ.le hz₀.le (show 0 < p / 2 by positivity)).mp hδroot
    exact h.trans (min_le_right _ _)
  have hCsmall : C * δ ^ (p / 2) ≤ 1 := by
    have h := (le_div_iff₀ hC).mp hsmall
    nlinarith
  refine ⟨K, ?_, ?_⟩
  · apply hKhi.le.trans
    rw [Real.rpow_add hδ, Real.rpow_one]
    have hδhalf : 2 * δ ≤ 1 := by linarith
    nlinarith [Real.rpow_nonneg hδ.le N]
  · calc C * ((K : ℝ) + 1) * δ ^ p =
        (C * δ ^ (p / 2)) * (((K : ℝ) + 1) * δ ^ (p / 2)) := by
          have hpow : δ ^ p = δ ^ (p / 2) * δ ^ (p / 2) := by
            rw [← Real.rpow_add hδ]
            congr 1
            ring
          rw [hpow]
          ring
      _ ≤ 1 * 1 := mul_le_mul hCsmall hlog (by positivity) (by norm_num)
      _ = 1 := one_mul 1

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
