-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.RegularShading.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularCells

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open MeasureTheory LeanEval.Analysis.WangZahlKakeya Set Metric
open scoped ENNReal Classical

/-- A dense shading of a bounded convex body has a half-mass subshading that
is regular at any prescribed finite collection of positive radii. -/
theorem convex_regular_subshading_finite {W Y : Set Space}
    (hW : Convex ℝ W) (hWm : MeasurableSet W) (hWt : TotallyBounded W)
    (hWfin : volume W ≠ ⊤) (hY : MeasurableSet Y) (hYW : Y ⊆ W)
    {lam : ℝ} (hlam : 0 ≤ lam) (hdense : ENNReal.ofReal lam * volume W ≤ volume Y)
    {k : ℕ} (hk : 0 < k) (r : Fin k → ℝ) (hr : ∀ j, 0 < r j) :
    ∃ Z : Set Space, MeasurableSet Z ∧ Z ⊆ Y ∧
      (1 / 2 : ℝ≥0∞) * volume Y ≤ volume Z ∧
      ∀ p ∈ Z, ∀ j, ENNReal.ofReal (lam / (16000 * k)) * volume (W ∩ ball p (r j)) ≤
        volume (Z ∩ ball p (r j)) := by
  classical
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  choose F hFW hsum hcover using
    fun j => convex_regular_cells hW hWm hWt (div_pos (hr j) (by norm_num : (0 : ℝ) < 4))
  let J := Σ j : Fin k, ↥(F j)
  let C : J → Set Space := fun j => W ∩ closedBall j.2 (2 * (r j.1 / 4))
  let Λ : ℝ≥0∞ := ENNReal.ofReal (lam / (250 * k))
  have hCm : ∀ j : J, MeasurableSet (C j) :=
    fun _ => hWm.inter measurableSet_closedBall
  have hsumC : ∑ j : J, volume (C j) ≤ (125 * k : ℝ≥0∞) * volume W := by
    calc
      _ = ∑ j : Fin k, ∑ q ∈ F j, volume (W ∩ closedBall q (2 * (r j / 4))) := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_coe_sort (F j) (fun q => volume (W ∩ closedBall q (2 * (r j / 4))))
      _ ≤ ∑ _j : Fin k, 125 * volume W := Finset.sum_le_sum fun j _ => hsum j
      _ = _ := by simp [mul_assoc, mul_comm]
  have hΛ : Λ * (125 * k : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal lam := by
    have heq : lam / (250 * (k : ℝ)) * (125 * k) = (1 / 2 : ℝ) * lam := by field_simp; ring
    calc
      _ = ENNReal.ofReal (lam / (250 * k) * (125 * k)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        simp [Λ, ENNReal.ofReal_mul]
      _ = ENNReal.ofReal ((1 / 2 : ℝ) * lam) := congrArg ENNReal.ofReal heq
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num [ENNReal.ofReal_div_of_pos]
  have hbudget : ∑ j : J, Λ * volume (C j) ≤ (1 / 2 : ℝ≥0∞) * volume Y := by
    calc
      _ = Λ * ∑ j : J, volume (C j) := (Finset.mul_sum _ _ _).symm
      _ ≤ Λ * ((125 * k : ℝ≥0∞) * volume W) := mul_le_mul_right hsumC _
      _ = (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal lam * volume W) := by rw [← mul_assoc, hΛ, mul_assoc]
      _ ≤ _ := mul_le_mul_right hdense _
  obtain ⟨Z, hZ, hZY, hmass, hreg⟩ := regular_subshading_half volume Finset.univ C
    (fun j => Λ * volume (C j)) (fun j _ => hCm j) Y hY
    (ne_top_of_le_ne_top hWfin (measure_mono hYW)) hbudget
  refine ⟨Z, hZ, hZY, hmass, ?_⟩
  intro p hp j
  obtain ⟨q, hq, hpC, hCB, hvol⟩ := hcover j p (hYW (hZY hp))
  let l : J := ⟨j, ⟨q, hq⟩⟩
  have hnon : (Z ∩ C l).Nonempty := ⟨p, hp, hpC⟩
  have hmassC : Λ * volume (C l) ≤ volume (Z ∩ C l) :=
    (hreg l (Finset.mem_univ _) |>.resolve_left hnon.ne_empty).le
  have heq : ENNReal.ofReal (lam / (16000 * k)) = Λ * ENNReal.ofReal (1 / 64 : ℝ) := by
    dsimp only [Λ]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc
    ENNReal.ofReal (lam / (16000 * k)) * volume (W ∩ ball p (r j)) =
        Λ * (ENNReal.ofReal (1 / 64 : ℝ) * volume (W ∩ ball p (4 * (r j / 4)))) := by
      rw [heq, mul_assoc, show 4 * (r j / 4) = r j by ring]
    _ ≤ Λ * volume (C l) := mul_le_mul_right hvol _
    _ ≤ volume (Z ∩ C l) := hmassC
    _ ≤ volume (Z ∩ ball p (r j)) := by
      apply measure_mono
      intro x hx
      refine ⟨hx.1, ?_⟩
      have hh := (hCB hx.2).2
      simpa only [show 4 * (r j / 4) = r j by ring] using hh


end WangZahlLot.Obl.wz_clustered_cover_volume_gain
