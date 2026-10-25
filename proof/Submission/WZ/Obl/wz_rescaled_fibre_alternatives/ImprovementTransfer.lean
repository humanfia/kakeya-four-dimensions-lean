-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.ImprovementTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.LocalEstimate

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

lemma selected_improvement_lower {d σ ω α θ a n M : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hσ : 0 ≤ σ) (hθα : θ ≤ α / 2)
    (ha : 0 ≤ a) (hn : 0 < n) (hM : 0 < M) (hMn : M ≤ n) (hcard : d ^ θ * n ≤ M) :
    a * d ^ (ω - α / 2) * (n * d ^ 2) * (n * d) ^ (-σ) ≤
      a * d ^ (ω - α) * (M * d ^ 2) * (M * d) ^ (-σ) := by
  have hp : d ^ (ω - α / 2) ≤ d ^ (ω - α + θ) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith)
  have hnp : (n * d) ^ (-σ) ≤ (M * d) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hM hd)
      (mul_le_mul_of_nonneg_right hMn hd.le) (neg_nonpos.mpr hσ)
  calc
    _ ≤ a * d ^ (ω - α + θ) * (n * d ^ 2) * (n * d) ^ (-σ) := by gcongr
    _ = a * d ^ (ω - α) * ((d ^ θ * n) * d ^ 2) * (n * d) ^ (-σ) := by
      rw [Real.rpow_add hd]
      ring
    _ ≤ a * d ^ (ω - α) * (M * d ^ 2) * (n * d) ^ (-σ) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hnp (by positivity)

noncomputable def improvementConstant (κ ω α σ : ℝ) : ℝ :=
  κ * (4 * contraction) ^ (ω - α / 2) * (16 / contraction) * (4 * contraction) ^ (-σ)

lemma improvementConstant_pos {κ ω α σ : ℝ} (hκ : 0 < κ) :
    0 < improvementConstant κ ω α σ := by unfold improvementConstant; positivity

lemma local_improvement_of_normalized {σ ω α θ κ r s : ℝ}
    (hσ : 0 ≤ σ) (hθα : θ ≤ α / 2) (hκ : 0 < κ)
    (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r)
    (e : Space ≃ₗᵢ[ℝ] Space) (y w : Space)
    {n M : ℕ} (hn : 0 < n) (hM : 0 < M)
    (j : Fin M → Fin n) (hj : Function.Injective j) (Y : Fin n → Set Space)
    (hcard : (normalizedRadius r s) ^ θ * n ≤ M)
    (hQ : ENNReal.ofReal (κ * (normalizedRadius r s) ^ (ω - α) *
      (M * (normalizedRadius r s) ^ 2) * (M * normalizedRadius r s) ^ (-σ)) ≤
      volume (⋃ i, normalize e y w r hr '' Y (j i))) :
    ENNReal.ofReal (improvementConstant κ ω α σ * (s / r) ^ (ω - α / 2) *
      (n * s ^ 2) * (n * (s / r)) ^ (-σ)) ≤ volume (⋃ i, Y i) := by
  have hd := normalizedRadius_pos hr hs
  have hd1 : normalizedRadius r s ≤ 1 := (normalizedRadius_le hr hsr).trans (by norm_num)
  have hMn : (M : ℝ) ≤ n := by exact_mod_cast (show M ≤ n by simpa using Fintype.card_le_of_injective j hj)
  have hh := selected_improvement_lower (ω := ω) hd hd1 hσ hθα hκ.le
    (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hM) hMn hcard
  have hnorm := (ENNReal.ofReal_le_ofReal hh).trans hQ
  rw [normalized_volume_identity hr hs (Nat.cast_nonneg n) κ (ω - α / 2) σ] at hnorm
  apply WangZahlLot.Obl.wz_nonflat_factored_improvement.ofReal_cancel_factor (by positivity : 0 < jacobian r)
  apply hnorm.trans
  calc
    _ = volume (normalize e y w r hr '' (⋃ i, Y (j i))) := by rw [Set.image_iUnion]
    _ = ENNReal.ofReal (jacobian r) * volume (⋃ i, Y (j i)) := normalize_volume e y w hr _
    _ ≤ ENNReal.ofReal (jacobian r) * volume (⋃ i, Y i) :=
      mul_le_mul_right (measure_mono (iUnion_subset fun i => subset_iUnion Y (j i))) _

end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
