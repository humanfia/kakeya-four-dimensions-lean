-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_rescaled_fibre_alternatives.CoverParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.PowerLoss
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ReverseConvex
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ReverseSlabs

namespace WangZahlLot.Obl.wz_rescaled_fibre_alternatives

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

def coverError : ℝ := max 1 (max coarseConvexLoss (max localSlabLoss 112000000))
lemma coverError_pos : 0 < coverError := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
lemma coarseLoss_le_coverError : coarseConvexLoss ≤ coverError :=
  (le_max_left _ _).trans (le_max_right _ _)
lemma localLoss_le_coverError : localSlabLoss ≤ coverError :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
lemma parentLoss_le_coverError : (112000000 : ℝ) ≤ coverError :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

lemma cover_parameters {ζ ω : ℝ} (hζ : 0 < ζ) (hω : 0 < ω) :
    ∃ (q : ℕ) (c : ℝ), 0 < q ∧ 4 < (ζ / 100) * q ∧ 0 < c ∧ c ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ c →
        4 * contraction * δ ≤ contraction ^ 2 ∧
        (4 * contraction * δ) ^ (ζ / 100) * (q : ℝ) ≤ 1 ∧
        (4 * contraction * δ) ^ (ω / 100) ≤ 1 / (100 * coverScale) ∧
        δ ^ ζ ≤ (4 * contraction * δ) ^ (3 * (ζ / 100)) ∧
        coverError * (4 * contraction * δ) ^ (-(6 * (ζ / 100))) ≤ δ ^ (-ζ) := by
  let τ := ζ / 100
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨q, hq⟩ := exists_nat_gt (max (4 / τ) 0)
  have hqpos : 0 < q := by exact_mod_cast (lt_of_le_of_lt (le_max_right _ _) hq)
  have hτq : 4 < τ * q := by
    have hh := (div_lt_iff₀ hτ).mp ((le_max_left _ _).trans_lt hq)
    linarith
  obtain ⟨c₁, hc₁, h₁⟩ := WangZahlLot.Obl.wz_nonflat_factored_improvement.exists_small_rpow
    hτ (show 0 < (q : ℝ)⁻¹ by positivity)
  obtain ⟨c₂, hc₂, h₂⟩ := WangZahlLot.Obl.wz_nonflat_factored_improvement.exists_small_rpow
    (show 0 < ω / 100 by positivity) (show 0 < 1 / (100 * coverScale) by have := coverScale_pos; positivity)
  let G := coverError * (4 * contraction) ^ (-(6 * τ))
  have hG : 0 < G := by dsimp [G]; exact mul_pos coverError_pos (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨c₃, hc₃, h₃⟩ := WangZahlLot.Obl.wz_nonflat_factored_improvement.exists_small_rpow
    (show 0 < ζ / 2 by positivity)
    (show 0 < min ((4 * contraction) ^ (3 * τ)) G⁻¹ from
      lt_min (Real.rpow_pos_of_pos (by norm_num) _) (inv_pos.mpr hG))
  let c := min (1 / 100) (min (contraction / 4) (min c₁ (min c₂ c₃)))
  have hc : 0 < c := lt_min (by norm_num) (lt_min (by norm_num) (lt_min hc₁ (lt_min hc₂ hc₃)))
  refine ⟨q, c, hqpos, hτq, hc, min_le_left _ _, ?_⟩
  intro δ hδ hδc
  have hδ1 : δ ≤ 1 := (hδc.trans (min_le_left _ _)).trans (by norm_num)
  have hδc' : δ ≤ min (contraction / 4) (min c₁ (min c₂ c₃)) := hδc.trans (min_le_right _ _)
  have hδκ := hδc'.trans (min_le_left _ _)
  have hδc'' := hδc'.trans (min_le_right _ _)
  have hδc₁ := hδc''.trans (min_le_left _ _)
  have hδc₂ := hδc''.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδc₃ := hδc''.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdδ : 4 * contraction * δ ≤ δ := by norm_num [contraction]; linarith
  have hd : 0 < 4 * contraction * δ := by positivity
  have hc₃' := h₃ δ hδ hδc₃
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [contraction] at hδκ ⊢
    linarith only [hδκ]
  · have hh := (Real.rpow_le_rpow hd.le hdδ hτ.le).trans (h₁ δ hδ hδc₁)
    have hh' := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg q)
    simpa only [inv_mul_cancel₀ (show (q : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hqpos.ne')] using hh'
  · exact (Real.rpow_le_rpow hd.le hdδ (by positivity)).trans (h₂ δ hδ hδc₂)
  · calc
      δ ^ ζ ≤ δ ^ (ζ / 2 + 3 * τ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by dsimp [τ]; linarith)
      _ = δ ^ (ζ / 2) * δ ^ (3 * τ) := Real.rpow_add hδ _ _
      _ ≤ (4 * contraction) ^ (3 * τ) * δ ^ (3 * τ) :=
        mul_le_mul_of_nonneg_right (hc₃'.trans (min_le_left _ _)) (by positivity)
      _ = _ := (Real.mul_rpow (by norm_num) hδ.le).symm
  · have hh := count_power_absorption hδ hδ1 (by dsimp [τ]; linarith : 6 * τ ≤ ζ / 2)
      hG (hc₃'.trans (min_le_right _ _))
    rw [Real.mul_rpow (by norm_num : 0 ≤ 4 * contraction) hδ.le]
    simpa only [G, mul_assoc] using hh

lemma parent_error_bound {d δ τ η : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hdδ : d ≤ δ)
    (hη : 0 ≤ η) (hητ : η ≤ τ) :
    2000000 * (d ^ (-τ) * δ ^ (-η) / (d ^ (4 * τ) / 56)) ≤
      112000000 * d ^ (-(6 * τ)) := by
  have hpow : δ ^ (-η) ≤ d ^ (-τ) :=
    (Real.rpow_le_rpow_of_nonpos hd hdδ (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_ge hd hd1 (by linarith))
  calc
    _ ≤ 2000000 * (d ^ (-τ) * d ^ (-τ) / (d ^ (4 * τ) / 56)) := by gcongr
    _ = _ := by
      rw [div_div_eq_mul_div, div_eq_mul_inv, ← Real.rpow_neg hd.le]
      have he : d ^ (-τ) * d ^ (-τ) * d ^ (-(4 * τ)) = d ^ (-(6 * τ)) := by
        rw [← Real.rpow_add hd, ← Real.rpow_add hd]
        congr 1
        ring
      calc
        _ = 112000000 * (d ^ (-τ) * d ^ (-τ) * d ^ (-(4 * τ))) := by ring
        _ = _ := by rw [he]

lemma physical_radius_range {r δ ρ ω : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hl : (4 * contraction * δ) ^ (1 - ω / 100) ≤ ρ)
    (hu : ρ ≤ (4 * contraction * δ) ^ (ω / 100)) :
    r * δ ^ (1 - ω / 100) ≤ coverScale * (coverScale * r * ρ) ∧
      coverScale * r * ρ ≤ coverScale * (r * δ ^ (ω / 100)) := by
  have hscale := coverScale_pos
  have hscale1 : 1 ≤ coverScale := by norm_num [coverScale, contraction]
  have hl' : δ ^ (1 - ω / 100) ≤ coverScale * ρ := by
    have hc : 1 ≤ coverScale * (4 * contraction) ^ (1 - ω / 100) := by
      have hp : 4 * contraction ≤ (4 * contraction) ^ (1 - ω / 100) := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
          (by norm_num : 0 < 4 * contraction) (by norm_num) (by linarith : 1 - ω / 100 ≤ 1)
      have hh := mul_le_mul_of_nonneg_left hp hscale.le
      norm_num [coverScale, contraction] at hh ⊢
      linarith
    calc
      _ ≤ (coverScale * (4 * contraction) ^ (1 - ω / 100)) * δ ^ (1 - ω / 100) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ δ ^ (1 - ω / 100))
      _ = coverScale * (4 * contraction * δ) ^ (1 - ω / 100) := by
        rw [Real.mul_rpow (by norm_num) hδ.le, mul_assoc]
      _ ≤ coverScale * ρ := mul_le_mul_of_nonneg_left hl hscale.le
  constructor
  · have hρ : 0 < ρ := (Real.rpow_pos_of_pos (by positivity) _).trans_le hl
    calc
      _ ≤ coverScale * r * ρ := by nlinarith only [mul_le_mul_of_nonneg_left hl' hr.le]
      _ ≤ _ := by nlinarith [mul_pos (mul_pos hscale hr) hρ]
  · have hδ' : 4 * contraction * δ ≤ δ := by norm_num [contraction]; linarith
    have hp := hu.trans (Real.rpow_le_rpow (by positivity) hδ' (by positivity : 0 ≤ ω / 100))
    have hh := mul_le_mul_of_nonneg_left hp (mul_pos hscale hr).le
    simpa only [mul_assoc] using hh

end
end WangZahlLot.Obl.wz_rescaled_fibre_alternatives
