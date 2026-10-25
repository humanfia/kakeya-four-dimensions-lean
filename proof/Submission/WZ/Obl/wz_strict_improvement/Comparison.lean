-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_strict_improvement.Comparison.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_strict_improvement.Slab

namespace WangZahlLot.Obl.wz_strict_improvement

open MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

/-- The lower cardinality bound absorbs an increase in `σ` into a small exponent margin. -/
theorem dLower_mono_sigma {σ₁ σ₂ ω a ε₁ ε₂ δ η : ℝ} {n : ℕ}
    (hσ : σ₁ ≤ σ₂) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hn : 0 < n)
    (hcard : δ ^ η ≤ 8 * ((n : ℝ) * δ))
    (hε : ε₁ + η * (σ₂ - σ₁) ≤ ε₂) :
    DLower σ₂ ω (a * (8 : ℝ) ^ (-(σ₂ - σ₁))) ε₂ δ n ≤
      DLower σ₁ ω a ε₁ δ n := by
  let t := σ₂ - σ₁
  have ht : 0 ≤ t := sub_nonneg.mpr hσ
  have hs : 0 < (n : ℝ) * δ := mul_pos (Nat.cast_pos.mpr hn) hδ
  have hpow := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hδ η) hcard
    (neg_nonpos.mpr ht)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hs.le,
    ← Real.rpow_mul hδ.le] at hpow
  have hsplit : ((n : ℝ) * δ) ^ (-σ₂) =
      ((n : ℝ) * δ) ^ (-σ₁) * ((n : ℝ) * δ) ^ (-t) := by
    rw [← Real.rpow_add hs]
    congr 1
    dsimp [t]
    ring
  unfold DLower
  rw [hsplit]
  calc
    a * (8 : ℝ) ^ (-t) * δ ^ (ω + ε₂) * ((n : ℝ) * δ ^ 2) *
        (((n : ℝ) * δ) ^ (-σ₁) * ((n : ℝ) * δ) ^ (-t)) =
      (a * δ ^ (ω + ε₂) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-σ₁)) *
        ((8 : ℝ) ^ (-t) * ((n : ℝ) * δ) ^ (-t)) := by ring
    _ ≤ (a * δ ^ (ω + ε₂) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-σ₁)) *
        δ ^ (η * -t) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = a * δ ^ (ω + ε₂ + η * -t) * ((n : ℝ) * δ ^ 2) *
        ((n : ℝ) * δ) ^ (-σ₁) := by
          rw [Real.rpow_add hδ (ω + ε₂) (η * -t)]
          ring
    _ ≤ a * δ ^ (ω + ε₁) * ((n : ℝ) * δ ^ 2) * ((n : ℝ) * δ) ^ (-σ₁) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs.le _)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ ha
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ₁
      dsimp [t]
      linarith

/-- The slab condition makes the estimate monotone in its multiplicity exponent. -/
theorem d_mono_sigma {σ₁ σ₂ ω : ℝ} (hσ : σ₁ ≤ σ₂) (hD : D σ₁ ω) : D σ₂ ω := by
  intro ε hε
  obtain ⟨a, ha, η₀, hη₀, h⟩ := hD (ε / 2) (by positivity)
  let t := σ₂ - σ₁
  have ht : 0 ≤ t := sub_nonneg.mpr hσ
  let η := min η₀ (ε / (2 * (t + 1)))
  have hη : 0 < η := lt_min hη₀ (by positivity)
  have hη₀' : η ≤ η₀ := min_le_left _ _
  have hηε : η * t ≤ ε / 2 := by
    have hsmall : η ≤ ε / (2 * (t + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (t + 1))).mp hsmall
    nlinarith
  refine ⟨a * (8 : ℝ) ^ (-t), by positivity, η, hη, ?_⟩
  intro δ hδ hδmax n x v Y hn hv hball hdistinct hmeas hsub hdense hK hF
  have hδ₁ : δ ≤ 1 := le_trans hδmax (by norm_num)
  have hm : δ ^ (-η) ≤ δ ^ (-η₀) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ₁ (neg_le_neg hη₀')
  have hbound := h δ hδ hδmax n x v Y hn hv hball hdistinct hmeas hsub
    (dense_mono hδ hδ₁ hη₀' hdense) (katzTao_mono hm hK) (frostmanSlab_mono hm hF)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
  exact dLower_mono_sigma hσ ha.le hδ hδ₁ hn
    (frostman_cardinality_lower hδ hn hv hball hF) (by linarith)

/-- A zero-error-exponent estimate at any smaller `σ` gives the full requested gain. -/
theorem strict_improvement_of_zero_exponent {σ₀ σ ω : ℝ} (hσ : σ₀ ≤ σ)
    (hω : 0 < ω) (hD : D σ₀ 0) :
    ∃ g : ℝ, 0 < g ∧ g ≤ ω ∧ D σ (ω - g) := by
  refine ⟨ω, hω, le_rfl, ?_⟩
  simpa only [sub_self] using d_mono_sigma hσ hD

end WangZahlLot.Obl.wz_strict_improvement
