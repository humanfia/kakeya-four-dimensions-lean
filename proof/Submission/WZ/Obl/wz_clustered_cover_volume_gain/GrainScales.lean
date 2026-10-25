-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GrainScales.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

noncomputable def grainAngle (δ ε ρ c : ℝ) : ℝ := min 1 (δ ^ (1 - ε) / (ρ * c))

lemma grainAngle_properties {δ ε ρ c : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) (hρc : 0 < ρ * c) (hρc1 : ρ * c ≤ 1) :
    0 < grainAngle δ ε ρ c ∧ grainAngle δ ε ρ c ≤ 1 ∧
    δ ≤ grainAngle δ ε ρ c ∧
    grainAngle δ ε ρ c * ρ * c ≤ δ ^ (1 - ε) ∧
    (grainAngle δ ε ρ c ≠ 1 → grainAngle δ ε ρ c * ρ * c = δ ^ (1 - ε)) := by
  have hT : 0 < δ ^ (1 - ε) := Real.rpow_pos_of_pos hδ _
  have hδT : δ ≤ δ ^ (1 - ε) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show 1 - ε ≤ 1 by linarith)
  have hδratio : δ ≤ δ ^ (1 - ε) / (ρ * c) := by
    apply (le_div_iff₀ hρc).mpr
    exact (mul_le_mul_of_nonneg_left hρc1 hδ.le).trans (by simpa using hδT)
  refine ⟨lt_min zero_lt_one (div_pos hT hρc), min_le_left _ _, le_min hδ1 hδratio, ?_, ?_⟩
  · have hh := min_le_right (1 : ℝ) (δ ^ (1 - ε) / (ρ * c))
    simpa only [grainAngle, mul_assoc] using (le_div_iff₀ hρc).mp hh
  · intro hne
    have he : grainAngle δ ε ρ c = δ ^ (1 - ε) / (ρ * c) := by
      apply min_eq_right
      by_contra h
      have hh : grainAngle δ ε ρ c = 1 := min_eq_left (le_of_not_ge h)
      exact hne hh
    rw [he, mul_assoc, div_mul_cancel₀ _ hρc.ne']

lemma grainAngle_contains_short {δ ε ρ c a : ℝ} (hρc : 0 < ρ * c)
    (hac : a ≤ ρ * c) (haT : a ≤ δ ^ (1 - ε)) :
    a ≤ grainAngle δ ε ρ c * ρ * c := by
  by_cases h : 1 ≤ δ ^ (1 - ε) / (ρ * c)
  · rw [grainAngle, min_eq_left h, one_mul]
    exact hac
  · rw [grainAngle, min_eq_right (le_of_not_ge h)]
    have he : δ ^ (1 - ε) / (ρ * c) * ρ * c = δ ^ (1 - ε) := by
      rw [mul_assoc, div_mul_cancel₀ _ hρc.ne']
    rwa [he]

lemma grainAngle_error_bound {δ ε ρ c a : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hε : 0 ≤ ε) (hρc : 0 < ρ * c) (hρc1 : ρ * c ≤ 1) (hδa : δ ≤ a) :
    grainAngle δ ε ρ c * ρ * c ≤ δ ^ (-ε) * a := by
  calc
    _ ≤ δ ^ (1 - ε) := (grainAngle_properties hδ hδ1 hε hρc hρc1).2.2.2.1
    _ = δ ^ (-ε) * δ := by
      rw [show 1 - ε = -ε + 1 by ring, Real.rpow_add hδ, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hδa (Real.rpow_nonneg hδ.le _)

lemma grain_error_ceiling {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) :
    1 ≤ ⌈δ ^ (-ε)⌉₊ ∧ (⌈δ ^ (-ε)⌉₊ : ℝ) ≤ 2 * δ ^ (-ε) ∧
      δ ^ (-ε) ≤ (⌈δ ^ (-ε)⌉₊ : ℝ) := by
  have hpow : 1 ≤ δ ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hceil := Nat.le_ceil (δ ^ (-ε))
  have hupper := Nat.ceil_lt_add_one (Real.rpow_nonneg hδ.le (-ε))
  exact ⟨by exact_mod_cast hpow.trans hceil, by linarith, hceil⟩

lemma grain_packet_weight_lower {a ρ θ s c A : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hθ : 0 < θ) (hs : 0 < s) (hc : 0 < c) (hA : 0 < A)
    (hconf : s * ρ * c ≤ A * a) :
    (1 / (800000000 * A)) * (ρ / θ) ^ 2 ≤ a * ρ / (800000000 * θ ^ 2 * s * c) := by
  rw [one_div, mul_comm (800000000 * A)⁻¹, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (show 0 < 800000000 * A by positivity)
    (show 0 < 800000000 * θ ^ 2 * s * c by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right hconf (show 0 ≤ 800000000 * ρ by positivity)
  convert hh using 1 <;> field_simp <;> ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
