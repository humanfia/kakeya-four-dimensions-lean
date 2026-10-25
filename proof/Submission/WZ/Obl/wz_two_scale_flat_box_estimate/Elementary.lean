-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Elementary.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement (profile profile_eq)

lemma admissible_mono_density {δ η η' m l : ℝ} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : η ≤ η')
    (h : Admissible δ η m l n x v Y) : Admissible δ η' m l n x v Y := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2⟩
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) h.2.2.2.1
  have hh := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη
  gcongr

lemma diagonal_profile {σ ω ε κ δ η n : ℝ}
    (hδ : 0 < δ) (hn : 0 < n) :
    profile σ ω ε κ δ (δ ^ (-η)) (δ ^ (-η)) n =
      κ * δ ^ (ω + ε + η * (1 - σ / 2)) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
  rw [profile_eq hδ (Real.rpow_pos_of_pos hδ _) (Real.rpow_pos_of_pos hδ _) hn]
  simp only [← Real.rpow_mul hδ.le]
  rw [show ω + ε + η * (1 - σ / 2) =
    ω + ε + (-η) * (-1 + 3 / 2 * σ) + (-η) * (-σ) by ring,
    Real.rpow_add hδ, Real.rpow_add hδ, Real.mul_rpow hn.le hδ.le,
    show (1 : ℝ) - σ = 1 + -σ by ring, Real.rpow_add hn, Real.rpow_one]
  rw [show ω + ε + 2 - σ = ω + ε + 2 + -σ by ring,
    Real.rpow_add hδ, Real.rpow_add hδ, Real.rpow_two]
  ring

/-- E controls the requested profile whenever its aspect-ratio factor fits in
an arbitrarily small power of the fine scale. -/
theorem near_round_from_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hE : Estimate σ ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ κ η : ℝ, 0 < κ ∧ 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      ∀ a b : ℝ, (b / a) ^ ω ≤ δ ^ (-(ε / 2)) →
        ENNReal.ofReal (bound σ ω ε κ δ a b n) ≤ volume (⋃ i, Y i) := by
  obtain ⟨κ, hκ, ηE, hηE, H⟩ := hE (ε / 4) (by positivity)
  let η := min ηE (ε / 4)
  have hη : 0 < η := lt_min hηE (by positivity)
  refine ⟨κ, η, hκ, hη, ?_⟩
  intro δ hδ hδ100 n x v Y hAdm a b hratio
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hm : 1 ≤ δ ^ (-η) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hn : (0 : ℝ) < n := by exact_mod_cast hAdm.1
  have hInput := admissible_mono_density hδ hδ1 (min_le_left ηE (ε / 4)) hAdm
  have hh := H δ hδ hδ100 _ _ hm hm n x v Y hInput
  rw [diagonal_profile hδ hn] at hh
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hh
  have hηε : η ≤ ε / 4 := min_le_right _ _
  have hbudget : ω + ε / 4 + η * (1 - σ / 2) ≤ ω + ε - ε / 2 := by
    nlinarith [mul_nonneg hη.le hσ]
  have hp := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hbudget
  unfold bound
  calc
    _ ≤ κ * δ ^ (ω + ε) * δ ^ (-(ε / 2)) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
      gcongr
    _ = κ * δ ^ (ω + ε - ε / 2) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
      rw [mul_assoc κ, ← Real.rpow_add hδ]
      congr 3
    _ ≤ _ := by gcongr

/-- On any interval bounded away from zero, the aspect ratio is a fixed
constant loss, since the short width is at least delta and the long width at most eight. -/
theorem large_scale_from_estimate {σ ω : ℝ} (hσ : 0 ≤ σ) (hω : 0 ≤ ω)
    (hE : Estimate σ ω) {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) :
    ∃ κ η : ℝ, 0 < κ ∧ 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → d ≤ δ →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Admissible δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
      ∀ a b : ℝ, δ ≤ a → 0 ≤ b → b ≤ 8 →
        ENNReal.ofReal (bound σ ω ε κ δ a b n) ≤ volume (⋃ i, Y i) := by
  obtain ⟨κ, η, hκ, hη, H⟩ := near_round_from_estimate hσ hE hε
  let C := (8 / d) ^ ω
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨κ / C, η, div_pos hκ hC, hη, ?_⟩
  intro δ hδ hδ100 hdδ n x v Y hAdm a b hδa hb hb8
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hratio0 : (1 / (1 : ℝ)) ^ ω ≤ δ ^ (-(ε / 2)) := by
    simp only [div_self one_ne_zero, Real.one_rpow]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hh := H δ hδ hδ100 n x v Y hAdm 1 1 hratio0
  have ha : 0 < a := hδ.trans_le hδa
  have hratio : (b / a) ^ ω ≤ C := by
    apply Real.rpow_le_rpow (div_nonneg hb ha.le) _ hω
    exact div_le_div₀ (by norm_num : (0 : ℝ) ≤ 8) hb8 hd (hdδ.trans hδa)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hh
  unfold bound
  simp only [div_self one_ne_zero, Real.one_rpow, mul_one]
  calc
    _ ≤ κ / C * δ ^ (ω + ε) * C * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
      gcongr
    _ = _ := by field_simp

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
