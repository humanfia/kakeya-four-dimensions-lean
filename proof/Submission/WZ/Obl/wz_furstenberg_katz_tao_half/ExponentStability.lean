-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.ExponentStability.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Stability of the directional exponent

For radii at most two and a scale at most one half, changing the exponent
from `σ` to `s` costs at most `r ^ (-2 * |σ - s|)`. Unit vectors have diameter
two, so the same loss controls every directional cap, including larger caps.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

lemma cap_rpow_exponent_transfer {r ρ σ s η η' : ℝ}
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hρ : r ≤ ρ) (hρtwo : ρ ≤ 2)
    (hη : η + 2 * |σ - s| ≤ η') :
    r ^ (-η) * (ρ / r) ^ σ ≤ r ^ (-η') * (ρ / r) ^ s := by
  have hrone : r ≤ 1 := by linarith
  have hratio : 1 ≤ ρ / r := (le_div_iff₀ hr).2 (by linarith)
  have hratiopos : 0 < ρ / r := lt_of_lt_of_le zero_lt_one hratio
  have hbase : ρ / r ≤ r ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hr.le, Real.rpow_two, inv_eq_one_div,
      le_div_iff₀ (sq_pos_of_pos hr)]
    calc ρ / r * r ^ 2 = ρ * r := by field_simp
      _ ≤ 1 := by nlinarith
  have hexp : (ρ / r) ^ σ ≤ (ρ / r) ^ (s + |σ - s|) :=
    Real.rpow_le_rpow_of_exponent_le hratio (by linarith [le_abs_self (σ - s)])
  have herror : (ρ / r) ^ |σ - s| ≤ (r ^ (-2 : ℝ)) ^ |σ - s| :=
    Real.rpow_le_rpow hratiopos.le hbase (abs_nonneg _)
  calc r ^ (-η) * (ρ / r) ^ σ
      ≤ r ^ (-η) * ((ρ / r) ^ s * (ρ / r) ^ |σ - s|) := by
        rw [← Real.rpow_add hratiopos]
        exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hr.le _)
    _ ≤ r ^ (-η) * ((ρ / r) ^ s * (r ^ (-2 : ℝ)) ^ |σ - s|) := by
        gcongr
    _ = r ^ (-η + (-2) * |σ - s|) * (ρ / r) ^ s := by
        rw [← Real.rpow_mul hr.le, Real.rpow_add hr]
        ring
    _ ≤ r ^ (-η') * (ρ / r) ^ s := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hratiopos.le _)
        exact Real.rpow_le_rpow_of_exponent_ge hr hrone (by linarith)

lemma unit_bush_exponent_transfer
    {E : Type*} [NormedAddCommGroup E] {D : Set (E × E)}
    {r σ s η η' : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hs : 0 ≤ s) (hη : η + 2 * |σ - s| ≤ η')
    (hunit : ∀ q ∈ D, ‖q.2‖ = 1) (p : E)
    (hcap : ∀ u : E, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤
        r ^ (-η) * (ρ / r) ^ σ) :
    ∀ u : E, ‖u‖ = 1 → ∀ ρ : ℝ, r ≤ ρ →
      ({e | (p, e) ∈ D ∧ dist e u ≤ ρ}.ncard : ℝ) ≤
        r ^ (-η') * (ρ / r) ^ s := by
  intro u hu ρ hρ
  by_cases hρtwo : ρ ≤ 2
  · exact (hcap u hu ρ hρ).trans (cap_rpow_exponent_transfer hr hrhalf hρ hρtwo hη)
  · have htwoρ : 2 ≤ ρ := le_of_not_ge hρtwo
    have hrtwo : r ≤ 2 := by linarith
    have hdist (e : E) (he : (p, e) ∈ D) : dist e u ≤ 2 := by
      calc dist e u = ‖e - u‖ := dist_eq_norm _ _
        _ ≤ ‖e‖ + ‖u‖ := norm_sub_le _ _
        _ = 2 := by rw [hunit (p, e) he, hu]; norm_num
    have hsets : {e | (p, e) ∈ D ∧ dist e u ≤ ρ} =
        {e | (p, e) ∈ D ∧ dist e u ≤ 2} := by
      ext e
      exact ⟨fun he => ⟨he.1, hdist e he.1⟩,
        fun he => ⟨he.1, he.2.trans htwoρ⟩⟩
    rw [hsets]
    calc ({e | (p, e) ∈ D ∧ dist e u ≤ 2}.ncard : ℝ)
        ≤ r ^ (-η) * (2 / r) ^ σ := hcap u hu 2 hrtwo
      _ ≤ r ^ (-η') * (2 / r) ^ s :=
        cap_rpow_exponent_transfer hr hrhalf hrtwo le_rfl hη
      _ ≤ r ^ (-η') * (ρ / r) ^ s := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr.le _)
        exact Real.rpow_le_rpow (by positivity)
          (div_le_div_of_nonneg_right htwoρ hr.le) hs

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
