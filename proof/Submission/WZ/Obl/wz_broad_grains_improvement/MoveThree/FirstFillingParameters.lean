-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FirstFillingParameters.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FirstFillingParameters.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FirstFillingParameters.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic
import Submission.WZ.Obl.wz_horizontal_tube_exclusion.Vertical

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

/-- A power gap between the short and middle widths pays the lower angular
cutoff and all geometric size conditions in the first filling. -/
theorem first_filling_geometric_budget {δ r a b g s C : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (hb : b ≤ 4) (hC : 0 < C) (hflat : a ≤ C * δ ^ g * b)
    (hsmall : δ ^ s ≤ 1 / 16)
    (hgap : δ ^ (g - s) ≤ 1 / (112 * C)) :
    let θ := δ ^ s * b
    r ≤ 1 / 100 ∧ r + 5 * (a / 2) ≤ 1 / 100 ∧
      100 * (r + 5 * (a / 2)) ≤ 3 * b ∧
      32 * (r + 5 * (a / 2)) ≤ θ ∧ θ ≤ 1 ∧ θ ≤ 3 * b := by
  have ha : 0 < a := hr.trans_le hra
  have hbpos : 0 < b := ha.trans_le hab
  have hp : 0 < δ ^ s := Real.rpow_pos_of_pos hδ _
  have hgap' : 112 * C * δ ^ (g - s) ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 112 * C)).mp hgap
    nlinarith only [hh]
  have hpow : δ ^ g = δ ^ (g - s) * δ ^ s := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hcoef : 112 * C * δ ^ g ≤ δ ^ s := by
    rw [hpow]
    nlinarith only [mul_le_mul_of_nonneg_right hgap' hp.le]
  have hwide : 112 * a ≤ δ ^ s * b := by
    have hh := mul_le_mul_of_nonneg_right hcoef hbpos.le
    nlinarith only [mul_le_mul_of_nonneg_left hflat (by norm_num : (0 : ℝ) ≤ 112), hh]
  have hlower : 32 * (r + 5 * (a / 2)) ≤ δ ^ s * b := by linarith
  have hupper : δ ^ s * b ≤ b / 16 := by
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hbpos.le]
  dsimp only
  refine ⟨?_, ?_, ?_, hlower, ?_, ?_⟩ <;> linarith

/-- The broadness exponent must dominate the mass-loss exponent. -/
theorem first_filling_broad_budget {δ b β s t C H : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hβ : 0 ≤ β) (hC : 0 < C) (hH : 0 < H)
    (hgap : δ ^ (s * β - t) ≤ 1 / (8 * H * C)) :
    C * ((δ ^ s * b) / (3 * b)) ^ β ≤ (δ ^ t / H) / 8 := by
  have hratio : (δ ^ s * b) / (3 * b) ≤ δ ^ s := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * b)).mpr
    nlinarith [Real.rpow_pos_of_pos hδ s]
  have hnon : 0 ≤ (δ ^ s * b) / (3 * b) := by positivity
  have hprod : 8 * H * C * δ ^ (s * β - t) ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * H * C)).mp hgap
    nlinarith only [hh]
  have he : δ ^ (s * β) = δ ^ (s * β - t) * δ ^ t := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ ≤ C * (δ ^ s) ^ β := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hnon hratio hβ) hC.le
    _ = C * δ ^ (s * β) := by rw [← Real.rpow_mul hδ.le]
    _ ≤ _ := by
      rw [he]
      have hh := mul_le_mul_of_nonneg_right hprod (Real.rpow_pos_of_pos hδ t).le
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
      apply (le_div_iff₀ hH).mpr
      nlinarith only [hh]

/-- A logarithmic loss in the short-tube radius is paid at the original scale,
using only that the short tubes are no thinner than that original scale. -/
theorem first_filling_density_budget {δ r b s t e H : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hb : 0 < b) (hH : 0 < H)
    (hgap : (3 * 10 ^ 13 : ℝ) * (1 + Real.log (1 / δ)) * δ ^ (e - s - 3 * t) ≤
      48 / (16000 ^ 2 * H ^ 3)) :
    δ ^ e * (10 ^ 13 * ((3 * b) / (δ ^ s * b)) * (1 + Real.log (1 / r))) ≤
      ((δ ^ t / H) / 16000) ^ 2 * (48 * (δ ^ t / H)) := by
  have hr : 0 < r := hδ.trans_le hδr
  have hp : 0 < δ ^ s := Real.rpow_pos_of_pos hδ _
  have hlog : 1 + Real.log (1 / r) ≤ 1 + Real.log (1 / δ) := by
    have hh := Real.log_le_log (by positivity : 0 < 1 / r)
      (one_div_le_one_div_of_le hδ hδr)
    linarith
  have hratio : (3 * b) / (δ ^ s * b) = 3 / δ ^ s := by field_simp
  have hpow : δ ^ (e - s) = δ ^ (e - s - 3 * t) * δ ^ (3 * t) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hpowt : δ ^ (3 * t) = (δ ^ t) ^ 3 := by
    rw [show 3 * t = t + t + t by ring, Real.rpow_add hδ, Real.rpow_add hδ]
    ring
  calc
    _ ≤ δ ^ e * (10 ^ 13 * ((3 * b) / (δ ^ s * b)) * (1 + Real.log (1 / δ))) := by
      gcongr
    _ = (3 * 10 ^ 13 : ℝ) * (1 + Real.log (1 / δ)) * δ ^ (e - s) := by
      rw [hratio, Real.rpow_sub hδ]
      ring
    _ = ((3 * 10 ^ 13 : ℝ) * (1 + Real.log (1 / δ)) * δ ^ (e - s - 3 * t)) *
        δ ^ (3 * t) := by rw [hpow]; ring
    _ ≤ (48 / (16000 ^ 2 * H ^ 3)) * δ ^ (3 * t) :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_pos_of_pos hδ _).le
    _ = _ := by rw [hpowt]; ring

/-- The density produced by the first filling is sufficient for the net
estimate when its exponent is strictly smaller than the net's density exponent. -/
theorem first_filling_net_density_budget {δ e η k : ℝ} (hδ : 0 < δ)
    (hgap : δ ^ (η - e) ≤ k / (6144 * 16000)) :
    6144 * δ ^ η ≤ δ ^ e * k / 16000 := by
  have he : δ ^ η = δ ^ (η - e) * δ ^ e := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right hgap (Real.rpow_pos_of_pos hδ e).le
  rw [he]
  nlinarith only [hh]

/-- One uniform cutoff pays the geometric, broadness, logarithmic and net
thresholds of the first filling. All exponent inequalities are explicit. -/
theorem first_filling_parameter_cutoff {g s β t e η C H K k : ℝ}
    (hs : 0 < s) (hgs : s < g) (hβ : 0 ≤ β) (hbt : t < s * β)
    (het : s + 3 * t < e) (heη : e < η)
    (hC : 0 < C) (hH : 0 < H) (hK : 0 < K) (hk : 0 < k) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ r a b : ℝ,
      δ ≤ r → r ≤ a → a ≤ b → b ≤ 4 → a ≤ K * δ ^ g * b →
      let θ := δ ^ s * b
      let lam := δ ^ t / H
      r ≤ 1 / 100 ∧ r + 5 * (a / 2) ≤ 1 / 100 ∧
      100 * (r + 5 * (a / 2)) ≤ 3 * b ∧
      32 * (r + 5 * (a / 2)) ≤ θ ∧ θ ≤ 1 ∧ θ ≤ 3 * b ∧
      C * (θ / (3 * b)) ^ β ≤ lam / 8 ∧
      δ ^ e * (10 ^ 13 * ((3 * b) / θ) * (1 + Real.log (1 / r))) ≤
        (lam / 16000) ^ 2 * (48 * lam) ∧
      6144 * δ ^ η ≤ δ ^ e * k / 16000 := by
  obtain ⟨d₁, hd₁, H₁⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    hs (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨d₂, hd₂, H₂⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (sub_pos.mpr hgs) (by positivity : 0 < 1 / (112 * K))
  obtain ⟨d₃, hd₃, H₃⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (sub_pos.mpr hbt) (by positivity : 0 < 1 / (8 * H * C))
  obtain ⟨d₄, hd₄, H₄⟩ := WangZahlLot.Obl.wz_horizontal_tube_exclusion.exists_log_power_cutoff
    (3 * 10 ^ 13 : ℝ) (by positivity : 0 < 48 / (16000 ^ 2 * H ^ 3))
    (by linarith : 0 < e - s - 3 * t)
  obtain ⟨d₅, hd₅, H₅⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    (sub_pos.mpr heη) (by positivity : 0 < k / (6144 * 16000))
  refine ⟨min (1 / 100) (min d₁ (min d₂ (min d₃ (min d₄ d₅)))), by positivity,
    min_le_left _ _, ?_⟩
  intro δ hδ hδd r a b hδr hra hab hb hflat
  have hrest := hδd.trans (min_le_right _ _)
  have h₁ := H₁ δ hδ (hrest.trans (min_le_left _ _))
  have hrest := hrest.trans (min_le_right _ _)
  have h₂ := H₂ δ hδ (hrest.trans (min_le_left _ _))
  have hrest := hrest.trans (min_le_right _ _)
  have h₃ := H₃ δ hδ (hrest.trans (min_le_left _ _))
  have hrest := hrest.trans (min_le_right _ _)
  have h₄ := H₄ δ hδ (hrest.trans (min_le_left _ _))
  have h₅ := H₅ δ hδ (hrest.trans (min_le_right _ _))
  obtain ⟨hr1, hslab, hfl, hθ, hθ1, hθb⟩ := first_filling_geometric_budget
    hδ (hδ.trans_le hδr) hra hab hb hK hflat h₁ h₂
  exact ⟨hr1, hslab, hfl, hθ, hθ1, hθb,
    first_filling_broad_budget hδ ((hδ.trans_le hδr).trans_le (hra.trans hab)) hβ hC hH h₃,
    first_filling_density_budget hδ hδr ((hδ.trans_le hδr).trans_le (hra.trans hab)) hH h₄,
    first_filling_net_density_budget hδ h₅⟩

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
