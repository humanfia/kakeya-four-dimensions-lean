-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FilledNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FilledNormalization.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FilledNormalization.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.AdaptedFrame

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm inner_boxAxis norm_le_coord_sum)

/-- The adapted intermediate boxes become round after normalizing the flat
containing prism. Both transverse widths are at most a constant times delta/a. -/
theorem filled_prism_normalized_tube {δ a b r : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 3) (hr : 5 * (a / 2) ≤ r)
    (z v : V) (hv : ‖v‖ = 1) (e g : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hf : ∀ q i, f.linear q i = (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * e q i)
    (hv₀ : |e v 0| ≤ 4 * a) (hv₁ : |e v 1| ≤ 4 * b)
    (hg₂ : ∀ p, g p 2 = inner ℝ v p)
    (hg₀ : ∀ w, |g w 0| ≤ 2 * (|inner ℝ (boxAxis e 0) w| +
      |inner ℝ (boxAxis e 0) v| * ‖w‖)) :
    f '' P (10 * δ) (6 * b * δ / r) 2 z g ⊆
      T (64 * δ / a) (f z - f.linear v) ((2 : ℝ) • f.linear v) ∧ ‖(2 : ℝ) • f.linear v‖ ≤ 20 := by
  have hbpos : 0 < b := ha.trans_le hab
  have hrpos : 0 < r := by linarith
  have hgaxis : boxAxis g 2 = v := adapted_long_axis hv g hg₂
  have hspos (i : Fin 3) : 0 ≤ (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i := by
    fin_cases i <;> simp <;> positivity
  have hcoord (q : V) (i : Fin 3) : |f.linear q i| =
      (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * |e q i| := by
    rw [hf, abs_mul, abs_of_nonneg (hspos i)]
  have hunit (j i : Fin 3) : |e (boxAxis g j) i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, e.norm_map, boxAxis_norm] using
      PiLp.norm_apply_le (e (boxAxis g j)) i
  have h₀ : ‖f.linear (boxAxis g 0)‖ ≤ 3 / a := by
    have h0 : |f.linear (boxAxis g 0) 0| ≤ a⁻¹ := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 0 0) (inv_nonneg.mpr ha.le)
    have h1 : |f.linear (boxAxis g 0) 1| ≤ b⁻¹ := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 0 1) (inv_nonneg.mpr hbpos.le)
    have h2 : |f.linear (boxAxis g 0) 2| ≤ (1 / 4 : ℝ) := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 0 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hba : b⁻¹ ≤ a⁻¹ := inv_anti₀ ha hab
    have hquarter : (1 / 4 : ℝ) ≤ a⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ ha]
      linarith
    have hn := norm_le_coord_sum (f.linear (boxAxis g 0))
    rw [div_eq_mul_inv]
    linarith
  have hmid : |e (boxAxis g 1) 0| ≤ 8 * a := by
    have hh := adapted_middle_normal (boxAxis_norm e 0) g hg₀
    rw [inner_boxAxis, inner_boxAxis] at hh
    linarith
  have h₁ : ‖f.linear (boxAxis g 1)‖ ≤ 4 / b := by
    have h0 : |f.linear (boxAxis g 1) 0| ≤ 8 := by
      rw [hcoord]
      change a⁻¹ * |e (boxAxis g 1) 0| ≤ 8
      calc _ ≤ a⁻¹ * (8 * a) := mul_le_mul_of_nonneg_left hmid (inv_nonneg.mpr ha.le)
        _ = 8 := by field_simp
    have h1 : |f.linear (boxAxis g 1) 1| ≤ b⁻¹ := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 1 1) (inv_nonneg.mpr hbpos.le)
    have h2 : |f.linear (boxAxis g 1) 2| ≤ (1 / 4 : ℝ) := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 1 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc _ ≤ 8 + b⁻¹ + 1 / 4 := by linarith [norm_le_coord_sum (f.linear (boxAxis g 1))]
      _ ≤ 4 / b := by
        rw [le_div_iff₀ hbpos]
        have he : (8 + b⁻¹ + 1 / 4) * b = 8 * b + 1 + b / 4 := by field_simp <;> ring
        rw [he]
        linarith
  have hvnorm : ‖f.linear v‖ ≤ 9 := by
    have h0 : |f.linear v 0| ≤ 4 := by
      rw [hcoord]
      change a⁻¹ * |e v 0| ≤ 4
      calc _ ≤ a⁻¹ * (4 * a) := mul_le_mul_of_nonneg_left hv₀ (inv_nonneg.mpr ha.le)
        _ = 4 := by field_simp
    have h1 : |f.linear v 1| ≤ 4 := by
      rw [hcoord]
      change b⁻¹ * |e v 1| ≤ 4
      calc _ ≤ b⁻¹ * (4 * b) := mul_le_mul_of_nonneg_left hv₁ (inv_nonneg.mpr hbpos.le)
        _ = 4 := by field_simp
    have h2 : |f.linear v 2| ≤ (1 / 4 : ℝ) := by
      rw [hcoord]
      have hh : |e v 2| ≤ 1 := by
        simpa only [Real.norm_eq_abs, e.norm_map, hv] using PiLp.norm_apply_le (e v) 2
      simpa using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith [norm_le_coord_sum (f.linear v)]
  have hsize₀ : (10 * δ) * ‖f.linear (boxAxis g 0)‖ ≤ 32 * δ / a := by
    calc _ ≤ (10 * δ) * (3 / a) := mul_le_mul_of_nonneg_left h₀ (by positivity)
      _ ≤ _ := by
        rw [show (10 * δ) * (3 / a) = 30 * (δ / a) by ring,
          show 32 * δ / a = 32 * (δ / a) by ring]
        nlinarith [div_pos hδ ha]
  have hsize₁ : (6 * b * δ / r) * ‖f.linear (boxAxis g 1)‖ ≤ 32 * δ / a := by
    calc _ ≤ (6 * b * δ / r) * (4 / b) := mul_le_mul_of_nonneg_left h₁ (by positivity)
      _ = 24 * δ / r := by field_simp <;> ring
      _ ≤ 32 * δ / a := by
        rw [div_le_div_iff₀ hrpos ha]
        nlinarith [mul_le_mul_of_nonneg_left hr hδ.le]
  have ht := affine_prism_tube (by positivity : 0 ≤ 10 * δ)
    (by positivity : 0 ≤ 6 * b * δ / r) (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 < 32 * δ / a) z g f hsize₀ hsize₁
  rw [hgaxis] at ht
  constructor
  · have he : 2 * (32 * δ / a) = 64 * δ / a := by ring
    simpa only [he, div_self (by norm_num : (2 : ℝ) ≠ 0), one_smul] using ht
  · rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith

/-- The same round enclosure for angular packet prisms, whose middle
width may be as large as four. The radius increases only by a factor four. -/
theorem filled_prism_normalized_tube_wide {δ a b r : ℝ}
    (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 4) (hr : 5 * (a / 2) ≤ r)
    (z v : V) (hv : ‖v‖ = 1) (e g : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hf : ∀ q i, f.linear q i = (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * e q i)
    (hv₀ : |e v 0| ≤ 4 * a) (hv₁ : |e v 1| ≤ 4 * b)
    (hg₂ : ∀ p, g p 2 = inner ℝ v p)
    (hg₀ : ∀ w, |g w 0| ≤ 2 * (|inner ℝ (boxAxis e 0) w| +
      |inner ℝ (boxAxis e 0) v| * ‖w‖)) :
    f '' P (10 * δ) (6 * b * δ / r) 2 z g ⊆
      T (256 * δ / a) (f z - f.linear v) ((2 : ℝ) • f.linear v) ∧ ‖(2 : ℝ) • f.linear v‖ ≤ 20 := by
  have hbpos : 0 < b := ha.trans_le hab
  have hrpos : 0 < r := by linarith
  have hgaxis : boxAxis g 2 = v := adapted_long_axis hv g hg₂
  have hspos (i : Fin 3) : 0 ≤ (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i := by
    fin_cases i <;> simp <;> positivity
  have hcoord (q : V) (i : Fin 3) : |f.linear q i| =
      (![a⁻¹, b⁻¹, (1 / 4 : ℝ)] : Fin 3 → ℝ) i * |e q i| := by
    rw [hf, abs_mul, abs_of_nonneg (hspos i)]
  have hunit (j i : Fin 3) : |e (boxAxis g j) i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, e.norm_map, boxAxis_norm] using
      PiLp.norm_apply_le (e (boxAxis g j)) i
  have h₀ : ‖f.linear (boxAxis g 0)‖ ≤ 3 / a := by
    have h0 : |f.linear (boxAxis g 0) 0| ≤ a⁻¹ := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 0 0) (inv_nonneg.mpr ha.le)
    have h1 : |f.linear (boxAxis g 0) 1| ≤ b⁻¹ := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 0 1) (inv_nonneg.mpr hbpos.le)
    have h2 : |f.linear (boxAxis g 0) 2| ≤ (1 / 4 : ℝ) := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 0 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hba : b⁻¹ ≤ a⁻¹ := inv_anti₀ ha hab
    have hquarter : (1 / 4 : ℝ) ≤ a⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ ha]
      linarith
    have hn := norm_le_coord_sum (f.linear (boxAxis g 0))
    rw [div_eq_mul_inv]
    linarith
  have hmid : |e (boxAxis g 1) 0| ≤ 8 * a := by
    have hh := adapted_middle_normal (boxAxis_norm e 0) g hg₀
    rw [inner_boxAxis, inner_boxAxis] at hh
    linarith
  have h₁ : ‖f.linear (boxAxis g 1)‖ ≤ 36 / b := by
    have h0 : |f.linear (boxAxis g 1) 0| ≤ 8 := by
      rw [hcoord]
      change a⁻¹ * |e (boxAxis g 1) 0| ≤ 8
      calc _ ≤ a⁻¹ * (8 * a) := mul_le_mul_of_nonneg_left hmid (inv_nonneg.mpr ha.le)
        _ = 8 := by field_simp
    have h1 : |f.linear (boxAxis g 1) 1| ≤ b⁻¹ := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 1 1) (inv_nonneg.mpr hbpos.le)
    have h2 : |f.linear (boxAxis g 1) 2| ≤ (1 / 4 : ℝ) := by
      rw [hcoord]
      simpa using mul_le_mul_of_nonneg_left (hunit 1 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    calc _ ≤ 8 + b⁻¹ + 1 / 4 := by linarith [norm_le_coord_sum (f.linear (boxAxis g 1))]
      _ ≤ 36 / b := by
        rw [le_div_iff₀ hbpos]
        have he : (8 + b⁻¹ + 1 / 4) * b = 8 * b + 1 + b / 4 := by field_simp <;> ring
        rw [he]
        linarith
  have hvnorm : ‖f.linear v‖ ≤ 9 := by
    have h0 : |f.linear v 0| ≤ 4 := by
      rw [hcoord]
      change a⁻¹ * |e v 0| ≤ 4
      calc _ ≤ a⁻¹ * (4 * a) := mul_le_mul_of_nonneg_left hv₀ (inv_nonneg.mpr ha.le)
        _ = 4 := by field_simp
    have h1 : |f.linear v 1| ≤ 4 := by
      rw [hcoord]
      change b⁻¹ * |e v 1| ≤ 4
      calc _ ≤ b⁻¹ * (4 * b) := mul_le_mul_of_nonneg_left hv₁ (inv_nonneg.mpr hbpos.le)
        _ = 4 := by field_simp
    have h2 : |f.linear v 2| ≤ (1 / 4 : ℝ) := by
      rw [hcoord]
      have hh : |e v 2| ≤ 1 := by
        simpa only [Real.norm_eq_abs, e.norm_map, hv] using PiLp.norm_apply_le (e v) 2
      simpa using mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith [norm_le_coord_sum (f.linear v)]
  have hsize₀ : (10 * δ) * ‖f.linear (boxAxis g 0)‖ ≤ 128 * δ / a := by
    calc _ ≤ (10 * δ) * (3 / a) := mul_le_mul_of_nonneg_left h₀ (by positivity)
      _ ≤ _ := by
        rw [show (10 * δ) * (3 / a) = 30 * (δ / a) by ring,
          show 128 * δ / a = 128 * (δ / a) by ring]
        nlinarith [div_pos hδ ha]
  have hsize₁ : (6 * b * δ / r) * ‖f.linear (boxAxis g 1)‖ ≤ 128 * δ / a := by
    calc _ ≤ (6 * b * δ / r) * (36 / b) := mul_le_mul_of_nonneg_left h₁ (by positivity)
      _ = 216 * δ / r := by field_simp <;> ring
      _ ≤ 128 * δ / a := by
        rw [div_le_div_iff₀ hrpos ha]
        nlinarith [mul_le_mul_of_nonneg_left hr hδ.le]
  have ht := affine_prism_tube (by positivity : 0 ≤ 10 * δ)
    (by positivity : 0 ≤ 6 * b * δ / r) (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 < 128 * δ / a) z g f hsize₀ hsize₁
  rw [hgaxis] at ht
  constructor
  · have he : 2 * (128 * δ / a) = 256 * δ / a := by ring
    simpa only [he, div_self (by norm_num : (2 : ℝ) ≠ 0), one_smul] using ht
  · rw [norm_smul, Real.norm_eq_abs]
    norm_num
    linarith

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
