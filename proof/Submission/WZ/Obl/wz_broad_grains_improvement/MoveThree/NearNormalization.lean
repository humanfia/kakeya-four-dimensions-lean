-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.NearNormalization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/NearNormalization.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NearGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm inner_boxAxis)

noncomputable section

/-- Natural normalization controls the short coordinate in every neighboring
plate, rather than only in the reference frame. -/
theorem near_plate_short_coordinate {a ρ c : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hc : 0 < c)
    (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hnear : P (a / ρ) c c z e ⊆ P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀)
    (hcoord : ∀ q j, f q j = ![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹] j * e₀ (q - z₀) j)
    (q : V) : |e (q - z) 0| ≤ 36 * a / ρ * dist (f q) (f z) := by
  have hn := near_plate_normal_coordinates (div_pos ha hρ) hc z z₀ e e₀
    (by simpa only [mul_div_assoc] using hnear)
  have hcomm (j : Fin 3) : e (boxAxis e₀ j) 0 = e₀ (boxAxis e 0) j := by
    rw [← inner_boxAxis, ← inner_boxAxis, real_inner_comm]
  have hc0 : |e₀ (boxAxis e 0) 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs, e₀.norm_map, boxAxis_norm] using
      PiLp.norm_apply_le (e₀ (boxAxis e 0)) 0
  have hc1 : |e₀ (boxAxis e 0) 1| ≤ 4 * (a / ρ) / c := by
    rw [← hcomm]
    exact hn 1 (by decide)
  have hc2 : |e₀ (boxAxis e 0) 2| ≤ 4 * (a / ρ) / c := by
    rw [← hcomm]
    exact hn 2 (by decide)
  have hdiff (j : Fin 3) : e₀ (q - z) j =
      ![4 * a / ρ, 4 * c, 4 * c] j * (f q - f z) j := by
    simp only [PiLp.sub_apply, hcoord]
    fin_cases j <;> dsimp <;> simp only [map_sub, PiLp.sub_apply]
    <;> field_simp <;> ring
  have hsmall (j : Fin 3) : |(f q - f z) j| ≤ dist (f q) (f z) := by
    simpa only [Real.norm_eq_abs, dist_eq_norm] using PiLp.norm_apply_le (f q - f z) j
  have hv0 : |e₀ (q - z) 0| ≤ (4 * a / ρ) * dist (f q) (f z) := by
    rw [hdiff 0]
    change |(4 * a / ρ) * (f q - f z) 0| ≤ _
    rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * a / ρ)]
    exact mul_le_mul_of_nonneg_left (hsmall 0) (by positivity)
  have hv1 : |e₀ (q - z) 1| ≤ (4 * c) * dist (f q) (f z) := by
    rw [hdiff 1]
    change |(4 * c) * (f q - f z) 1| ≤ _
    rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * c)]
    exact mul_le_mul_of_nonneg_left (hsmall 1) (by positivity)
  have hv2 : |e₀ (q - z) 2| ≤ (4 * c) * dist (f q) (f z) := by
    rw [hdiff 2]
    change |(4 * c) * (f q - f z) 2| ≤ _
    rw [abs_mul, abs_of_pos (by positivity : 0 < 4 * c)]
    exact mul_le_mul_of_nonneg_left (hsmall 2) (by positivity)
  have he : e (q - z) 0 =
      e₀ (boxAxis e 0) 0 * e₀ (q - z) 0 +
      e₀ (boxAxis e 0) 1 * e₀ (q - z) 1 +
      e₀ (boxAxis e 0) 2 * e₀ (q - z) 2 := by
    rw [← inner_boxAxis, ← e₀.inner_map_map]
    simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
    ring
  rw [he]
  calc
    _ ≤ |e₀ (boxAxis e 0) 0| * |e₀ (q - z) 0| +
        |e₀ (boxAxis e 0) 1| * |e₀ (q - z) 1| +
        |e₀ (boxAxis e 0) 2| * |e₀ (q - z) 2| := by
      simpa only [abs_mul] using (abs_add_le
        (e₀ (boxAxis e 0) 0 * e₀ (q - z) 0 + e₀ (boxAxis e 0) 1 * e₀ (q - z) 1)
        (e₀ (boxAxis e 0) 2 * e₀ (q - z) 2)).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 1 * ((4 * a / ρ) * dist (f q) (f z)) +
        (4 * (a / ρ) / c) * ((4 * c) * dist (f q) (f z)) +
        (4 * (a / ρ) / c) * ((4 * c) * dist (f q) (f z)) := by
      gcongr
    _ = _ := by field_simp; ring

/-- The image of every neighboring grain contains a ball whose radius is a
fixed multiple of rho, even when the original short side is much smaller. -/
theorem near_plate_normalized_ball {a ρ c : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hc : 0 < c)
    (z z₀ : V) (e e₀ : V ≃ₗᵢ[ℝ] V) (f : V ≃ᵃ[ℝ] V)
    (hnear : P (a / ρ) c c z e ⊆ P (2 * a / ρ) (2 * c) (2 * c) z₀ e₀)
    (hcoord : ∀ q j, f q j = ![ρ / (4 * a), (4 * c)⁻¹, (4 * c)⁻¹] j * e₀ (q - z₀) j)
    (hdist : ∀ p q, dist p q / (4 * c) ≤ dist (f p) (f q)) :
    ball (f z) (ρ / 100) ⊆ f '' P a (ρ * c) c z e := by
  intro p hp
  let q := f.symm p
  have hfp : f q = p := f.apply_symm_apply p
  have hd : dist (f q) (f z) < ρ / 100 := by simpa only [hfp, mem_ball] using hp
  have hshort := near_plate_short_coordinate ha hρ hc z z₀ e e₀ f hnear hcoord q
  have hshort' : |e (q - z) 0| ≤ a / 2 := by
    have hh := mul_lt_mul_of_pos_left hd (by positivity : 0 < 36 * a / ρ)
    have he : (36 * a / ρ) * (ρ / 100) = 9 * a / 25 := by field_simp; ring
    rw [he] at hh
    linarith
  have hnorm : ‖q - z‖ < ρ * c / 25 := by
    have hh := (hdist q z).trans_lt hd
    rw [div_lt_iff₀ (by positivity : 0 < 4 * c)] at hh
    rw [dist_eq_norm] at hh
    convert hh using 1 <;> ring
  have hcoord' (j : Fin 3) : |e (q - z) j| ≤ ρ * c / 25 := by
    have hh := PiLp.norm_apply_le (e (q - z)) j
    rw [Real.norm_eq_abs, e.norm_map] at hh
    exact hh.trans hnorm.le
  refine ⟨q, ⟨hshort', (hcoord' 1).trans ?_, (hcoord' 2).trans ?_⟩, hfp⟩
  · nlinarith [mul_pos hρ hc]
  · nlinarith [mul_le_mul_of_nonneg_right hρ1 hc.le]

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
