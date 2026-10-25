-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.CoarseProof.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.Cells
import Submission.WZ.Obl.wz_normalized_projection_iteration.Parameters
import Submission.WZ.Obl.wz_normalized_projection_iteration.Orientation
import Submission.WZ.Obl.wz_normalized_projection_iteration.Lifting
import Submission.WZ.Obl.wz_essentially_distinct_tube_count

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open MeasureTheory

/-- Coarse lifting with a fixed loss in projected outer area. -/
theorem coarse_lifting : CoarseLifting := by
  classical
  obtain ⟨P, hP, hpack⟩ := WangZahlLot.wz_essentially_distinct_tube_count
  refine ⟨7396, by norm_num, ?_⟩
  intro a β ha ha1 hβ
  obtain ⟨κ, hκ, d0, hd0, hparams⟩ := coarse_parameters hP ha hβ
  refine ⟨κ, hκ, d0, hd0, ?_⟩
  intro δ r hδ hd hδsmall hδr hra hrsmall n x v Y hH hv hF f hf hf0
  have hpacking := hpack δ hδ hδsmall n x v hH.2.1 hH.2.2.1 hH.2.2.2.1
  obtain ⟨hr1, hdensity, hcount, hcoeff⟩ := hparams δ r hδ hd hδr hra n hH.1 hpacking
  let x' : Fin n → Space := fun i => orientStart (x i) (v i)
  let v' : Fin n → Space := fun i => orientDir (v i)
  have hH' : Family κ δ n x' v' Y := family_orient hH
  have hF' : Frostman κ δ n x' v' := frostman_orient hF
  have hv2 : ∀ i, (1 / 2 : ℝ) ≤ v' i 2 := fun i => orientDir_vertical (hv i)
  obtain ⟨m, M, hm, hM, A, b, hA, hcard, hmax, hcell, hsep, hretain⟩ :=
    select_cells hδ hδr hr1 hκ hH' hv2
  have hYfinite (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ((measure_mono ((hH.2.2.2.2.2.1 i).trans (hH.2.2.1 i))).trans_lt measure_ball_lt_top).ne
  have hsumfinite : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => hYfinite i)
  have hmassreal : δ ^ κ * (n : ℝ) * δ ^ 2 ≤ ∑ i, (volume (Y i)).toReal := by
    have hh := ENNReal.toReal_mono hsumfinite hH.2.2.2.2.2.2
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ δ ^ κ * (n : ℝ) * δ ^ 2),
      ENNReal.toReal_sum (fun i _ => hYfinite i)] using hh
  have hc : 0 < (1 - (2 : ℝ) ^ (-κ)) / 2 := by
    have hh := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
      (by linarith : -κ < 0)
    linarith
  have hmass : δ ^ (8 * κ) * (n : ℝ) * δ ^ 2 ≤
      ∑ j, ∑ i ∈ A j, (volume (Y i)).toReal := by
    apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < linePalette by norm_num [linePalette])).mp
    calc
      (linePalette : ℝ) * (δ ^ (8 * κ) * (n : ℝ) * δ ^ 2) =
          ((linePalette : ℝ) * δ ^ (8 * κ)) * ((n : ℝ) * δ ^ 2) := by ring
      _ ≤ (δ ^ κ * ((1 - (2 : ℝ) ^ (-κ)) / 2) * (n : ℝ) ^ (-κ)) *
          ((n : ℝ) * δ ^ 2) := mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = (δ ^ κ * (n : ℝ) * δ ^ 2) * ((1 - (2 : ℝ) ^ (-κ)) / 2) *
          (n : ℝ) ^ (-κ) := by ring
      _ ≤ (∑ i, (volume (Y i)).toReal) * ((1 - (2 : ℝ) ^ (-κ)) / 2) *
          (n : ℝ) ^ (-κ) := by gcongr
      _ ≤ _ := hretain
  obtain ⟨Z, hZ, hZF, harea⟩ := family_of_cells hδ hδsmall hδr (by linarith : r ≤ 1 / 4)
    (Real.rpow_pos_of_pos hδ (8 * κ)) hdensity hcount hm hM hH' hv2 hF'
    A b hA hcard hmax hcell hsep hmass hf hf0
  refine ⟨m, (fun j => inwardStart r (x' (b j)) (v' (b j))), (fun j => v' (b j)),
    Z, hZ, ?_, hZF, harea⟩
  intro j
  exact (hv2 (b j)).trans (le_abs_self _)

end WangZahlLot.Obl.wz_normalized_projection_iteration
