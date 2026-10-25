import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/ComparisonMeshNumerics.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

noncomputable section

/-- Explicit mesh inequalities, without an analytic conclusion. `ζ` is
the primitive physical mesh and `δ` the common normalized jitter mesh. -/
structure ComparisonMeshBounds (K H h g b a χ B V δ η ζ : ℝ) : Prop where
  mesh_pos : 0 < δ
  mesh_small : δ ≤ 1 / 32
  physical_nonneg : 0 ≤ η
  physical_small : η ≤ 1
  coeff_nonneg : 0 ≤ B
  velocity_nonneg : 0 ≤ V
  domain_velocity : K + g ≤ V
  major_velocity : K + χ ≤ V
  cap_resolution : 54 * B * (K + 1) ^ 4 * ζ ≤ a
  cap_time : ζ ≤ (32 * h) * δ
  cap_major_width : ζ ≤ 2 * χ
  cap_transverse_width : ζ ≤ (32 * b) * δ
  cap_major_motion : V * ζ ≤ 2 * χ
  cap_transverse_motion : V * ζ ≤ (32 * b) * δ
  jitter_time : (32 * h) * δ ≤ η
  jitter_transverse : (V * (32 * h) + 32 * b) * δ ≤ η
  jitter_resolution : 54 * B * (K + 1) ^ 4 * η ≤ H * a

/-- One coarse fixed-power bound gives fixed-power meshes. These large
exponents concern only the primitive cap resolution, not the layer depth. -/
theorem comparison_mesh_from_power_bound {X K H h g b a χ : ℝ}
    (hX : 2 ≤ X) (hK0 : 0 ≤ K) (hKX : K ≤ X) (hH : 1 ≤ H)
    (hhlo : X ^ (-1 : ℝ) ≤ h) (hhhi : h ≤ X)
    (hbg : g ≤ X) (hblo : X ^ (-1 : ℝ) ≤ b) (hbhi : b ≤ X)
    (ha : X ^ (-1 : ℝ) ≤ a) (hχlo : X ^ (-1 : ℝ) ≤ χ) (hχhi : χ ≤ X) :
    ComparisonMeshBounds K H h g b a χ X (3 * X)
      (X ^ (-40 : ℝ)) (X ^ (-20 : ℝ)) (X ^ (-80 : ℝ)) := by
  have hXp : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hxinv : 0 < X ^ (-1 : ℝ) := Real.rpow_pos_of_pos hXp _
  have hh : 0 < h := hxinv.trans_le hhlo
  have hb : 0 < b := hxinv.trans_le hblo
  have hap : 0 < a := hxinv.trans_le ha
  have hχ : 0 < χ := hxinv.trans_le hχlo
  have hδ : 0 < X ^ (-40 : ℝ) := Real.rpow_pos_of_pos hXp _
  have hη : 0 < X ^ (-20 : ℝ) := Real.rpow_pos_of_pos hXp _
  have hζ : 0 < X ^ (-80 : ℝ) := Real.rpow_pos_of_pos hXp _
  have ple {s t : ℝ} (hst : s ≤ t) : X ^ s ≤ X ^ t :=
    Real.rpow_le_rpow_of_exponent_le hX1 hst
  have h32 : (32 : ℝ) ≤ X ^ (5 : ℝ) := by
    calc
      _ = (2 : ℝ) ^ (5 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
  have h128 : (128 : ℝ) ≤ X ^ (7 : ℝ) := by
    calc
      _ = (2 : ℝ) ^ (7 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
  have h864 : (864 : ℝ) ≤ X ^ (10 : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (10 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
  have h3 : (3 : ℝ) ≤ X ^ (2 : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
  have hV : 3 * X ≤ X ^ (3 : ℝ) := by
    calc
      _ ≤ X ^ (2 : ℝ) * X := mul_le_mul_of_nonneg_right h3 hXp.le
      _ = _ := by conv_lhs => rhs; rw [← Real.rpow_one X]
                  rw [← Real.rpow_add hXp]; norm_num
  have hδsmall : X ^ (-40 : ℝ) ≤ 1 / 32 := by
    calc
      _ ≤ X ^ (-5 : ℝ) := ple (by norm_num)
      _ = (X ^ (5 : ℝ))⁻¹ := Real.rpow_neg hXp.le _
      _ ≤ (32 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h32
      _ = _ := by norm_num
  have hcost : 54 * X * (K + 1) ^ 4 ≤ 864 * X ^ (5 : ℝ) := by
    have hK1 : K + 1 ≤ 2 * X := by linarith
    calc
      _ ≤ 54 * X * (2 * X) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hK1 4) (by positivity)
      _ = _ := by rw [Real.rpow_ofNat]; ring
  have hcostη : 54 * X * (K + 1) ^ 4 * X ^ (-20 : ℝ) ≤ X ^ (-1 : ℝ) := by
    calc
      _ ≤ (864 * X ^ (5 : ℝ)) * X ^ (-20 : ℝ) :=
        mul_le_mul_of_nonneg_right hcost hη.le
      _ ≤ (X ^ (10 : ℝ) * X ^ (5 : ℝ)) * X ^ (-20 : ℝ) := by gcongr
      _ = X ^ (-5 : ℝ) := by rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]; norm_num
      _ ≤ _ := ple (by norm_num)
  have hcostζ : 54 * X * (K + 1) ^ 4 * X ^ (-80 : ℝ) ≤ X ^ (-1 : ℝ) := by
    calc
      _ ≤ (864 * X ^ (5 : ℝ)) * X ^ (-80 : ℝ) :=
        mul_le_mul_of_nonneg_right hcost hζ.le
      _ ≤ (X ^ (10 : ℝ) * X ^ (5 : ℝ)) * X ^ (-80 : ℝ) := by gcongr
      _ = X ^ (-65 : ℝ) := by rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]; norm_num
      _ ≤ _ := ple (by norm_num)
  have hVζ : (3 * X) * X ^ (-80 : ℝ) ≤ X ^ (-41 : ℝ) := by
    calc
      _ ≤ X ^ (3 : ℝ) * X ^ (-80 : ℝ) := mul_le_mul_of_nonneg_right hV hζ.le
      _ = X ^ (-77 : ℝ) := by rw [← Real.rpow_add hXp]; norm_num
      _ ≤ _ := ple (by norm_num)
  have hcell (w : ℝ) (hw : X ^ (-1 : ℝ) ≤ w) :
      X ^ (-41 : ℝ) ≤ (32 * w) * X ^ (-40 : ℝ) := by
    have hw0 : 0 < w := hxinv.trans_le hw
    calc
      _ = X ^ (-1 : ℝ) * X ^ (-40 : ℝ) := by rw [← Real.rpow_add hXp]; norm_num
      _ ≤ w * X ^ (-40 : ℝ) := mul_le_mul_of_nonneg_right hw hδ.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
  have hgeom : (3 * X) * (32 * h) + 32 * b ≤ 128 * X ^ (2 : ℝ) := by
    have hhh := mul_le_mul_of_nonneg_left hhhi (show (0 : ℝ) ≤ 96 * X by positivity)
    have hbb := mul_le_mul_of_nonneg_left hbhi (show (0 : ℝ) ≤ 32 by norm_num)
    have hsq : X ≤ X ^ 2 := le_self_pow₀ hX1 (by norm_num : 2 ≠ 0)
    rw [Real.rpow_two]
    nlinarith
  have hjit : ((3 * X) * (32 * h) + 32 * b) * X ^ (-40 : ℝ) ≤ X ^ (-20 : ℝ) := by
    calc
      _ ≤ (128 * X ^ (2 : ℝ)) * X ^ (-40 : ℝ) := mul_le_mul_of_nonneg_right hgeom hδ.le
      _ ≤ (X ^ (7 : ℝ) * X ^ (2 : ℝ)) * X ^ (-40 : ℝ) := by gcongr
      _ = X ^ (-31 : ℝ) := by rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]; norm_num
      _ ≤ _ := ple (by norm_num)
  have htime : (32 * h) * X ^ (-40 : ℝ) ≤ X ^ (-20 : ℝ) := by
    apply le_trans (mul_le_mul_of_nonneg_right (show 32 * h ≤ (3 * X) * (32 * h) + 32 * b from ?_) hδ.le) hjit
    calc
      _ ≤ (3 * X) * (32 * h) := le_mul_of_one_le_left (by positivity) (by linarith)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hmajor : X ^ (-41 : ℝ) ≤ 2 * χ :=
    (ple (by norm_num : (-41 : ℝ) ≤ -1)).trans (hχlo.trans (by linarith))
  exact {
    mesh_pos := hδ
    mesh_small := hδsmall
    physical_nonneg := hη.le
    physical_small := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by norm_num)
    coeff_nonneg := hXp.le
    velocity_nonneg := by positivity
    domain_velocity := by linarith
    major_velocity := by linarith
    cap_resolution := hcostζ.trans ha
    cap_time := (ple (by norm_num : (-80 : ℝ) ≤ -41)).trans (hcell h hhlo)
    cap_major_width := (ple (by norm_num : (-80 : ℝ) ≤ -41)).trans hmajor
    cap_transverse_width := (ple (by norm_num : (-80 : ℝ) ≤ -41)).trans (hcell b hblo)
    cap_major_motion := hVζ.trans hmajor
    cap_transverse_motion := hVζ.trans (hcell b hblo)
    jitter_time := htime
    jitter_transverse := hjit
    jitter_resolution := hcostη.trans (ha.trans (le_mul_of_one_le_left hap.le hH)) }

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
