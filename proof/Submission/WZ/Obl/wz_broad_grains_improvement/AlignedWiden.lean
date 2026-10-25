-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.AlignedWiden.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedPrismCover
import Submission.WZ.Obl.wz_broad_grains_improvement.AlignedGrid
import Submission.WZ.Obl.wz_wide_grains_axial_alignment.Crossing

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open Set Metric
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Crosses)

set_option maxHeartbeats 800000

/-- Widening only the middle side preserves the full crossing condition. -/
theorem aligned_crossing_widen {d a ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : 0 < c)
    {x v z : V} {e : V ≃ₗᵢ[ℝ] V} (hcross : Crosses d a (ρ*c) c x v z e) :
    Crosses d a ((10000*ρ)*c) c x v z e := by
  exact (WangZahlLot.Obl.wz_wide_grains_axial_alignment.crossing_widen
    ((convex_segment x (x+v)).thickening d) isOpen_thickening hc
    (by nlinarith : ρ*c ≤ (10000*ρ)*c) hcross.1 hcross.2).2

/-- A widened prism fits in the grid carrier of its representative,
without shortening its long side. -/
theorem aligned_widened_prism_carrier {d a ρ c : ℝ}
    (hd : 0 < d) (hda : d ≤ a) (haρ : a ≤ ρ*c)
    (hρ : 0 < ρ) (hc1 : c ≤ 1) (h4 : 4*d ≤ c)
    {x v y w z : V} {e : V ≃ₗᵢ[ℝ] V} (hv : ‖v‖ = 1)
    (hrep : Crosses d a (ρ*c) c x v z e)
    (hcell : alignedCell ρ x v = alignedCell ρ y w) :
    P a ((10000*ρ)*c) c z e ⊆ T (10000*ρ) y w ∧
      (e w 0)^2 + (e w 1)^2 ≤ (10*(10000*ρ))^2 := by
  have ha : 0 ≤ a := hd.le.trans hda
  have hc : 0 < c := by linarith
  have hbase := (crossing_prism_representative_carrier hd hda haρ hρ hc1 h4 hv hrep).1
  have hT := aligned_cell_tube_subset (s := 4096*ρ) hρ hcell
  refine ⟨?_, ?_⟩
  · intro p hp
    let q : V := p + (-(e (p-z) 1)) • e.symm (EuclideanSpace.single 1 1)
    have hcoord (j : Fin 3) : e (q-z) j = e (p-z) j + if j=1 then -(e (p-z) 1) else 0 :=
      WangZahlLot.Obl.wz_wide_grains_axial_alignment.coord_shift z e p _ 1 j
    have hq : q ∈ P a (ρ*c) c z e := by
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hcoord 0, show (0:Fin 3) ≠ 1 by decide, ite_false, add_zero] using hp.1
      · simp only [hcoord 1, ite_true, add_neg_cancel, abs_zero]
        positivity
      · simpa only [hcoord 2, show (2:Fin 3) ≠ 1 by decide, ite_false, add_zero] using hp.2.2
    have hpq : dist p q ≤ (10000*ρ)*c/2 := by
      rw [dist_comm]
      dsimp only [q]
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, e.symm.norm_map,
        PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_neg]
      exact hp.2.1
    obtain ⟨s, hs, hqs⟩ := mem_thickening_iff.mp (hT (hbase hq))
    apply mem_thickening_iff.mpr
    refine ⟨s, hs, lt_of_lt_of_le ((dist_triangle p q s).trans_lt (add_lt_add_of_le_of_lt hpq hqs)) ?_⟩
    nlinarith
  · have hdir := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.crossing_prism_direction
      e hd hda haρ h4 hv hrep.2
    have h0 : |e v 0| ≤ 6*ρ := hdir.1.trans ((div_le_iff₀ hc).mpr (by nlinarith))
    have h1 : |e v 1| ≤ 6*ρ := by
      have hh := hdir.2
      field_simp at hh
      exact hh
    have hclose := WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.norm_sub_lt_of_cellIdx_eq
      hρ (congrArg Prod.snd hcell)
    have hcoord (j : Fin 3) (hshort : |e v j| ≤ 6*ρ) : |e w j| ≤ 8*ρ := by
      have he : e w j = e v j - e (v-w) j := by
        simp only [map_sub, PiLp.sub_apply]
        ring
      have hn : |e (v-w) j| ≤ ‖v-w‖ := by
        simpa only [Real.norm_eq_abs, e.norm_map] using PiLp.norm_apply_le (e (v-w)) j
      rw [he]
      linarith [abs_sub (e v j) (e (v-w) j)]
    have hs0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 8*ρ)).mpr (hcoord 0 h0)
    have hs1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 8*ρ)).mpr (hcoord 1 h1)
    rw [sq_abs] at hs0 hs1
    nlinarith [sq_nonneg ρ]

end WangZahlLot.Obl.wz_broad_grains_improvement
