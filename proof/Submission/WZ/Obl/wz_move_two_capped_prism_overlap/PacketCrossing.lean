-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.PacketCrossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PacketContainment
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainRotation
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.EndTrimming
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.RobustTransversality

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, PacketCrossing.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (V P T boxAxis boxAxis_norm inner_boxAxis coarseLinear dualLinear
   normal_transport_coordinate dualLinear_norm_lower frozen_prism_norm
   frozen_prism_coarse_bounds frozenBasis)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (unit norm_sq_coords)
open WangZahlLot.Obl.wz_coarse_tube_grains.RIS (tubeEnds)

/-- Euclidean clearance implies the endpoint trimming condition used in
exact prism crossing. -/
theorem not_mem_tubeEnds_of_clearance {δ c : ℝ} {x v q : V}
    (hδc : δ ≤ c) (hv : ‖v‖ = 1)
    (hleft : 3 * c < dist q x) (hright : 3 * c < dist q (x + v)) :
    q ∉ tubeEnds δ c x v := by
  intro hq
  rcases hq with hq | hq
  · obtain ⟨p, ⟨t, ht, rfl⟩, hqp⟩ := mem_thickening_iff.mp hq
    have hd : dist (x + t • v) x = t := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hv,
        mul_one, abs_of_nonneg ht.1]
    have hh := dist_triangle q (x + t • v) x
    rw [hd] at hh
    linarith [ht.2]
  · obtain ⟨p, ⟨t, ht, rfl⟩, hqp⟩ := mem_thickening_iff.mp hq
    have hd : dist (x + t • v) (x + v) = 1 - t := by
      rw [dist_eq_norm, show x + t • v - (x + v) = (t - 1) • v by module,
        norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_nonpos (by linarith [ht.2])]
      ring
    have hh := dist_triangle q (x + t • v) (x + v)
    rw [hd] at hh
    linarith [ht.1]

/-- Angular and spatial packet closeness put every original prism well
inside a fixed larger prism, including in its long coordinate. -/
theorem packet_prism_in_core {ρ a c s : ℝ} {z z₀ : V}
    (e e₀ : V ≃ₗᵢ[ℝ] V)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (ha : 0 < a) (hac : a ≤ ρ * c)
    (hc : 0 < c) (hs : 0 < s) (has : a ≤ ρ * s * c)
    (hD0 : ‖dualLinear ρ (boxAxis e₀ 0)‖ ≤ 25 * ρ)
    (hD1 : ‖dualLinear ρ (boxAxis e₀ 1)‖ ≤ 25 * ρ)
    (haxis : ‖coarseLinear ρ (boxAxis e 2)‖ ≤ 43)
    (hangle : ‖unit (dualLinear ρ (boxAxis e 0)) -
      unit (dualLinear ρ (boxAxis e₀ 0))‖ ≤ s)
    (hcenter : ‖coarseLinear ρ (z - z₀)‖ ≤ c / 100)
    (hshortcenter : |inner ℝ (unit (dualLinear ρ (boxAxis e₀ 0)))
      (coarseLinear ρ (z - z₀))| ≤ s * c / 100) :
    P a (ρ * c) c z e ⊆
      P ((524288 * ρ * s * c) / 8) ((524288 * ρ * c) / 8) ((32 * c) / 8) z₀ e₀ := by
  have hbc : ρ * c ≤ c := by nlinarith
  have hcsrc := frozen_prism_coarse_bounds hρ hρ1 ha.le hac (le_refl (ρ * c)) hc z e haxis
  have hsub := WangZahlLot.Obl.wz_clustered_cover_volume_gain.physical_packet_enclosure
    hρ hρ1 hc hs has z z₀ (unit (dualLinear ρ (boxAxis e 0)))
    (frozenBasis e₀) (P a (ρ * c) c z e) hD0 hD1 hangle hcenter hshortcenter
    (fun p hp => frozen_prism_norm ha.le hac hbc z e hp)
    (fun p hp => (hcsrc p hp).1) (fun p hp => (hcsrc p hp).2)
  intro p hp
  have hh := hsub hp
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  simp only [WangZahlLot.Obl.wz_clustered_cover_volume_gain.frozenBasis_apply, inner_boxAxis,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h2
  refine ⟨?_, ?_, ?_⟩
  · change |e₀ (p - z₀) 0| ≤ _
    nlinarith [mul_pos (mul_pos hρ hs) hc]
  · change |e₀ (p - z₀) 1| ≤ _
    nlinarith [mul_pos hρ hc]
  · change |e₀ (p - z₀) 2| ≤ _
    linarith

/-- A fine direction crossing the source prism stays sufficiently axial
in a nearby packet frame. The coarse normalization controls the angular error. -/
theorem packet_direction_bounds {ρ a c s : ℝ} {v : V}
    (e e₀ : V ≃ₗᵢ[ℝ] V)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 16384) (hc : 0 < c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ ρ * s * c)
    (hv : ‖v‖ = 1) (hvcoarse : ‖coarseLinear ρ v‖ ≤ 15)
    (hvshort : |e v 0| ≤ 6 * a / c)
    (hD0 : ‖dualLinear ρ (boxAxis e₀ 0)‖ ≤ 25 * ρ)
    (hD1 : ‖dualLinear ρ (boxAxis e₀ 1)‖ ≤ 25 * ρ)
    (hangle : ‖unit (dualLinear ρ (boxAxis e 0)) -
      unit (dualLinear ρ (boxAxis e₀ 0))‖ ≤ s) :
    1 / 2 ≤ |e₀ v 2| ∧ |e₀ v 0| ≤ 525 * ρ * s ∧ |e₀ v 1| ≤ 375 * ρ := by
  have hρ1 : ρ ≤ 1 := by linarith
  have hn (j : Fin 3) : boxAxis e j ≠ 0 := by
    intro he
    have hh := boxAxis_norm e j
    simp [he] at hh
  have hn₀ (j : Fin 3) : boxAxis e₀ j ≠ 0 := by
    intro he
    have hh := boxAxis_norm e₀ j
    simp [he] at hh
  have hold : |inner ℝ (unit (dualLinear ρ (boxAxis e 0))) (coarseLinear ρ v)| ≤ 6 * s := by
    have hlo : ρ ≤ ‖dualLinear ρ (boxAxis e 0)‖ := by
      simpa only [boxAxis_norm, mul_one] using dualLinear_norm_lower hρ hρ1 (boxAxis e 0)
    have hcoord := normal_transport_coordinate hρ hρ1 (hn 0) v
    rw [inner_boxAxis] at hcoord
    have hmul : ρ * |inner ℝ (unit (dualLinear ρ (boxAxis e 0))) (coarseLinear ρ v)| ≤ |e v 0| := by
      rw [hcoord, abs_mul, abs_norm]
      exact mul_le_mul_of_nonneg_right hlo (abs_nonneg _)
    have hh := (le_div_iff₀ hc).mp hvshort
    apply (mul_le_mul_iff_right₀ (mul_pos hρ hc)).mp
    calc
      _ = (ρ * |inner ℝ (unit (dualLinear ρ (boxAxis e 0))) (coarseLinear ρ v)|) * c := by ring
      _ ≤ |e v 0| * c := mul_le_mul_of_nonneg_right hmul hc.le
      _ ≤ 6 * a := hh
      _ ≤ _ := by nlinarith
  have hnew : |inner ℝ (unit (dualLinear ρ (boxAxis e₀ 0))) (coarseLinear ρ v)| ≤ 21 * s := by
    have hdiff := abs_real_inner_le_norm
      (unit (dualLinear ρ (boxAxis e₀ 0)) - unit (dualLinear ρ (boxAxis e 0)))
      (coarseLinear ρ v)
    rw [inner_sub_left, norm_sub_rev] at hdiff
    have hm := mul_le_mul (by simpa only [norm_sub_rev] using hangle) hvcoarse
      (norm_nonneg _) hs.le
    have ha := abs_sub (inner ℝ (unit (dualLinear ρ (boxAxis e₀ 0))) (coarseLinear ρ v) -
      inner ℝ (unit (dualLinear ρ (boxAxis e 0))) (coarseLinear ρ v))
      (-inner ℝ (unit (dualLinear ρ (boxAxis e 0))) (coarseLinear ρ v))
    simp only [sub_neg_eq_add, sub_add_cancel, abs_neg] at ha
    linarith
  have h0 : |e₀ v 0| ≤ 525 * ρ * s := by
    rw [← inner_boxAxis e₀ 0 v, normal_transport_coordinate hρ hρ1 (hn₀ 0) v,
      abs_mul, abs_norm]
    have hh := mul_le_mul hD0 hnew (abs_nonneg _) (by positivity : 0 ≤ 25 * ρ)
    nlinarith
  have h1 : |e₀ v 1| ≤ 375 * ρ := by
    rw [← inner_boxAxis e₀ 1 v, ← WangZahlLot.Obl.wz_clustered_cover_volume_gain.dual_inner_coarse hρ]
    exact (abs_real_inner_le_norm _ _).trans ((mul_le_mul hD1 hvcoarse (norm_nonneg _)
      (by positivity : 0 ≤ 25 * ρ)).trans_eq (by ring))
  refine ⟨?_, h0, h1⟩
  have h0' : |e₀ v 0| ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_left hs1 (by positivity : 0 ≤ 525 * ρ)
    nlinarith
  have h1' : |e₀ v 1| ≤ 1 / 4 := by linarith
  have hsq := norm_sq_coords (e₀ v)
  rw [e₀.norm_map, hv] at hsq
  have hsq0 : (e₀ v 0) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith [sq_abs (e₀ v 0), abs_nonneg (e₀ v 0)]
  have hsq1 : (e₀ v 1) ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith [sq_abs (e₀ v 1), abs_nonneg (e₀ v 1)]
  nlinarith [sq_abs (e₀ v 2), abs_nonneg (e₀ v 2)]

/-- After whole-prism endpoint trimming, a fine tube crossing any member
of a close packet crosses the common containing prism through both long ends. -/
theorem packet_prism_crossing {δ ρ a c s : ℝ} {x v z z₀ q : V}
    (e e₀ : V ≃ₗᵢ[ℝ] V)
    (hδ : 0 < δ) (hδa : δ ≤ a) (hδc : 4 * δ ≤ c)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 16384) (hac : a ≤ ρ * c)
    (hs : 0 < s) (hs1 : s ≤ 1) (has : a ≤ ρ * s * c)
    (hv : ‖v‖ = 1) (hvcoarse : ‖coarseLinear ρ v‖ ≤ 15)
    (hD0 : ‖dualLinear ρ (boxAxis e₀ 0)‖ ≤ 25 * ρ)
    (hD1 : ‖dualLinear ρ (boxAxis e₀ 1)‖ ≤ 25 * ρ)
    (haxis : ‖coarseLinear ρ (boxAxis e 2)‖ ≤ 43)
    (hangle : ‖unit (dualLinear ρ (boxAxis e 0)) -
      unit (dualLinear ρ (boxAxis e₀ 0))‖ ≤ s)
    (hcenter : ‖coarseLinear ρ (z - z₀)‖ ≤ c / 100)
    (hshortcenter : |inner ℝ (unit (dualLinear ρ (boxAxis e₀ 0)))
      (coarseLinear ρ (z - z₀))| ≤ s * c / 100)
    (hcross : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P a (ρ * c) c z e, e (p - z) 2 = t)
    (hq : q ∈ T δ x v ∩ P a (ρ * c) c z e)
    (hleft : 96 * c < dist q x) (hright : 96 * c < dist q (x + v)) :
    (∀ p ∈ T δ x v ∩ frontier (P (524288 * ρ * s * c) (524288 * ρ * c) (32 * c) z₀ e₀),
      |e₀ (p - z₀) 2| = (32 * c) / 2) ∧
    (∀ t ∈ ({-(32 * c) / 2, (32 * c) / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P (524288 * ρ * s * c) (524288 * ρ * c) (32 * c) z₀ e₀,
        e₀ (p - z₀) 2 = t) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hc : 0 < c := by linarith
  have hρ1 : ρ ≤ 1 := by linarith
  have hdir := WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.crossing_prism_direction
    e hδ hδa hac hδc hv hcross
  obtain ⟨hlong, h0, h1⟩ := packet_direction_bounds e e₀ hρ hρsmall hc hs hs1 has
    hv hvcoarse hdir.1 hD0 hD1 hangle
  have hcore := packet_prism_in_core e e₀ hρ hρ1 ha hac hc hs has hD0 hD1 haxis
    hangle hcenter hshortcenter hq.2
  have hend : q ∉ tubeEnds δ (32 * c) x v :=
    not_mem_tubeEnds_of_clearance (by linarith) hv (by nlinarith) (by nlinarith)
  have hscale : δ ≤ ρ * s * c := hδa.trans has
  have hsbc : ρ * s * c ≤ ρ * c := by nlinarith
  apply WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.prism_crossing_of_core_point e₀ hδ
  · nlinarith
  · nlinarith
  · linarith
  · exact hlong
  · nlinarith [mul_le_mul_of_nonneg_left h0 (show 0 ≤ 32 * c by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left h1 (show 0 ≤ 32 * c by positivity)]
  · exact ⟨⟨hq.1, hend⟩, hcore⟩

/-- Exact coarse containment bounds the fine direction in coarse
coordinates, once the coarse axis has been rotated near the vertical axis. -/
theorem contained_direction_coarse_norm {δ ρ : ℝ} {x v y w : V}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hw0 : |w 0| ≤ ρ) (hw1 : |w 1| ≤ ρ)
    (hcontain : T δ x v ⊆ T ρ y w) : ‖coarseLinear ρ v‖ ≤ 15 := by
  have hdir := WangZahlLot.Obl.wz_extremal_lipschitz_grains.direction_close_of_subset
    hδ hv hw hcontain
  have h0 : |v 0| ≤ 5 * ρ :=
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.coord_abs_le_of_projective v w 0).trans
      (by dsimp only [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd]; linarith)
  have h1 : |v 1| ≤ 5 * ρ :=
    (WangZahlLot.Obl.wz_clustered_cover_volume_gain.coord_abs_le_of_projective v w 1).trans
      (by dsimp only [WangZahlLot.Obl.wz_affine_robust_cluster_estimate.pd]; linarith)
  have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.coarse_norm_of_coords hρ hv h0 h1
  norm_num at hh ⊢
  linarith

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
