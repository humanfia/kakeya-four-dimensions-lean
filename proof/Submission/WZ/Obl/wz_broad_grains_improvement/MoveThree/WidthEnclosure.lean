-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.WidthEnclosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/WidthEnclosure.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, WidthEnclosure.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConvexEnclosure
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.ConvexBox

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (orthogonalBox exists_comparable_orthogonal_box volume_orthogonalBox)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm)

/-- Interior radius, diameter and volume bound the middle side of a
comparable orthogonal enclosure. This retains information lost by merely
bounding all three sides by the diameter. -/
theorem convex_prism_middle_bound {U : Set V} {r R c vol : ℝ} {z : V}
    (hU : IsCompact U) (hconv : Convex ℝ U) (hr : 0 < r) (hc : 0 < c)
    (hball : ball z r ⊆ U) (hbound : U ⊆ closedBall z R)
    (hdiam : ∃ p ∈ U, ∃ q ∈ U, c ≤ dist p q)
    (hvol : μ U ≤ O vol) :
    ∃ (A B C : ℝ) (e : V ≃ₗᵢ[ℝ] V),
      r ≤ A ∧ A ≤ B ∧ B ≤ C ∧ C ≤ 24*R ∧ c ≤ 2*C ∧
      B ≤ 8192*vol/(c*r) ∧ U ⊆ P A B C z e ∧
      μ (P A B C z e) ≤ O 4096*μ U := by
  let f : V ≃ᵃ[ℝ] V := AffineEquiv.constVAdd ℝ V (-z)
  have hf (p : V) : f p = p-z := by change -z+p=p-z; abel
  let U₀ := f '' U
  have hU₀ : IsCompact U₀ := hU.image f.toContinuousAffineEquiv.continuous
  have hconv₀ : Convex ℝ U₀ := hconv.affine_image f.toAffineMap
  have hball₀ : ball (0 : V) r ⊆ U₀ := by
    intro p hp
    refine ⟨p+z, hball ?_, ?_⟩
    · simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hp
    · rw [hf, add_sub_cancel_right]
  have hbound₀ : U₀ ⊆ closedBall (0 : V) R := by
    rintro _ ⟨p, hp, rfl⟩
    simpa only [hf, mem_closedBall, dist_eq_norm, sub_zero] using hbound hp
  have hmeasure : μ U₀ = μ U := by
    have he : U₀ = (fun p : V => p + -z) '' U := by
      apply image_congr
      intro p _
      rw [hf, sub_eq_add_neg]
    rw [he, image_add_right]
    exact measure_preimage_add_right volume _ _
  obtain ⟨u,w,hw,horder,hwidth,hbox,hvolume⟩ :=
    exists_comparable_orthogonal_box hU₀ hconv₀ hr hball₀ hbound₀
  have hw0 := hw 0
  have hw1 := hw 1
  have hw2 := hw 2
  have hcoords {p : V} (hp : p ∈ U) (i : Fin 3) :
      |inner ℝ (u i) (p-z)| ≤ w i := by
    have hh := hbox (mem_image_of_mem f hp) i
    simpa only [hf, sub_zero] using hh
  have hlong : c ≤ 4*w 0 := by
    obtain ⟨p,hp,q,hq,hd⟩ := hdiam
    have hcoord (i : Fin 3) : |u.repr (p-q) i| ≤ 2*w 0 := by
      rw [OrthonormalBasis.repr_apply_apply,
        show p-q=(p-z)-(q-z) by abel, inner_sub_right]
      exact (abs_sub _ _).trans (by linarith [hcoords hp i, hcoords hq i, horder (Fin.zero_le i)])
    have hn := WangZahlLot.Obl.wz_balanced_cluster_cover.norm_le_of_forall_abs_le
      (by positivity : 0 ≤ 2*w 0) hcoord
    rw [u.repr.norm_map] at hn
    exact hd.trans (by rw [dist_eq_norm]; linarith)
  let v := u.reindex (Fin.revPerm : Equiv.Perm (Fin 3))
  have hv0 : v 0 = u 2 := by simp [v,OrthonormalBasis.reindex_apply,Fin.revPerm]
  have hv1 : v 1 = u 1 := by simp [v,OrthonormalBasis.reindex_apply,Fin.revPerm]
  have hv2 : v 2 = u 0 := by simp [v,OrthonormalBasis.reindex_apply,Fin.revPerm]
  have hP : U ⊆ P (2*w 2) (2*w 1) (2*w 0) z v.repr := by
    intro p hp
    change |v.repr (p-z) 0| ≤ (2*w 2)/2 ∧
      |v.repr (p-z) 1| ≤ (2*w 1)/2 ∧ |v.repr (p-z) 2| ≤ (2*w 0)/2
    simp only [OrthonormalBasis.repr_apply_apply,hv0,hv1,hv2]
    exact ⟨by linarith [hcoords hp 2],by linarith [hcoords hp 1],
      by linarith [hcoords hp 0]⟩
  have hPV : μ (P (2*w 2) (2*w 1) (2*w 0) z v.repr) =
      O ((2*w 2)*(2*w 1)*(2*w 0)) :=
    WangZahlLot.Obl.wz_move_three_thick_grains_gain.volume_P
      (by positivity) (by positivity) (by positivity) _ _
  have hPvol : μ (P (2*w 2) (2*w 1) (2*w 0) z v.repr) =
      μ (orthogonalBox w (0 : V) u) := by
    rw [hPV]
    change O _ = volume (orthogonalBox w (0 : V) u)
    rw [volume_orthogonalBox w (fun i => (hw i).le), Fin.prod_univ_three]
    congr 1
    ring
  have hvolume' : μ (P (2*w 2) (2*w 1) (2*w 0) z v.repr) ≤ O 4096*μ U := by
    rw [hPvol]
    calc
      _ = O 4096*(O (1/4096)*μ (orthogonalBox w (0 : V) u)) := by
        rw [← mul_assoc,← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4096)]
        norm_num [O]
      _ ≤ O 4096*μ U₀ := mul_le_mul' le_rfl hvolume
      _ = _ := by rw [hmeasure]
  have hvnonneg : 0 ≤ vol := by
    have hpos : 0 < μ U := (measure_ball_pos volume z hr).trans_le (measure_mono hball)
    exact (ENNReal.ofReal_pos.mp (hpos.trans_le hvol)).le
  have hprod : (2*w 2)*(2*w 1)*(2*w 0) ≤ 4096*vol := by
    have hh := hvolume'.trans (mul_le_mul' le_rfl hvol)
    rw [hPV, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4096)] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 4096*vol)).mp hh
  refine ⟨2*w 2,2*w 1,2*w 0,v.repr,?_,?_,?_,?_,?_,?_,hP,hvolume'⟩
  · linarith [(hwidth 2).1]
  · linarith [horder (by decide : (1 : Fin 3) ≤ 2)]
  · linarith [horder (by decide : (0 : Fin 3) ≤ 1)]
  · linarith [(hwidth 0).2]
  · linarith
  · apply (le_div_iff₀ (mul_pos hc hr)).mpr
    have hs : r ≤ 2*w 2 := by linarith [(hwidth 2).1]
    have h1 := mul_le_mul hs hlong (by positivity : 0 ≤ c) (by positivity : 0 ≤ 2*w 2)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2*w 1)
    nlinarith only [h2,hprod]

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
