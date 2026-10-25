-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.CrossingSlab.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_move_two_long_grains_gain.CrossBox
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Volume
import Submission.WZ.Obl.wz_broad_grains_initialization.CubeGeometry

/-! A tube crossing only through long faces fills the intervening axial slab. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory Metric

lemma Crosses.interior_of_long_lt {d a b c : ℝ} {x v z p : V} {e : V ≃ₗᵢ[ℝ] V}
    (h : Crosses d a b c x v z e) (hpT : p ∈ T d x v) (hpP : p ∈ P a b c z e)
    (hp : |e (p-z) 2| < c/2) : p ∈ interior (P a b c z e) := by
  by_contra hnot
  have hf : p ∈ frontier (P a b c z e) := ⟨subset_closure hpP, hnot⟩
  exact hp.ne (h.1 p ⟨hpT, hf⟩)

lemma long_slab_convex (c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    Convex ℝ {p : V | |e (p-z) 2| < c/2} := by
  let l : V →ₗ[ℝ] ℝ :=
    { toFun := fun p => e p 2
      map_add' := by intros; simp
      map_smul' := by intros; simp }
  have h := ((convex_Ioo (-c/2) (c/2)).linear_preimage l).translate_preimage_left (-z)
  convert h using 1
  ext p
  simp [l, abs_lt, sub_eq_add_neg, neg_div]

/-- The long-face crossing condition forces every tube point between the long
faces to be in the prism. This needs no tube-direction bounds. -/
theorem Crosses.slab_subset {d a b c : ℝ} {x v z : V} {e : V ≃ₗᵢ[ℝ] V}
    (hc : 0 < c) (h : Crosses d a b c x v z e) :
    T d x v ∩ {p | |e (p-z) 2| < c/2} ⊆ interior (P a b c z e) := by
  let S := T d x v ∩ {p | |e (p-z) 2| < c/2}
  have hS : IsPreconnected S :=
    ((wz_flat_cluster_slab_filling.tube_convex d x v).inter (long_slab_convex c z e)).isPreconnected
  obtain ⟨p, hp, hep⟩ := h.2 (-c/2) (by simp)
  obtain ⟨q, hq, heq⟩ := h.2 (c/2) (by simp)
  let r : V := (1/2 : ℝ) • p + (1/2 : ℝ) • q
  have hrT : r ∈ T d x v := (wz_flat_cluster_slab_filling.tube_convex d x v)
    hp.1 hq.1 (by norm_num) (by norm_num) (by norm_num)
  have hrP : r ∈ P a b c z e := (wz_two_scale_flat_box_estimate.box_convex a b c z e)
    hp.2 hq.2 (by norm_num) (by norm_num) (by norm_num)
  have hr0 : e (r-z) 2 = 0 := by
    have hre : r-z = (1/2 : ℝ) • (p-z) + (1/2 : ℝ) • (q-z) := by dsimp [r]; module
    rw [hre, map_add, map_smul, map_smul]
    change (1/2 : ℝ) * e (p-z) 2 + (1/2 : ℝ) * e (q-z) 2 = 0
    rw [hep, heq]
    ring
  have hrlt : |e (r-z) 2| < c/2 := by rw [hr0, abs_zero]; positivity
  have hnon : (S ∩ interior (P a b c z e)).Nonempty :=
    ⟨r, ⟨hrT, hrlt⟩, h.interior_of_long_lt hrT hrP hrlt⟩
  apply hS.subset_left_of_subset_union isOpen_interior
    (wz_two_scale_flat_box_estimate.box_isClosed a b c z e).isOpen_compl
    (Set.disjoint_left.mpr (fun _ hp hq => hq (interior_subset hp))) _ hnon
  intro p hp
  by_cases hpP : p ∈ P a b c z e
  · exact Or.inl (h.interior_of_long_lt hp.1 hpP hp.2)
  · exact Or.inr hpP

/-- Crossing a prism whose two smaller dimensions are at most its length
forces a definite component in its long direction. -/
theorem Crosses.long_direction {d a b c : ℝ} {x v z : V} {e : V ≃ₗᵢ[ℝ] V}
    (hc : 0 < c) (hdc : d ≤ c/100) (hab : a ≤ b) (hbc : b ≤ c) (hv : ‖v‖ = 1)
    (h : Crosses d a b c x v z e) : 1/4 ≤ |e v 2| := by
  obtain ⟨p, hp, hep⟩ := h.2 (-c/2) (by simp)
  obtain ⟨q, hq, heq⟩ := h.2 (c/2) (by simp)
  obtain ⟨s, _, hs⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hp.1
  obtain ⟨t, _, ht⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hq.1
  have hpB := wz_two_scale_flat_box_estimate.box_subset_closedBall hab hbc hc.le z e hp.2
  have hqB := wz_two_scale_flat_box_estimate.box_subset_closedBall hab hbc hc.le z e hq.2
  change dist p z ≤ c at hpB
  change dist q z ≤ c at hqB
  have hpq : ‖q-p‖ ≤ 2*c := by
    have hh := dist_triangle q z p
    rw [dist_comm z p] at hh
    have : dist q p ≤ 2*c := by linarith [hpB, hqB]
    simpa only [dist_eq_norm] using this
  have hst : |t-s| ≤ 3*c := by
    have he : (t-s) • v = (q-p) + (p-(x+s•v)) - (q-(x+t•v)) := by module
    have hn : ‖(t-s) • v‖ = |t-s| := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
    rw [← hn, he]
    calc
      _ ≤ ‖q-p‖ + ‖p-(x+s•v)‖ + ‖q-(x+t•v)‖ := by
        linarith [norm_sub_le ((q-p) + (p-(x+s•v))) (q-(x+t•v)),
          norm_add_le (q-p) (p-(x+s•v))]
      _ ≤ 3*c := by linarith
  have hs' := wz_broad_grains_initialization.tube_axis_coord_error e hs (z := z) 2
  have ht' := wz_broad_grains_initialization.tube_axis_coord_error e ht (z := z) 2
  have herr : |c - (t-s) * e v 2| < 2*d := by
    have he : c - (t-s) * e v 2 =
        (e (q-z) 2 - (e (x-z) 2 + t * e v 2)) -
          (e (p-z) 2 - (e (x-z) 2 + s * e v 2)) := by rw [hep, heq]; ring
    rw [he]
    exact (abs_sub _ _).trans_lt (by linarith)
  have hc' : c ≤ |c - (t-s) * e v 2| + |(t-s) * e v 2| := by
    have hh := abs_sub_abs_le_abs_sub c ((t-s) * e v 2)
    rw [abs_of_pos hc] at hh
    linarith
  rw [abs_mul] at hc'
  have hh := mul_le_mul_of_nonneg_right hst (abs_nonneg (e v 2))
  nlinarith

/-- The portion of a crossing tube in the central ball belongs to its prism. -/
lemma Crosses.ball_subset {d a b c : ℝ} {x v z : V} {e : V ≃ₗᵢ[ℝ] V}
    (hc : 0 < c) (h : Crosses d a b c x v z e) :
    T d x v ∩ ball z (c/2) ⊆ P a b c z e := by
  rintro p ⟨hpT, hpB⟩
  apply interior_subset (h.slab_subset hc ⟨hpT, ?_⟩)
  have hh := wz_move_two_long_grains_gain.abs_coord_le_norm (e (p-z)) 2
  rw [e.norm_map, ← dist_eq_norm] at hh
  exact hh.trans_lt hpB

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
