-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.AngularCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_broad_grains_initialization.DirectionClass
import Submission.WZ.Obl.wz_broad_grains_initialization.CubeGeometry
import Submission.WZ.Obl.wz_move_two_long_grains_gain.CrossBox
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry

/-! Pointwise angular counts from the convex Katz--Tao condition. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set Metric
open wz_move_two_long_grains_gain (abs_coord_le_norm)

/-- Points of one unit tube differ in a frame coordinate by at most its
axial change and two tube radii. -/
lemma tube_coordinate_difference {d : ℝ} {x v p q : V}
    (e : V ≃ₗᵢ[ℝ] V) (hp : p ∈ T d x v) (hq : q ∈ T d x v) (j : Fin 3) :
    |e (q-p) j| ≤ 2 * d + |e v j| := by
  obtain ⟨s, hsI, hs⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  obtain ⟨t, htI, ht⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hq
  have hs' := wz_broad_grains_initialization.tube_axis_coord_error e hs (z := p) j
  have ht' := wz_broad_grains_initialization.tube_axis_coord_error e ht (z := p) j
  have hst : |t-s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hsI.1, hsI.2, htI.1, htI.2]
  have herr : |e (q-p) j - (t-s) * e v j| < 2 * d := by
    have hp0 : e (p-p) j = 0 := by simp
    rw [hp0] at hs'
    have he : e (q-p) j - (t-s) * e v j =
        (e (q-p) j - (e (x-p) j + t * e v j)) +
          (e (x-p) j + s * e v j) := by ring
    rw [he]
    have hh := abs_add_le (e (q-p) j - (e (x-p) j + t * e v j))
      (e (x-p) j + s * e v j)
    simp only [zero_sub, abs_neg] at hs'
    linarith
  calc
    |e (q-p) j| ≤ |e (q-p) j - (t-s) * e v j| + |(t-s) * e v j| := by
      linarith [abs_sub_abs_le_abs_sub (e (q-p) j) ((t-s) * e v j)]
    _ ≤ 2 * d + |e v j| := by
      rw [abs_mul]
      nlinarith [abs_nonneg (e v j)]

/-- All tubes through a point in an angular cap lie in a common small-volume box. -/
lemma point_cap_container {d r : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hdr : d ≤ r)
    (p u : V) (hu : ‖u‖ = 1) :
    ∃ W : Set V, Convex ℝ W ∧ μ W = O (216 * r ^ 2) ∧
      ∀ x v : V, ‖v‖ = 1 → p ∈ T d x v →
        min ‖v-u‖ ‖v+u‖ ≤ r → T d x v ⊆ W := by
  have hr : 0 < r := hd.trans_le hdr
  obtain ⟨e, he⟩ := wz_broad_grains_initialization.frame_last_of_unit hu
  refine ⟨P (6*r) (6*r) 6 p e,
    wz_two_scale_flat_box_estimate.box_convex _ _ _ _ _, ?_, ?_⟩
  · calc
      _ = O ((6*r)*(6*r)*6) := wz_two_scale_flat_box_estimate.box_volume
        (by positivity) (by positivity) (by norm_num) p e
      _ = _ := by congr 1; ring
  · intro x v hv hp hangle q hq
    have hshort (j : Fin 3) (hj : j ≠ 2) : |e v j| ≤ r := by
      have huj : e u j = 0 := by rw [he]; simp [hj]
      have hmin : |e v j| ≤ min ‖v-u‖ ‖v+u‖ := by
        apply le_min
        · have : |e (v-u) j| ≤ ‖v-u‖ := by
            simpa only [LinearIsometryEquiv.norm_map] using abs_coord_le_norm (e (v-u)) j
          simpa only [map_sub, PiLp.sub_apply, huj, sub_zero] using this
        · have : |e (v+u) j| ≤ ‖v+u‖ := by
            simpa only [LinearIsometryEquiv.norm_map] using abs_coord_le_norm (e (v+u)) j
          simpa only [map_add, PiLp.add_apply, huj, add_zero] using this
      exact hmin.trans hangle
    have hlong : |e v 2| ≤ 1 := by
      simpa only [LinearIsometryEquiv.norm_map, hv] using abs_coord_le_norm (e v) 2
    refine ⟨?_, ?_, ?_⟩
    · change |e (q-p) 0| ≤ _
      linarith [tube_coordinate_difference e hp hq 0, hshort 0 (by decide)]
    · change |e (q-p) 1| ≤ _
      linarith [tube_coordinate_difference e hp hq 1, hshort 1 (by decide)]
    · change |e (q-p) 2| ≤ _
      linarith [tube_coordinate_difference e hp hq 2]

/-- The pointwise count in a cap costs two powers of its radius. -/
theorem point_cap_count {d r m : ℝ} {n : ℕ} {x v : Fin n → V}
    (hd : 0 < d) (hd1 : d ≤ 1) (hdr : d ≤ r) (hm : 0 ≤ m)
    (hv : ∀ i, ‖v i‖ = 1)
    (hK : ∀ W : Set V, Convex ℝ W →
      O (q n {i | T d (x i) (v i) ⊆ W} * d ^ 2) ≤ O m * μ W)
    (p u : V) (hu : ‖u‖ = 1) :
    q n {i | p ∈ T d (x i) (v i) ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} * d ^ 2 ≤
      216 * m * r ^ 2 := by
  obtain ⟨W, hW, hvol, hcontain⟩ := point_cap_container hd hd1 hdr p u hu
  have hcount : q n {i | p ∈ T d (x i) (v i) ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} ≤
      q n {i | T d (x i) (v i) ⊆ W} := by
    exact_mod_cast Set.ncard_le_ncard (show
      {i | p ∈ T d (x i) (v i) ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} ⊆
      {i | T d (x i) (v i) ⊆ W} from fun i hi => hcontain _ _ (hv i) hi.1 hi.2)
  have hbound : O (q n {i | p ∈ T d (x i) (v i) ∧ min ‖v i-u‖ ‖v i+u‖ ≤ r} * d ^ 2) ≤
      O (216 * m * r ^ 2) := by
    calc
      _ ≤ O (q n {i | T d (x i) (v i) ⊆ W} * d ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcount (sq_nonneg d))
      _ ≤ O m * μ W := hK W hW
      _ = _ := by rw [hvol, ← ENNReal.ofReal_mul hm]; congr 1; ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
