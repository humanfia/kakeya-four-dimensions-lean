-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.AxialGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_broad_grains_initialization.DirectionClass
import Submission.WZ.Obl.wz_move_two_long_grains_gain.CrossBox

/-! Axial coordinates of points in a fine tube. -/

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open Set MeasureTheory Metric
open wz_move_two_long_grains_gain (abs_coord_le_norm)

lemma frame_last_inner {u : V} {e : V ≃ₗᵢ[ℝ] V}
    (he : e u = EuclideanSpace.single 2 (1 : ℝ)) (p : V) :
    e p 2 = inner ℝ u p := by
  calc
    _ = inner ℝ (e u) (e p) := by rw [he, EuclideanSpace.inner_single_left]; simp
    _ = _ := e.inner_map_map u p

lemma volume_frame_level (e : V ≃ₗᵢ[ℝ] V) (j : Fin 3) (t : ℝ) :
    volume {p : V | e p j = t} = 0 := by
  have hm : MeasurableSet {p : V | p j = t} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hcoord : volume {p : V | p j = t} = 0 := by
    have hm' : MeasurableSet {p : Fin 3 → ℝ | p j = t} :=
      measurableSet_eq_fun (measurable_pi_apply j) measurable_const
    have hh := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage hm'.nullMeasurableSet
    change volume {p : V | p j = t} = volume {p : Fin 3 → ℝ | p j = t} at hh
    rw [hh]
    exact Measure.pi_hyperplane (fun _ : Fin 3 => (volume : Measure ℝ)) j t
  exact (e.measurePreserving.measure_preimage hm.nullMeasurableSet).trans hcoord

lemma volume_inner_level {u : V} (hu : ‖u‖ = 1) (t : ℝ) :
    volume ((fun p : V => inner ℝ u p) ⁻¹' {t}) = 0 := by
  obtain ⟨e, he⟩ := wz_broad_grains_initialization.frame_last_of_unit hu
  have hh : ((fun p : V => inner ℝ u p) ⁻¹' {t}) = {p : V | e p 2 = t} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq, frame_last_inner he]
  rw [hh]
  exact volume_frame_level e 2 t

/-- Projecting the difference of two tube points onto the axis introduces only
a bounded transverse error, in every orthonormal coordinate. -/
lemma tube_projected_coordinate_error {d : ℝ} {x v p q : V} (hv : ‖v‖ = 1)
    (e : V ≃ₗᵢ[ℝ] V) (hp : p ∈ T d x v) (hq : q ∈ T d x v) (j : Fin 3) :
    |e (q-p) j - inner ℝ v (q-p) * e v j| < 4*d := by
  obtain ⟨s, _, hs⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hp
  obtain ⟨t, _, ht⟩ := wz_balanced_cluster_cover.exists_param_of_mem_tube hq
  let r : V := (q-(x+t•v)) - (p-(x+s•v))
  have hr : ‖r‖ < 2*d := (norm_sub_le _ _).trans_lt (by linarith)
  have heq : q-p = (t-s) • v + r := by dsimp [r]; module
  have hi : inner ℝ v (q-p) = (t-s) + inner ℝ v r := by
    rw [heq, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  have hj : e (q-p) j = (t-s)*e v j + e r j := by
    rw [heq, map_add, map_smul]
    rfl
  have hvj : |e v j| ≤ 1 := by simpa only [e.norm_map, hv] using abs_coord_le_norm (e v) j
  have hrj : |e r j| ≤ ‖r‖ := by simpa only [e.norm_map] using abs_coord_le_norm (e r) j
  have hir : |inner ℝ v r| ≤ ‖r‖ := by simpa only [hv, one_mul] using abs_real_inner_le_norm v r
  rw [hj, hi]
  have halg : (t-s)*e v j + e r j - ((t-s) + inner ℝ v r) * e v j =
      e r j - inner ℝ v r * e v j := by ring
  rw [halg]
  calc
    _ ≤ |e r j| + |inner ℝ v r * e v j| := abs_sub _ _
    _ = |e r j| + |inner ℝ v r| * |e v j| := by rw [abs_mul]
    _ ≤ ‖r‖ + ‖r‖ * 1 := add_le_add hrj (mul_le_mul hir hvj (abs_nonneg _) (norm_nonneg _))
    _ < 4*d := by linarith

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
