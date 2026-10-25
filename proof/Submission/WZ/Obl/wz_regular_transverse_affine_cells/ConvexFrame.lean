-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.ConvexFrame.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Types

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open Module Set

/-- A maximal-volume frame bounds every coordinate of a compact set. This supplies
an elementary affine normalization without invoking a John ellipsoid theorem. -/
lemma exists_bounded_frame {U : Set E} (hUc : IsCompact U) (x : E)
    (v₀ : Fin 3 → E) (hv₀ : ∀ i, x + v₀ i ∈ U)
    (hdet₀ : (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det v₀ ≠ 0) :
    ∃ b : Basis (Fin 3) ℝ E,
      (∀ i, x + b i ∈ U) ∧ (∀ q ∈ U, ∀ i, |b.repr (q - x) i| ≤ 1) := by
  classical
  let e := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let V : Set E := (fun q : E => q - x) '' U
  let Q : Set (Fin 3 → E) := {v | ∀ i, v i ∈ V}
  have hVc : IsCompact V := hUc.image (by fun_prop)
  have hQc : IsCompact Q := isCompact_pi_infinite (fun _ => hVc)
  have hv₀Q : v₀ ∈ Q := by
    intro i
    exact ⟨x + v₀ i, hv₀ i, by abel_nf⟩
  have hcont : Continuous (fun v : Fin 3 → E => |e.det v|) := by
    have hm : Continuous (fun v : Fin 3 → E => e.toMatrix v) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (e.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)
    exact hm.matrix_det.abs
  obtain ⟨v, hv, hmax⟩ := hQc.exists_isMaxOn ⟨v₀, hv₀Q⟩ hcont.continuousOn
  have hvne : e.det v ≠ 0 := by
    have hmax₀ := hmax hv₀Q
    have hpos : 0 < |e.det v₀| := abs_pos.mpr hdet₀
    exact (abs_pos.mp (hpos.trans_le hmax₀))
  obtain ⟨hli, hspan⟩ := (e.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hvne)
  let b : Basis (Fin 3) ℝ E := Basis.mk hli hspan.ge
  have hb : ⇑b = v := Basis.coe_mk _ _
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hb]
    obtain ⟨q, hq, he⟩ := hv i
    rw [← he]
    simpa only [add_sub_cancel] using hq
  · intro q hq i
    have hupdate : Function.update v i (q - x) ∈ Q := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self]
        exact ⟨q, hq, rfl⟩
      · simpa only [Function.update_of_ne hji] using hv j
    have hbound := hmax hupdate
    have hcoord : e.det v * b.repr (q - x) i = e.det (Function.update v i (q - x)) := by
      exact congrArg (fun f : E →ₗ[ℝ] ℝ => f (q - x))
        (e.det_smul_mk_coord_eq_det_update hli hspan.ge i)
    have habs : |e.det v| * |b.repr (q - x) i| ≤ |e.det v| := by
      rw [← abs_mul, hcoord]
      exact hbound
    have hpos := abs_pos.mpr hvne
    nlinarith

/-- A ball supplies the initial nondegenerate frame used in `exists_bounded_frame`. -/
lemma exists_bounded_frame_of_ball {U : Set E} (hUc : IsCompact U) {x : E} {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball x r ⊆ U) :
    ∃ b : Basis (Fin 3) ℝ E,
      (∀ i, x + b i ∈ U) ∧ (∀ q ∈ U, ∀ i, |b.repr (q - x) i| ≤ 1) := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  apply exists_bounded_frame hUc x (fun i => (r / 2) • e i)
  · intro i
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, e.norm_eq_one,
      mul_one, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 2)]
    linarith
  · change e.toBasis.det (fun i => (r / 2) • e i) ≠ 0
    rw [AlternatingMap.map_smul_univ]
    have he : e.toBasis.det e = 1 := by
      rw [← e.coe_toBasis]
      exact e.toBasis.det_self
    rw [he]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    positivity

/-- The linear coordinate map from the standard Euclidean frame to a chosen frame. -/
noncomputable def frameLinear (b : Basis (Fin 3) ℝ E) : E ≃ₗ[ℝ] E :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.equivFun.trans b.equivFun.symm

/-- Translate the frame to its physical base point. -/
noncomputable def frameAffine (x : E) (b : Basis (Fin 3) ℝ E) : E ≃ᵃ[ℝ] E :=
  (frameLinear b).toAffineEquiv.trans (AffineEquiv.vaddConst ℝ x)

lemma frameAffine_apply (x : E) (b : Basis (Fin 3) ℝ E) (q : E) :
    frameAffine x b q = frameLinear b q + x := rfl

lemma frameLinear_symm_coord (b : Basis (Fin 3) ℝ E) (q : E) (i : Fin 3) :
    (frameLinear b).symm q i = b.repr q i := by
  have hstd (p : E) : (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.equivFun p i = p i := by
    simp [EuclideanSpace.basisFun_repr]
  rw [← hstd]
  simp [frameLinear, Basis.equivFun_apply]

lemma frameAffine_volume (x : E) (b : Basis (Fin 3) ℝ E) (Q : Set E) :
    MeasureTheory.volume (frameAffine x b '' Q) =
      ENNReal.ofReal |LinearMap.det (frameLinear b : E →ₗ[ℝ] E)| * MeasureTheory.volume Q := by
  have he : frameAffine x b '' Q =
      (fun y : E => y + x) '' ((frameLinear b : E →ₗ[ℝ] E) '' Q) := by
    rw [Set.image_image]
    rfl
  rw [he, Set.image_add_right, MeasureTheory.measure_preimage_add_right,
    MeasureTheory.Measure.addHaar_image_linearMap]

lemma frameAffine_jacobian_pos (b : Basis (Fin 3) ℝ E) :
    0 < |LinearMap.det (frameLinear b : E →ₗ[ℝ] E)| :=
  abs_pos.mpr (isUnit_iff_ne_zero.mp (frameLinear b).isUnit_det')

/-- The bounded-coordinate property gives a uniform outer Euclidean ball after the
frame change. -/
lemma subset_frameAffine_ball {U : Set E} (x : E) (b : Basis (Fin 3) ℝ E)
    (hb : ∀ q ∈ U, ∀ i, |b.repr (q - x) i| ≤ 1) :
    U ⊆ frameAffine x b '' Metric.closedBall 0 2 := by
  intro p hp
  let q := (frameLinear b).symm (p - x)
  have hcoord (i : Fin 3) : |q i| ≤ 1 := by
    dsimp [q]
    rw [frameLinear_symm_coord]
    exact hb p hp i
  have hcoord2 (i : Fin 3) : (q i) ^ 2 ≤ 1 := by
    have h := pow_le_pow_left₀ (abs_nonneg (q i)) (hcoord i) 2
    simpa only [sq_abs, one_pow] using h
  have hnorm2 : ‖q‖ ^ 2 ≤ 3 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    linarith [hcoord2 0, hcoord2 1, hcoord2 2]
  have hnorm : ‖q‖ ≤ 2 := by nlinarith [norm_nonneg q]
  refine ⟨q, by simpa using hnorm, ?_⟩
  rw [frameAffine_apply]
  simp [q]

lemma frameLinear_apply (b : Basis (Fin 3) ℝ E) (q : E) :
    frameLinear b q = ∑ i, q i • b i := by
  simp [frameLinear, Basis.equivFun_symm_apply]

/-- The same frame contains a fixed inner cube when its vertices lie in a convex set. -/
lemma frameAffine_inner_cube_subset {U : Set E} (hU : Convex ℝ U) (x : E) (hx : x ∈ U)
    (b : Basis (Fin 3) ℝ E) (hb : ∀ i, x + b i ∈ U) :
    frameAffine x b '' {q : E | ∀ i, 0 ≤ q i ∧ q i ≤ 1 / 4} ⊆ U := by
  rintro _ ⟨q, hq, rfl⟩
  let w : Fin 4 → ℝ := ![1 - q 0 - q 1 - q 2, q 0, q 1, q 2]
  let z : Fin 4 → E := ![x, x + b 0, x + b 1, x + b 2]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · dsimp [w]
      linarith [(hq 0).2, (hq 1).2, (hq 2).2]
    · exact (hq 0).1
    · exact (hq 1).1
    · exact (hq 2).1
  have hsum : ∑ i, w i = 1 := by
    rw [Fin.sum_univ_four]
    dsimp [w]
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 4)), z i ∈ U := by
    intro i _
    fin_cases i
    · exact hx
    · exact hb 0
    · exact hb 1
    · exact hb 2
  have hmem := hU.sum_mem hw hsum hz
  rw [Fin.sum_univ_four] at hmem
  dsimp [w, z] at hmem
  rw [frameAffine_apply, frameLinear_apply, Fin.sum_univ_three]
  convert hmem using 1
  module

/-- A compact convex body with an interior ball admits a frame normalization between
one fixed cube and one fixed ball, with an exact positive affine volume factor. -/
lemma exists_affine_normalization {U : Set E} (hUc : IsCompact U) (hU : Convex ℝ U)
    {x : E} {r : ℝ} (hr : 0 < r) (hball : Metric.ball x r ⊆ U) :
    ∃ (f : AffineEquiv ℝ E E) (D : ℝ), 0 < D ∧ f 0 = x ∧
      f '' {q : E | ∀ i, 0 ≤ q i ∧ q i ≤ 1 / 4} ⊆ U ∧
      U ⊆ f '' Metric.closedBall 0 2 ∧
      ∀ Q : Set E, MeasureTheory.volume (f '' Q) = ENNReal.ofReal D * MeasureTheory.volume Q := by
  obtain ⟨b, hb, hbcoord⟩ := exists_bounded_frame_of_ball hUc hr hball
  refine ⟨frameAffine x b, |LinearMap.det (frameLinear b : E →ₗ[ℝ] E)|,
    frameAffine_jacobian_pos b, ?_, ?_, subset_frameAffine_ball x b hbcoord, frameAffine_volume x b⟩
  · rw [frameAffine_apply, map_zero, zero_add]
  · exact frameAffine_inner_cube_subset hU x (hball (Metric.mem_ball_self hr)) b hb

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
