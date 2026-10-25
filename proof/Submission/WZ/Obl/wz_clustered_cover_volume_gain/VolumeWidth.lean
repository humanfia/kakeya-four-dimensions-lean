-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.VolumeWidth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BodyMultiplicity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Module MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (frameLinear frameAffine frameAffine_apply frameLinear_symm_coord frameAffine_volume
    exists_bounded_frame_of_ball coordinateBox volume_coordinateBox)

/-- Removing a bounded multiple of one edge produces a comparably long fibre
of a linear projection inside the convex hull of three points. -/
theorem convex_kernel_pair {U : Set Space} (hU : Convex ℝ U) {x v w : Space}
    (hx : x ∈ U) (hv : x + v ∈ U) (hw : x + w ∈ U)
    {t : ℝ} (ht : |t| ≤ 1) (ℓ : Space →ₗ[ℝ] ℝ) (hz : ℓ (v - t • w) = 0) :
    ∃ p ∈ U, ∃ q ∈ U, ℓ (p - q) = 0 ∧ ‖v - t • w‖ ≤ 2 * dist p q := by
  have hseg (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) : x + s • w ∈ U := by
    convert hU hx hw (sub_nonneg.mpr hs1) hs (by ring : 1 - s + s = 1) using 1 <;> module
  rcases le_total 0 t with ht0 | ht0
  · refine ⟨x + v, hv, x + t • w, hseg t ht0 ((le_abs_self t).trans ht), ?_, ?_⟩
    · simpa only [add_sub_add_left_eq_sub] using hz
    · rw [dist_eq_norm, add_sub_add_left_eq_sub]
      linarith [norm_nonneg (v - t • w)]
  · let p : Space := (1 / 2 : ℝ) • (x + v) + (1 / 2 : ℝ) • (x + (-t) • w)
    have hp : p ∈ U := hU hv
      (hseg (-t) (neg_nonneg.mpr ht0) (by simpa [abs_of_nonpos ht0] using ht))
      (by norm_num) (by norm_num) (by norm_num)
    have hdiff : p - x = (1 / 2 : ℝ) • (v - t • w) := by dsimp [p]; module
    refine ⟨p, hp, x, hx, ?_, ?_⟩
    · rw [hdiff, map_smul, hz, smul_zero]
    · rw [dist_eq_norm, hdiff, norm_smul]
      norm_num
      linarith

theorem frameLinear_det (b : Basis (Fin 3) ℝ Space) :
    LinearMap.det (frameLinear b : Space →ₗ[ℝ] Space) =
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det b := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  have h := e.toBasis.det_comp (frameLinear b : Space →ₗ[ℝ] Space) e.toBasis
  simp only [Basis.det_self, mul_one] at h
  rw [← h]
  congr 1
  funext i
  simp [WangZahlLot.Obl.wz_regular_transverse_affine_cells.frameLinear, e]

/-- The bounded coordinates of a maximal frame give a sharp enough outer-volume bound. -/
theorem volume_le_frame_det {U : Set Space} (x : Space) (b : Basis (Fin 3) ℝ Space)
    (hcoord : ∀ p ∈ U, ∀ i, |b.repr (p - x) i| ≤ 1) :
    volume U ≤ ENNReal.ofReal
      (8 * |(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det b|) := by
  have hsub : U ⊆ frameAffine x b '' coordinateBox (fun _ => 1) := by
    intro p hp
    refine ⟨(frameLinear b).symm (p - x), ?_, ?_⟩
    · intro i
      rw [frameLinear_symm_coord]
      exact hcoord p hp i
    · rw [frameAffine_apply, LinearEquiv.apply_symm_apply, sub_add_cancel]
  calc
    _ ≤ volume (frameAffine x b '' coordinateBox (fun _ => 1)) := measure_mono hsub
    _ = _ := by
      rw [frameAffine_volume, volume_coordinateBox _ (fun _ => zero_le_one), frameLinear_det]
      simp only [Finset.prod_const_one, mul_one]
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      ring

theorem standard_det_le_product_norm (v : Fin 3 → Space) :
    |(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det v| ≤ ∏ i, ‖v i‖ := by
  let e := EuclideanSpace.basisFun (Fin 3) ℝ
  letI : Fact (finrank ℝ Space = 3) := ⟨by simp [Space]⟩
  have h := e.toBasis.orientation.abs_volumeForm_apply_le v
  rw [e.toBasis.orientation.volumeForm_robust e rfl] at h
  exact h

theorem standard_det_remove_pivot (v : Fin 3 → Space) (t : Fin 3 → ℝ) (i : Fin 3) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
      (fun j => if j = i then v j else v j - t j • v i) =
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det v := by
  fin_cases i <;>
    simp [Basis.det_apply, Matrix.det_fin_three, Basis.toMatrix_apply,
      Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] <;> ring

/-- A convex body in the unit ball has middle width bounded below by the square
root of its volume. This supplies the width needed by the body estimate from
the Jacobian volume weight alone. -/
theorem wideSection_of_volume {U : Set Space} (hUc : IsCompact U) (hU : Convex ℝ U)
    {x : Space} {s w : ℝ} (hs : 0 < s) (hball : ball x s ⊆ U)
    (hbound : U ⊆ closedBall (0 : Space) 1) (hw : 0 < w)
    (hvol : ENNReal.ofReal w ≤ volume U) : WideSection U (Real.sqrt w / 16) := by
  classical
  obtain ⟨b, hb, hcoord⟩ := exists_bounded_frame_of_ball hUc hs hball
  have hx : x ∈ U := hball (mem_ball_self hs)
  have hbnorm : ∀ i, ‖b i‖ ≤ 2 := by
    intro i
    have hxnorm : ‖x‖ ≤ 1 := by simpa using hbound hx
    have hinorm : ‖x + b i‖ ≤ 1 := by simpa using hbound (hb i)
    have hi := norm_sub_le (x + b i) x
    rw [add_sub_cancel_left] at hi
    linarith
  have hdet : w ≤ 8 * |(EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det b| :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
      (hvol.trans (volume_le_frame_det x b hcoord))
  intro ℓ
  by_contra hfail
  push Not at hfail
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin 3 => |ℓ (b i)|) (by simp)
  let t : Fin 3 → ℝ := fun j => ℓ (b j) / ℓ (b i)
  have ht : ∀ j, |t j| ≤ 1 := by
    intro j
    by_cases hi0 : ℓ (b i) = 0
    · simp [t, hi0]
    · dsimp [t]
      rw [abs_div, div_le_one (abs_pos.mpr hi0)]
      exact hi j (Finset.mem_univ j)
  have hz : ∀ j, ℓ (b j - t j • b i) = 0 := by
    intro j
    rw [map_sub, map_smul]
    dsimp [t]
    by_cases hi0 : ℓ (b i) = 0
    · have hj0 : ℓ (b j) = 0 := abs_eq_zero.mp
        (le_antisymm (by simpa [hi0] using hi j (Finset.mem_univ j)) (abs_nonneg _))
      simp [hi0, hj0]
    · simp only [div_mul_cancel₀ _ hi0, sub_self]
  have hsmall : ∀ j, ‖b j - t j • b i‖ ≤ 2 * (Real.sqrt w / 16) := by
    intro j
    obtain ⟨p, hp, q, hq, hpq, hd⟩ := convex_kernel_pair hU hx (hb j) (hb i) (ht j) ℓ (hz j)
    have hh := hfail p hp q hq hpq
    linarith
  let v : Fin 3 → Space := fun j => if j = i then b j else b j - t j • b i
  have hv : ∀ j, ‖v j‖ ≤ if j = i then 2 else 2 * (Real.sqrt w / 16) := by
    intro j
    by_cases hj : j = i
    · simpa [v, hj] using hbnorm j
    · simpa [v, hj] using hsmall j
  have hp : (∏ j, ‖v j‖) ≤ 8 * (Real.sqrt w / 16) ^ 2 := by
    calc
      _ ≤ ∏ j : Fin 3, (if j = i then 2 else 2 * (Real.sqrt w / 16)) := by
        gcongr with j
        exact hv j
      _ = _ := by fin_cases i <;> simp [Fin.prod_univ_three] <;> ring
  have hh := (standard_det_le_product_norm v).trans hp
  rw [show (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det v =
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det b from
        standard_det_remove_pivot b t i] at hh
  nlinarith [Real.sq_sqrt hw.le]

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
