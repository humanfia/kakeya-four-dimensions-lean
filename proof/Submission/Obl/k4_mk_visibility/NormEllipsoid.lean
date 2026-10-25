import Mathlib
import ChallengeDeps

/-!
The finite-dimensional convex-geometric step in the visibility argument.
A maximal determinant frame gives the required comparison with Euclidean norm;
the volume estimate uses a small parallelepiped in the seminorm unit ball.

The maximal-frame argument is the dimension-independent version of the argument
in `WangZahlLot.Obl.wz_regular_transverse_affine_cells.ConvexFrame`; its available
theorem is restricted to dimension three. Here the dimension is arbitrary.
-/

namespace Submission.Obl.k4_mk_visibility

open Module Set MeasureTheory

private lemma compact_frame {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : IsCompact S) (v₀ : Fin n → EuclideanSpace ℝ (Fin n))
    (hv₀ : ∀ i, v₀ i ∈ S)
    (hdet₀ : (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v₀ ≠ 0) :
    ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (∀ i, b i ∈ S) ∧ ∀ x ∈ S, ∀ i, |b.repr x i| ≤ 1 := by
  classical
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hc : Continuous (fun v : Fin n → EuclideanSpace ℝ (Fin n) => |e.det v|) := by
    have hm : Continuous (fun v : Fin n → EuclideanSpace ℝ (Fin n) => e.toMatrix v) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact (e.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)
    exact hm.matrix_det.abs
  obtain ⟨v, hv, hmax⟩ := (isCompact_pi_infinite (fun _ : Fin n => hS)).exists_isMaxOn
    ⟨v₀, hv₀⟩ hc.continuousOn
  have hd : e.det v ≠ 0 := by
    exact abs_pos.mp ((abs_pos.mpr hdet₀).trans_le (hmax hv₀))
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hd)
  let b := Basis.mk hli hsp.ge
  have hb : ⇑b = v := Basis.coe_mk _ _
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hb]
    exact hv i
  · intro x hx i
    have hu : ∀ j, Function.update v i x j ∈ S := by
      intro j
      by_cases h : j = i
      · simpa [h] using hx
      · simpa [Function.update_of_ne h] using hv j
    have hreplace : e.det v * b.repr x i = e.det (Function.update v i x) :=
      congrArg (fun f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ => f x)
        (e.det_smul_mk_coord_eq_det_update hli hsp.ge i)
    have hbound : |e.det v| * |b.repr x i| ≤ |e.det v| := by
      rw [← abs_mul, hreplace]
      exact hmax hu
    exact (mul_le_mul_iff_right₀ (abs_pos.mpr hd)).mp (by simpa [mul_comm] using hbound)

/-- A continuous coercive seminorm has a basis with seminorm at
most one and coordinate functionals bounded by that seminorm. -/
theorem exists_seminorm_basis {n : ℕ} (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hp : Continuous p) (hcoerce : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ p x) :
    ∃ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (∀ i, p (b i) ≤ 1) ∧ ∀ x i, |b.repr x i| ≤ p x := by
  classical
  obtain ⟨c₀, hc₀, hdom⟩ := hcoerce
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let S := {x : EuclideanSpace ℝ (Fin n) | p x ≤ 1}
  have hSc : IsCompact S := by
    apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) c₀⁻¹).of_isClosed_subset
      (isClosed_le hp continuous_const)
    intro x hx
    change p x ≤ 1 at hx
    apply mem_closedBall_zero_iff.mpr
    simpa only [one_div] using (le_div_iff₀ hc₀).mpr
      (show ‖x‖ * c₀ ≤ 1 by nlinarith [hdom x])
  let c : Fin n → ℝ := fun i => (p (e i) + 1)⁻¹
  have hc : ∀ i, 0 < c i := fun i => inv_pos.mpr (by linarith [apply_nonneg p (e i)])
  obtain ⟨b, hb, hcoord⟩ := compact_frame hSc (fun i => c i • e i) (by
    intro i
    change p (c i • e i) ≤ 1
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (hc i)]
    dsimp [c]
    rw [inv_mul_eq_div, div_le_one (by linarith [apply_nonneg p (e i)])]
    linarith) (by
      change e.det (fun i => c i • e i) ≠ 0
      rw [AlternatingMap.map_smul_univ, e.det_self]
      simp only [smul_eq_mul, mul_one]
      exact ne_of_gt (Finset.prod_pos fun i _ => hc i))
  refine ⟨b, hb, ?_⟩
  intro x i
  by_cases hz : p x = 0
  · have hx : x = 0 := norm_eq_zero.mp (by nlinarith [hdom x, norm_nonneg x])
    simp [hx]
  · have hpx : 0 < p x := lt_of_le_of_ne (apply_nonneg p x) (Ne.symm hz)
    have hy : (p x)⁻¹ • x ∈ S := by
      change p ((p x)⁻¹ • x) ≤ 1
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpx), inv_mul_cancel₀ hz]
    have hi := hcoord ((p x)⁻¹ • x) hy i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hpx)] at hi
    simpa only [mul_one] using (inv_mul_le_iff₀ hpx).mp hi

/-- The coordinate isomorphism associated to a basis, with Euclidean target. -/
noncomputable def coordinateMap {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  b.equivFun.trans (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.equivFun.symm

lemma coordinateMap_basis {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    coordinateMap b (b i) = (EuclideanSpace.basisFun (Fin n) ℝ) i := by
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  change coordinateMap b (b i) = e i
  apply e.equivFun.injective
  change e.equivFun (e.equivFun.symm (b.equivFun (b i))) = e.equivFun (e i)
  rw [LinearEquiv.apply_symm_apply]
  simp only [Basis.equivFun_apply, Basis.repr_self]

lemma coordinateMap_repr {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.repr (coordinateMap b x) = b.repr x := by
  apply Finsupp.ext
  intro i
  change ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.equivFun (coordinateMap b x)) i = _
  simp [coordinateMap, Basis.equivFun_apply]

lemma coordinateMap_norm_le {n : ℕ} (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ x i, |b.repr x i| ≤ p x) (x : EuclideanSpace ℝ (Fin n)) :
    ‖coordinateMap b x‖ ≤ (n : ℝ) * p x := by
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have he : ∀ i, ‖e i‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one
  calc
    ‖coordinateMap b x‖ = ‖∑ i, b.repr x i • e i‖ := by
      rw [← coordinateMap_repr b x, e.sum_repr]
    _ ≤ ∑ i, ‖b.repr x i • e i‖ := norm_sum_le _ _
    _ = ∑ i, |b.repr x i| := by simp [norm_smul, he, Real.norm_eq_abs]
    _ ≤ ∑ _i : Fin n, p x := Finset.sum_le_sum (fun i _ => hb x i)
    _ = (n : ℝ) * p x := by simp

private lemma small_parallelepiped_subset {n : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ i, p (b i) ≤ 1) :
    parallelepiped (fun i => ((n : ℝ) + 1)⁻¹ • b i) ⊆ {x | p x ≤ 1} := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff _ x).mp hx
  have hr : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  calc
    p (∑ i, t i • (((n : ℝ) + 1)⁻¹ • b i)) ≤
        ∑ i, p (t i • (((n : ℝ) + 1)⁻¹ • b i)) :=
      Finset.le_sum_of_subadditive p (by simp) (map_add_le_add p) _ _
    _ ≤ ∑ _i : Fin n, ((n : ℝ) + 1)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (ht.1 i), abs_of_nonneg hr]
      calc
        t i * (((n : ℝ) + 1)⁻¹ * p (b i)) ≤ 1 * (((n : ℝ) + 1)⁻¹ * 1) :=
          mul_le_mul (ht.2 i) (mul_le_mul_of_nonneg_left (hb i) hr)
            (mul_nonneg hr (apply_nonneg p _)) zero_le_one
        _ = ((n : ℝ) + 1)⁻¹ := by ring
    _ = (n : ℝ) / ((n : ℝ) + 1) := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)

/-- Every regularized directional seminorm admits a linear map whose Euclidean
norm is controlled by the seminorm, and whose determinant times the seminorm-ball
volume has a dimension-only positive lower bound. -/
theorem exists_norm_controlled_map {n : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hp : Continuous p) (hcoerce : ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ p x) :
    ∃ A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ x, ‖A x‖ ≤ (n : ℝ) * p x) ∧
      ENNReal.ofReal (((n : ℝ) + 1)⁻¹ ^ n) ≤
        ENNReal.ofReal |LinearMap.det A| * volume {x | p x ≤ 1} := by
  obtain ⟨b, hb, hcoord⟩ := exists_seminorm_basis p hp hcoerce
  let A := coordinateMap b
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let P := parallelepiped (fun i => ((n : ℝ) + 1)⁻¹ • b i)
  have hP : P ⊆ {x | p x ≤ 1} := small_parallelepiped_subset p b hb
  have himage : A '' P = parallelepiped (fun i => ((n : ℝ) + 1)⁻¹ • e i) := by
    rw [show A '' P = (A : _ →ₗ[ℝ] _) '' P from rfl, image_parallelepiped]
    congr 1
    funext i
    exact (map_smul A _ _).trans (congrArg (fun v => ((n : ℝ) + 1)⁻¹ • v)
      (coordinateMap_basis b i))
  have hvol : volume (A '' P) = ENNReal.ofReal (((n : ℝ) + 1)⁻¹ ^ n) := by
    rw [himage, ← (EuclideanSpace.basisFun (Fin n) ℝ).addHaar_eq_volume]
    rw [Measure.addHaar_parallelepiped]
    change ENNReal.ofReal |e.det (fun i => ((n : ℝ) + 1)⁻¹ • e i)| = _
    rw [AlternatingMap.map_smul_univ, e.det_self]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one, abs_pow, abs_of_nonneg (by positivity : 0 ≤ ((n : ℝ) + 1)⁻¹)]
  refine ⟨A.toLinearMap, coordinateMap_norm_le p b hcoord, ?_⟩
  calc
    ENNReal.ofReal (((n : ℝ) + 1)⁻¹ ^ n) = volume (A '' P) := hvol.symm
    _ ≤ volume (A '' {x | p x ≤ 1}) := measure_mono (image_mono hP)
    _ = ENNReal.ofReal |LinearMap.det A.toLinearMap| * volume {x | p x ≤ 1} :=
      Measure.addHaar_image_linearMap _ _ _

end Submission.Obl.k4_mk_visibility
