import Mathlib

/-
Adapted from: here:o003
Original proofs by session x0004 in this LOT tree, obligation o003,
Submission/Obl/k4_multilinear_kakeya/Frame.lean.
-/

namespace Submission.Lib.K4PolynomialGeometry

open Module Set

/-- A compact set containing a basis has a basis whose coordinate functionals are bounded by one
on the set. Choose a tuple maximizing its absolute determinant and replace one vector at a time. -/
theorem exists_compact_bounded_basis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℝ E) {U : Set E} (hU : IsCompact U)
    (b₀ : Basis ι ℝ E) (hb₀ : ∀ i, b₀ i ∈ U) :
    ∃ b : Basis ι ℝ E, (∀ i, b i ∈ U) ∧ ∀ x ∈ U, ∀ i, |b.repr x i| ≤ 1 := by
  classical
  let S : Set (ι → E) := Set.univ.pi fun _ => U
  have hS : IsCompact S := isCompact_univ_pi fun _ => hU
  have hb₀' : (fun i => b₀ i) ∈ S := Set.mem_univ_pi.mpr hb₀
  have hm : Continuous (fun v : ι → E => e.toMatrix v) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (e.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)
  have hd : Continuous (fun v : ι → E => |e.det v|) := by
    simpa only [Basis.det_apply] using hm.matrix_det.abs
  obtain ⟨v, hv, hmax⟩ := hS.exists_isMaxOn ⟨b₀, hb₀'⟩ hd.continuousOn
  have hvdet : e.det v ≠ 0 := by
    intro hzero
    have h : |e.det b₀| ≤ |e.det v| := hmax hb₀'
    rw [hzero, abs_zero] at h
    exact (e.isUnit_det b₀).ne_zero (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  obtain ⟨hli, hspan⟩ := (e.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hvdet)
  let b : Basis ι ℝ E := Basis.mk hli hspan.ge
  refine ⟨b, ?_, ?_⟩
  · intro i
    simpa only [b, Basis.mk_apply] using Set.mem_univ_pi.mp hv i
  · intro x hx i
    have hup : Function.update v i x ∈ S := by
      apply Set.mem_univ_pi.mpr
      intro j
      by_cases hji : j = i
      · simpa [hji] using hx
      · simpa [Function.update, hji] using Set.mem_univ_pi.mp hv j
    have hcoord : e.det v * b.repr x i = e.det (Function.update v i x) := by
      have h := congrArg (fun L : E →ₗ[ℝ] ℝ => L x)
        (e.det_smul_mk_coord_eq_det_update hli hspan.ge i)
      simpa [b, MultilinearMap.toLinearMap_apply] using h
    have hbound : |e.det (Function.update v i x)| ≤ |e.det v| := hmax hup
    rw [← hcoord, abs_mul] at hbound
    exact (mul_le_mul_iff_right₀ (abs_pos.mpr hvdet)).mp (by simpa using hbound)

noncomputable def frameEquiv {n : ℕ} (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.equiv b (Equiv.refl _)

lemma frameEquiv_basis {n : ℕ} (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (i : Fin n) : frameEquiv b ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i) = b i := by
  unfold frameEquiv
  exact Basis.equiv_apply _ _ _ _

lemma frameEquiv_apply {n : ℕ} (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : frameEquiv b x = ∑ i, x i • b i := by
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have h := congrArg (frameEquiv b) (e.sum_repr x)
  simp only [map_sum, map_smul] at h
  simp_rw [show ∀ i, frameEquiv b (e i) = b i from frameEquiv_basis b] at h
  exact h.symm

lemma frameEquiv_symm_coord {n : ℕ} (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (frameEquiv b).symm x i = b.repr x i := by
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hlin : (e.coord i).comp (frameEquiv b).symm.toLinearMap = b.coord i := by
    apply b.ext
    intro j
    have hB : frameEquiv b (e j) = b j := frameEquiv_basis b j
    have hsymm : (frameEquiv b).symm (b j) = e j := by
      rw [← hB, LinearEquiv.symm_apply_apply]
    change (e.coord i) ((frameEquiv b).symm (b j)) = (b.coord i) (b j)
    rw [hsymm]
    simp
  exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ => L x) hlin

lemma frameEquiv_det {n : ℕ} (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    LinearMap.det (frameEquiv b).toLinearMap =
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det b := by
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have h := e.det_comp (frameEquiv b).toLinearMap e
  have hB : (fun i => frameEquiv b (e i)) = b := by
    funext i
    exact frameEquiv_basis b i
  simpa only [Function.comp_def, LinearEquiv.coe_coe, hB, Basis.det_self, mul_one] using h.symm

def coordinateCube {n : ℕ} (s : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun _ => Set.Icc (-s) s)

lemma volume_coordinateCube {n : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    MeasureTheory.volume (coordinateCube (n := n) s) = ENNReal.ofReal ((2 * s) ^ n) := by
  open MeasureTheory in
  rw [coordinateCube, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).nullMeasurableSet,
    volume_pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, show s + s = 2 * s by ring,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity)]

lemma frameEquiv_cube_superset {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hcoord : ∀ x ∈ U, ∀ i, |b.repr x i| ≤ 1) :
    U ⊆ frameEquiv b '' coordinateCube 1 := by
  intro x hx
  refine ⟨(frameEquiv b).symm x, ?_, (frameEquiv b).apply_symm_apply x⟩
  apply Set.mem_univ_pi.mpr
  intro i
  rw [frameEquiv_symm_coord]
  exact abs_le.mp (hcoord x hx i)

open MeasureTheory in
lemma volume_le_frame_cube {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hcoord : ∀ x ∈ U, ∀ i, |b.repr x i| ≤ 1) :
    volume U ≤ ENNReal.ofReal |LinearMap.det (frameEquiv b).toLinearMap| *
      ENNReal.ofReal ((2 : ℝ) ^ n) := by
  calc
    volume U ≤ volume (frameEquiv b '' coordinateCube 1) :=
      measure_mono (frameEquiv_cube_superset b hcoord)
    _ = _ := by
      change volume ((frameEquiv b).toLinearMap '' coordinateCube 1) = _
      rw [Measure.addHaar_image_linearMap volume (frameEquiv b).toLinearMap,
        volume_coordinateCube (by norm_num : (0 : ℝ) ≤ 1), mul_one]

open MeasureTheory in
lemma det_frame_ge_volume_div {n : ℕ}
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hcoord : ∀ x ∈ U, ∀ i, |b.repr x i| ≤ 1) :
    (volume U).toReal / (2 : ℝ) ^ n ≤ |LinearMap.det (frameEquiv b).toLinearMap| := by
  have h := ENNReal.toReal_mono (by finiteness) (volume_le_frame_cube b hcoord)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (by positivity)] at h
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr h

lemma frameEquiv_cube_subset {n : ℕ} (hn : 0 < n)
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : Convex ℝ U) (hbal : Balanced ℝ U) (hb : ∀ i, b i ∈ U) :
    frameEquiv b '' coordinateCube ((n : ℝ)⁻¹) ⊆ U := by
  rintro _ ⟨x, hx, rfl⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx' (i : Fin n) : |x i| ≤ (n : ℝ)⁻¹ := by
    exact abs_le.mpr (Set.mem_univ_pi.mp hx i)
  have hscaled (i : Fin n) : ((n : ℝ) * x i) • b i ∈ U := by
    apply hbal.smul_mem _ (hb i)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hn0]
    calc
      (n : ℝ) * |x i| ≤ (n : ℝ) * (n : ℝ)⁻¹ := mul_le_mul_of_nonneg_left (hx' i) hn0.le
      _ = 1 := mul_inv_cancel₀ hn0.ne'
  have hsum : (∑ _i : Fin n, (n : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn0.ne'
  have hmem := hU.sum_mem (t := Finset.univ) (w := fun _ : Fin n => (n : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.mpr hn0.le) hsum (fun i _ => hscaled i)
  convert hmem using 1
  rw [frameEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, ← mul_assoc, inv_mul_cancel₀ hn0.ne', one_mul]

open MeasureTheory in
theorem compact_body_frame {n : ℕ} (hn : 0 < n) {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsCompact U) (hconv : Convex ℝ U) (hbal : Balanced ℝ U)
    (b₀ : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) (hb₀ : ∀ i, b₀ i ∈ U) :
    ∃ A : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ x ∈ U, ‖A x‖ ≤ (n : ℝ)) ∧
      ENNReal.ofReal ((2 * (n : ℝ)⁻¹) ^ n) ≤
        ENNReal.ofReal |LinearMap.det A.toLinearMap| * volume U := by
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  obtain ⟨b, hb, hcoord⟩ := exists_compact_bounded_basis e hU b₀ hb₀
  refine ⟨(frameEquiv b).symm, ?_, ?_⟩
  · intro x hx
    have hs : ‖(frameEquiv b).symm x‖ ^ 2 ≤ (n : ℝ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        (∑ i : Fin n, ((frameEquiv b).symm x i) ^ 2) ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [frameEquiv_symm_coord]
          have h := abs_le.mp (hcoord x hx i)
          nlinarith [h.1, h.2]
        _ = (n : ℝ) := by simp
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [norm_nonneg ((frameEquiv b).symm x)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hvol : ENNReal.ofReal |LinearMap.det (frameEquiv b).toLinearMap| *
        ENNReal.ofReal ((2 * (n : ℝ)⁻¹) ^ n) ≤ volume U := by
      rw [← volume_coordinateCube (inv_nonneg.mpr hn0.le),
        ← Measure.addHaar_image_linearMap volume (frameEquiv b).toLinearMap]
      exact measure_mono (frameEquiv_cube_subset hn b hconv hbal hb)
    have hd : LinearMap.det (frameEquiv b).toLinearMap ≠ 0 := by
      rw [frameEquiv_det]
      exact (e.isUnit_det b).ne_zero
    calc
      ENNReal.ofReal ((2 * (n : ℝ)⁻¹) ^ n) =
          ENNReal.ofReal |LinearMap.det (frameEquiv b).symm.toLinearMap| *
            (ENNReal.ofReal |LinearMap.det (frameEquiv b).toLinearMap| *
              ENNReal.ofReal ((2 * (n : ℝ)⁻¹) ^ n)) := by
        rw [LinearEquiv.det_coe_symm, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
          ← abs_mul, inv_mul_cancel₀ hd, abs_one, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr

end Submission.Lib.K4PolynomialGeometry
