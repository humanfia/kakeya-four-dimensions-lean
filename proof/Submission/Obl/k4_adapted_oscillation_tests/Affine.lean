import Mathlib

open MeasureTheory Set

namespace Submission.Obl.k4_adapted_oscillation_tests

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem pi_unitInterval_restrict (n : ℕ) :
    Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) =
      (volume : Measure (Fin n → ℝ)).restrict (Set.Icc 0 1) := by
  rw [← Measure.restrict_pi_pi]
  exact congrArg (fun s : Set (Fin n → ℝ) =>
    (volume : Measure (Fin n → ℝ)).restrict s)
    (pi_univ_Icc (x := (0 : Fin n → ℝ)) (y := (1 : Fin n → ℝ)))

/-- The coordinate unit cube in Euclidean space. -/
def unitCube (n : ℕ) : Set (Space n) :=
  WithLp.toLp 2 '' Set.Icc (0 : Fin n → ℝ) 1

/-- An affine image of the coordinate cube. -/
def affineCube {n : ℕ} (L : Space n ≃L[ℝ] Space n) (c : Space n) : Set (Space n) :=
  (fun x => c + L x) '' unitCube n

/-- The linear change of coordinates for a scaled basis cube. -/
noncomputable def basisScaleEquiv {n : ℕ} (b : Module.Basis (Fin n) ℝ (Space n))
    (η : ℝ) (hη : η ≠ 0) : Space n ≃L[ℝ] Space n :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).trans
    b.equivFun.symm.toContinuousLinearEquiv).trans
      (LinearEquiv.smulOfNeZero ℝ (Space n) η hη).toContinuousLinearEquiv

theorem basisScaleEquiv_toLp {n : ℕ} (b : Module.Basis (Fin n) ℝ (Space n))
    (η : ℝ) (hη : η ≠ 0) (t : Fin n → ℝ) :
    basisScaleEquiv b η hη (WithLp.toLp 2 t) = η • ∑ i, t i • b i := by
  change η • b.equivFun.symm t = _
  rw [b.equivFun_symm_apply]

theorem basisScaleEquiv_single {n : ℕ} (b : Module.Basis (Fin n) ℝ (Space n))
    (η : ℝ) (hη : η ≠ 0) (i : Fin n) :
    basisScaleEquiv b η hη (EuclideanSpace.single i 1) = η • b i := by
  change basisScaleEquiv b η hη (WithLp.toLp 2 (Pi.single i 1)) = _
  rw [basisScaleEquiv_toLp]
  simp

theorem affineCube_basisScaleEquiv {n : ℕ} (b : Module.Basis (Fin n) ℝ (Space n))
    (η : ℝ) (hη : η ≠ 0) (a : Space n) :
    affineCube (basisScaleEquiv b η hη) a =
      (fun t : Fin n → ℝ => a + η • ∑ i, t i • b i) '' Set.Icc (0 : Fin n → ℝ) 1 := by
  rw [affineCube, unitCube, Set.image_image]
  congr 1
  funext t
  simp only [basisScaleEquiv_toLp]

theorem isCompact_unitCube (n : ℕ) : IsCompact (unitCube n) := by
  exact isCompact_Icc.image (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.continuous

theorem volume_unitCube (n : ℕ) : volume (unitCube n) = 1 := by
  change volume ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).toEquiv ''
    Set.Icc (0 : Fin n → ℝ) 1) = 1
  rw [(MeasurableEquiv.toLp 2 (Fin n → ℝ)).toEquiv.image_eq_preimage_symm]
  calc
    _ = volume (Set.Icc (0 : Fin n → ℝ) 1) :=
      (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage_emb
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding _
    _ = 1 := by simp [Real.volume_Icc_pi]

theorem integral_unitCube {n : ℕ} (g : Space n → ℝ) :
    ∫ x in unitCube n, g x =
      ∫ x in Set.Icc (0 : Fin n → ℝ) 1, g (WithLp.toLp 2 x) := by
  exact (PiLp.volume_preserving_toLp (Fin n)).setIntegral_image_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding g _

theorem isCompact_affineCube {n : ℕ} (L : Space n ≃L[ℝ] Space n) (c : Space n) :
    IsCompact (affineCube L c) :=
  (isCompact_unitCube n).image (continuous_const.add L.continuous)

/-- The affine-cube integral formula keeps the determinant as a single constant. -/
theorem integral_affineCube {n : ℕ} (L : Space n ≃L[ℝ] Space n)
    (c : Space n) (g : Space n → ℝ) :
    ∫ x in affineCube L c, g x =
      |LinearMap.det (L : Space n →ₗ[ℝ] Space n)| *
        ∫ x in Set.Icc (0 : Fin n → ℝ) 1, g (c + L (WithLp.toLp 2 x)) := by
  have hd : ∀ x ∈ unitCube n,
      HasFDerivWithinAt (fun x => c + L x) (L : Space n →L[ℝ] Space n) (unitCube n) x :=
    fun x hx => L.hasFDerivAt.const_add c |>.hasFDerivWithinAt
  have hi : Set.InjOn (fun x => c + L x) (unitCube n) := by
    intro x hx y hy h
    exact L.injective (add_left_cancel h)
  rw [affineCube, integral_image_eq_integral_abs_det_fderiv_smul volume
    (isCompact_unitCube n).measurableSet hd hi]
  simp only [smul_eq_mul]
  rw [integral_const_mul, integral_unitCube]
  rfl

theorem volume_affineCube {n : ℕ} (L : Space n ≃L[ℝ] Space n) (c : Space n) :
    volume (affineCube L c) =
      ENNReal.ofReal |LinearMap.det (L : Space n →ₗ[ℝ] Space n)| := by
  rw [affineCube, ← Set.image_image]
  change volume ((MeasurableEquiv.addLeft c).toEquiv '' (L '' unitCube n)) = _
  rw [(MeasurableEquiv.addLeft c).toEquiv.image_eq_preimage_symm]
  calc
    _ = volume (L '' unitCube n) :=
      ((measurePreserving_add_left (volume : Measure (Space n)) c).symm
        (MeasurableEquiv.addLeft c)).measure_preimage_equiv _
    _ = _ := by
      rw [Measure.addHaar_image_continuousLinearEquiv, volume_unitCube, mul_one]

theorem volume_affineCube_pos {n : ℕ} (L : Space n ≃L[ℝ] Space n) (c : Space n) :
    0 < volume (affineCube L c) := by
  rw [volume_affineCube]
  exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero)

theorem volume_affineCube_toReal {n : ℕ} (L : Space n ≃L[ℝ] Space n) (c : Space n) :
    (volume (affineCube L c)).toReal =
      |LinearMap.det (L : Space n →ₗ[ℝ] Space n)| := by
  rw [volume_affineCube, ENNReal.toReal_ofReal (abs_nonneg _)]

end Submission.Obl.k4_adapted_oscillation_tests
