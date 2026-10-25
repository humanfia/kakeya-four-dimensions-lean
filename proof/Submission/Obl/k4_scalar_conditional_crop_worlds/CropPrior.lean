import Submission.Obl.k4_scalar_conditional_crop_worlds.Geometry
import Submission.Obl.k4_scalar_conditional_crop_worlds.FormatLemmas
import Submission.Obl.k4_scalar_marked_packet_recovery.MarkedMeasure

/-!
# The conditional prior of a scalar crop of a marked noisy prior

The marked prior is a finite mixture of uniform laws on translated noise cubes. Restricted to a
scalar cell and pushed through the crop, each component becomes a constant multiple of Lebesgue
measure on a box: the crop scales two coordinates by `a⁻¹`, so its Jacobian is `a⁻²`. The boxes
are cut out by affine conditions, so the conditional prior has the finite density format.
-/

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

open MeasureTheory Set

noncomputable section

/-! ### The Jacobian of the crop -/

/-- The diagonal of the linear part of the crop. -/
def cropScale (a : ℝ) : Coeff := ![a⁻¹, a⁻¹, 1, 1, 1]

/-- The translation part of the crop. -/
def cropShift (z : Label) : Coeff := ![-(z 0 : ℝ), -(z 1 : ℝ), 0, 0, 0]

/-- The linear part of the crop. -/
def cropLinear (a : ℝ) : Coeff →ₗ[ℝ] Coeff := Matrix.toLin' (Matrix.diagonal (cropScale a))

lemma cropLinear_apply (a : ℝ) (c : Coeff) (i : Fin 5) :
    cropLinear a c i = cropScale a i * c i := by
  simp [cropLinear, Matrix.diagonal_toLin']

lemma cropCoeff_eq_comp (a : ℝ) (z : Label) :
    cropCoeff a z = (fun c : Coeff => c + cropShift z) ∘ cropLinear a := by
  ext c i
  change cropCoeff a z c i = cropLinear a c i + cropShift z i
  rw [cropLinear_apply]
  fin_cases i <;> simp [cropCoeff, cropScale, cropShift, div_eq_mul_inv, mul_comm, sub_eq_add_neg]

lemma cropLinear_det (a : ℝ) : (Matrix.diagonal (cropScale a)).det = (a⁻¹) ^ 2 := by
  simp [Matrix.det_diagonal, cropScale, Fin.prod_univ_succ]
  ring

lemma map_cropCoeff_volume {a : ℝ} (ha : a ≠ 0) (z : Label) :
    Measure.map (cropCoeff a z) volume = ENNReal.ofReal (a ^ 2) • (volume : Measure Coeff) := by
  have hdet : (Matrix.diagonal (cropScale a)).det ≠ 0 := by
    rw [cropLinear_det]
    exact pow_ne_zero _ (inv_ne_zero ha)
  have hm : Measure.map (cropLinear a) volume =
      ENNReal.ofReal (a ^ 2) • (volume : Measure Coeff) := by
    rw [cropLinear, Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, cropLinear_det]
    simp only [inv_pow, inv_inv, abs_of_nonneg (by positivity : 0 ≤ a ^ 2)]
  rw [cropCoeff_eq_comp, ← Measure.map_map (by fun_prop) (LinearMap.continuous_on_pi _).measurable,
    hm, Measure.map_smul _ (by fun_prop), map_add_right_eq_self]

lemma map_cropCoeff_restrict {a : ℝ} (ha : a ≠ 0) (z : Label) (A : Set Coeff) :
    Measure.map (cropCoeff a z) (volume.restrict A) =
      ENNReal.ofReal (a ^ 2) • volume.restrict (uncropCoeff a z ⁻¹' A) := by
  have h := (coeffHomeomorph ha z).toMeasurableEquiv.restrict_map (volume : Measure Coeff)
    (uncropCoeff a z ⁻¹' A)
  have hpre : (coeffHomeomorph ha z).toMeasurableEquiv ⁻¹' (uncropCoeff a z ⁻¹' A) = A := by
    ext c
    change uncropCoeff a z (cropCoeff a z c) ∈ A ↔ c ∈ A
    rw [uncrop_cropCoeff ha]
  rw [hpre] at h
  change (Measure.map (cropCoeff a z) volume).restrict _ =
    Measure.map (cropCoeff a z) (volume.restrict A) at h
  rw [← h, map_cropCoeff_volume ha z, Measure.restrict_smul]

/-! ### The noise as a box density -/

/-- The noise cube `[0, σ]^5`. -/
def noiseCube (σ : ℝ) : Set Coeff := Set.pi univ (fun _ => Icc (0 : ℝ) σ)

lemma noise_eq {σ : ℝ} (hσ : 0 < σ) :
    Noise σ = ENNReal.ofReal (σ⁻¹ ^ 5) • volume.restrict (noiseCube σ) := by
  have := (volume.restrict (Icc (0 : ℝ) σ)).smul_finite
    (c := ENNReal.ofReal σ⁻¹) ENNReal.ofReal_ne_top
  show Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • volume.restrict (Icc (0 : ℝ) σ)) = _
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    noiseCube, ← Set.pi_inter_distrib, volume_pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hs _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (inv_nonneg.2 hσ.le)]

/-- The box `b + [0, σ]^5` carrying one marked component. -/
def boxOf (σ : ℝ) (b : Coeff) : Set Coeff := {c | ∀ e, c e - b e ∈ Icc (0 : ℝ) σ}

lemma map_translate_cube (σ : ℝ) (b : Coeff) :
    Measure.map (fun u : Coeff => b + u) (volume.restrict (noiseCube σ)) =
      volume.restrict (boxOf σ b) := by
  have h := (MeasurableEquiv.addLeft b).restrict_map (volume : Measure Coeff) (boxOf σ b)
  have hpre : (MeasurableEquiv.addLeft b) ⁻¹' boxOf σ b = noiseCube σ := by
    ext u
    change (∀ e, (b + u) e - b e ∈ Icc (0 : ℝ) σ) ↔ ∀ e ∈ (univ : Set (Fin 5)), u e ∈ Icc (0 : ℝ) σ
    simp only [Pi.add_apply, add_sub_cancel_left, mem_univ, true_implies]
  rw [hpre] at h
  change (Measure.map (fun u => b + u) volume).restrict _ =
    Measure.map (fun u => b + u) (volume.restrict (noiseCube σ)) at h
  rw [← h, map_add_left_eq_self]

/-! ### The conditional prior as a finite sum of boxes -/

/-- The coefficient section of a scalar cell. -/
def coeffCell (a : ℝ) (z : Label) : Set Coeff := {c | ⌊c 0 / a⌋ = z 0 ∧ ⌊c 1 / a⌋ = z 1}

/-- The cropped box of one marked component. -/
def cropBox (σ a : ℝ) (z : Label) (b : Coeff) : Set Coeff :=
  uncropCoeff a z ⁻¹' (coeffCell a z ∩ boxOf σ b)

lemma measurableSet_coeffCell (a : ℝ) (z : Label) : MeasurableSet (coeffCell a z) := by
  have h0 : Measurable fun c : Coeff => ⌊c 0 / a⌋ := Int.measurable_floor.comp (by fun_prop)
  have h1 : Measurable fun c : Coeff => ⌊c 1 / a⌋ := Int.measurable_floor.comp (by fun_prop)
  exact (measurableSet_eq_fun h0 measurable_const).inter
    (measurableSet_eq_fun h1 measurable_const)

lemma restrict_finset_sum {α ι : Type*} [MeasurableSpace α] (s : Finset ι)
    (μ : ι → Measure α) (t : Set α) :
    (∑ i ∈ s, μ i).restrict t = ∑ i ∈ s, (μ i).restrict t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.restrict_add, ih]

lemma measurable_index (j : ℕ) : Measurable (fun c : Coeff => (j, c)) :=
  measurable_const.prodMk measurable_id

/-- One marked component, restricted to a scalar cell and cropped. -/
lemma crop_component {N : ℝ} (hN : 0 < N) (u₀ : ℝ) (z : Label) {σ : ℝ} (hσ : 0 < σ)
    (j : ℕ) (b : Coeff) :
    Measure.map (scalarCropLine N u₀ z)
        ((Measure.map (fun u : Coeff => (j, b + u)) (Noise σ)).restrict (scalarCell N u₀ z)) =
      (ENNReal.ofReal (σ⁻¹ ^ 5) * ENNReal.ofReal ((N ^ (-u₀)) ^ 2)) •
        Measure.map (fun c : Coeff => (j, c)) (volume.restrict (cropBox σ (N ^ (-u₀)) z b)) := by
  have ha := scale_ne_zero hN u₀
  have hcomp : (fun u : Coeff => (j, b + u)) = (fun c : Coeff => (j, c)) ∘ (fun u => b + u) := rfl
  rw [noise_eq hσ, Measure.map_smul _ (by fun_prop), hcomp,
    ← Measure.map_map (measurable_index j) (by fun_prop), map_translate_cube,
    Measure.restrict_smul, Measure.restrict_map (measurable_index j)
      (measurableSet_scalarCell N u₀ z)]
  have hpre : (fun c : Coeff => (j, c)) ⁻¹' scalarCell N u₀ z = coeffCell (N ^ (-u₀)) z := rfl
  rw [hpre, Measure.restrict_restrict (measurableSet_coeffCell _ z),
    Measure.map_smul _ (by fun_prop),
    Measure.map_map (measurable_scalarCropLine N u₀ z) (measurable_index j)]
  have hcomp' : scalarCropLine N u₀ z ∘ (fun c : Coeff => (j, c)) =
      (fun c : Coeff => (j, c)) ∘ cropCoeff (N ^ (-u₀)) z := rfl
  rw [hcomp', ← Measure.map_map (measurable_index j) (continuous_cropCoeff _ z).measurable,
    map_cropCoeff_restrict ha, Measure.map_smul _ (by fun_prop), smul_smul]
  rfl

lemma ofReal_weight {w s g p : ℝ} (hw : 0 ≤ w) (hs : 0 ≤ s) (hp : 0 < p) :
    ENNReal.ofReal (w * s * g / p) =
      (ENNReal.ofReal p)⁻¹ * (ENNReal.ofReal w * (ENNReal.ofReal s * ENNReal.ofReal g)) := by
  rw [ENNReal.ofReal_div_of_pos hp, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hw, div_eq_mul_inv]
  ring

/-- The conditional prior of a scalar crop of a marked prior is a finite sum of boxes. -/
theorem conditionalPrior_eq {N : ℝ} (hN : 0 < N) (u₀ : ℝ) (z : Label) {σ : ℝ} (hσ : 0 < σ)
    {H : ℕ} (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) {p : ℝ} (hp : 0 < p) :
    (ENNReal.ofReal p)⁻¹ • Measure.map (scalarCropLine N u₀ z)
        ((MarkedPrior σ H b₀ w).restrict (scalarCell N u₀ z)) =
      ∑ j : Fin H, ENNReal.ofReal (w j * σ⁻¹ ^ 5 * (N ^ (-u₀)) ^ 2 / p) •
        Measure.map (fun c : Coeff => ((j : ℕ), c))
          (volume.restrict (cropBox σ (N ^ (-u₀)) z (b₀ j))) := by
  change (ENNReal.ofReal p)⁻¹ • Measure.map (scalarCropLine N u₀ z)
      ((∑ j, ENNReal.ofReal (w j) • Measure.map (fun u : Coeff => ((j : ℕ), b₀ j + u))
        (Noise σ)).restrict (scalarCell N u₀ z)) = _
  rw [restrict_finset_sum, Measure.map_finset_sum (by fun_prop), Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Measure.restrict_smul, Measure.map_smul _ (by fun_prop), crop_component hN u₀ z hσ,
    smul_smul, smul_smul, ofReal_weight (hw j) (by positivity) hp, mul_assoc]

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
