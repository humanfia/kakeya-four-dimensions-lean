/-
Adapted from: here:o204
Original o204 sources and file-level provenance are recorded below.
-/
/- Original provenance: here:o204, session x0706, commit d013eb32;
   original file Submission/Obl/k4_uniform_sampled_isotropic_branches/RawJointSupport.lean. -/
import Submission.Lib.K4OriginalGeometricReference.JointSupport

/-!
Keep the ORIGINAL earlier source mass in the joint support bound. It later
cancels in heavy-group selection, so no old narrowed-chart prior/volume
calibration is required by this completion step.
-/

namespace Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

open Set

noncomputable section

/-- Full ORIGINAL finer-entry floors bound the sum of actual base-box
volumes in units of the geometric signal reference. The earlier source
mass is kept explicitly, rather than replaced by an old assignment prior. -/
theorem raw_original_graph_box_volume_budget
    {I : Type*} [Fintype I]
    (boxVolume fineTime fineDet prior mass : I → ℝ)
    {N fFine oldTime oldDet Kbox Kfine θ sourceMass : ℝ}
    (hN : 0 < N) (ht : 0 < oldTime) (hdet : 0 < oldDet) (hθ : 0 < θ)
    (hKbox : 0 ≤ Kbox) (hKfine : 0 ≤ Kfine)
    (htime : ∀ i, 0 ≤ fineTime i)
    (hbox : ∀ i, boxVolume i ≤ Kbox * fineTime i * fineDet i / (oldTime * oldDet))
    (hprior : ∀ i, fineDet i ≤ Kfine * N ^ fFine * prior i)
    (hfloor : ∀ i, θ * fineTime i * prior i ≤ mass i)
    (hsum : (∑ i, mass i) ≤ sourceMass) :
    (∑ i, boxVolume i) ≤ (Kbox * Kfine / θ) *
      sourceMass / (oldTime * oldDet * N ^ (-fFine)) := by
  have hpoint (i : I) : boxVolume i ≤
      (Kbox * Kfine * N ^ fFine / (oldTime * oldDet * θ)) * mass i := by
    have hfl : fineTime i * prior i ≤ mass i / θ := by
      apply (le_div_iff₀ hθ).mpr
      nlinarith [hfloor i]
    calc
      boxVolume i ≤ Kbox * fineTime i * fineDet i / (oldTime * oldDet) := hbox i
      _ ≤ Kbox * fineTime i * (Kfine * N ^ fFine * prior i) / (oldTime * oldDet) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hprior i) (mul_nonneg hKbox (htime i))) (by positivity)
      _ = Kbox * Kfine * N ^ fFine / (oldTime * oldDet) * (fineTime i * prior i) := by ring
      _ ≤ Kbox * Kfine * N ^ fFine / (oldTime * oldDet) * (mass i / θ) :=
        mul_le_mul_of_nonneg_left hfl (by positivity)
      _ = _ := by ring
  calc
    (∑ i, boxVolume i) ≤ ∑ i, (Kbox * Kfine * N ^ fFine /
        (oldTime * oldDet * θ)) * mass i := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = (Kbox * Kfine * N ^ fFine / (oldTime * oldDet * θ)) * ∑ i, mass i :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (Kbox * Kfine * N ^ fFine / (oldTime * oldDet * θ)) * sourceMass :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [Real.rpow_neg hN.le]
      field_simp

/-- Independent base/signal meshes retain the source-mass/geometric-
reference ratio. This requires only ORIGINAL finer-entry floors and
geometry; there is NO old-chart prior lower or upper bound. -/
theorem raw_original_joint_support
    {I X : Type*} [Fintype I]
    (Z : X → Fin 3 → ℝ) (signal : X → ℝ)
    (A : I → Set X) (c H : I → Fin 3 → ℝ)
    (fineTime fineDet prior mass : I → ℝ)
    {N fFine oldTime oldDet Kbox Kfine θ sourceMass R baseMesh signalMesh : ℝ}
    (hN : 0 < N) (ht : 0 < oldTime) (hdet : 0 < oldDet) (hθ : 0 < θ)
    (hKbox : 0 ≤ Kbox) (hKfine : 0 ≤ Kfine) (htime : ∀ i, 0 ≤ fineTime i)
    (hR : 0 ≤ R) (hbase : 0 < baseMesh) (hsignal : 0 < signalMesh)
    (hresolve : ∀ i j, baseMesh ≤ H i j)
    (hbox : ∀ i x, x ∈ A i → ∀ j, |Z x j - c i j| ≤ H i j)
    (hosc : ∀ i x, x ∈ A i → ∀ y, y ∈ A i →
      baseCode baseMesh (Z x) = baseCode baseMesh (Z y) →
      |signal x - signal y| ≤ R * signalMesh)
    (hgeometry : ∀ i, (∏ j, H i j) ≤ Kbox * fineTime i * fineDet i / (oldTime * oldDet))
    (hprior : ∀ i, fineDet i ≤ Kfine * N ^ fFine * prior i)
    (hfloor : ∀ i, θ * fineTime i * prior i ≤ mass i)
    (hsum : (∑ i, mass i) ≤ sourceMass) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * baseMesh ^ 3 ≤
        (216 * (2 * R + 2) * (Kbox * Kfine / θ)) *
          sourceMass / (oldTime * oldDet * N ^ (-fFine)) ∧
      ∀ i x, x ∈ A i → jointCode baseMesh signalMesh (Z x) (signal x) ∈ S := by
  have hvolume := raw_original_graph_box_volume_budget (fun i => ∏ j, H i j)
    fineTime fineDet prior mass hN ht hdet hθ hKbox hKfine htime hgeometry hprior hfloor hsum
  obtain ⟨S, hS, hcover⟩ := rectangular_joint_family_cover Z signal A c H
    hR hbase hsignal hresolve hbox hosc hvolume
  refine ⟨S, ?_, hcover⟩
  convert hS using 1 <;> ring


/-- Compare the actual residual signal with its fixed earlier fine-sheet
residual. Whole-entry oscillation then supplies the signal diameter used
in a JOINT residual support cover. No common intercept is chosen here. -/
theorem original_entry_residual_signal_diameter
    {X : Type*} (A : Set X) (signal residual : X → ℝ) {comparison oscillation : ℝ}
    (hcomparison : ∀ x ∈ A, |signal x - residual x| ≤ comparison)
    (hoscillation : ∀ x ∈ A, ∀ y ∈ A, |residual x - residual y| ≤ oscillation) :
    ∀ x ∈ A, ∀ y ∈ A, |signal x - signal y| ≤ 2 * comparison + oscillation := by
  intro x hx y hy
  have hx' := hcomparison x hx
  have hy' := hcomparison y hy
  have hxy := hoscillation x hx y hy
  apply abs_le.mpr
  constructor <;> linarith [(abs_le.mp hx').1, (abs_le.mp hx').2,
    (abs_le.mp hy').1, (abs_le.mp hy').2, (abs_le.mp hxy).1, (abs_le.mp hxy).2]

end

end Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
