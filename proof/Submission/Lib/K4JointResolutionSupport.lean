-- General joint-width resolution for original physical-parent source counting.
-- Developed in this LOT tree, o265/x0943, SharpResolutionNumerics.lean and
-- SharpJointResolution.lean. Accepted affine support remains an import.
import Submission.Lib.K4SharpAffineSupport

set_option autoImplicit false

namespace Submission.Lib.K4JointResolutionSupport
open Set
open Submission.Lib.K4AffineCubeSupport
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open Submission.Lib.K4SharpAffineSupport
noncomputable section

/-- Choose a dyadic auxiliary base that resolves all actual inverse
frames and the sharp signal slope. Its ratio costs at most twice the
largest displayed original bound. -/
theorem exists_dyadic_sharp_resolution {I : Type*}
    (M : I → Matrix (Fin 3) (Fin 3) ℝ) {mesh additive Lip frameBudget : ℝ}
    (hmesh : 0 < mesh) (hadditive : additive ≤ mesh/2)
    (hframe : ∀ i r, (∑ j : Fin 3, |(M i)⁻¹ r j|)*mesh ≤ frameBudget) :
    ∃ steps : ℕ, (2:ℝ)^steps ≤ 2*max 1 (max frameBudget (6*Lip)) ∧
      (∀ i r, (∑ j : Fin 3, |(M i)⁻¹ r j| *(mesh/(2:ℝ)^steps)) ≤ 1) ∧
      additive+3*Lip*(mesh/(2:ℝ)^steps) ≤ mesh := by
  let C := max 1 (max frameBudget (6*Lip))
  have hC : 1 ≤ C := le_max_left _ _
  obtain ⟨n,hn,hup⟩ := exists_nat_pow_near hC (by norm_num : (1:ℝ) < 2)
  let steps := n+1
  have hpow : C ≤ (2:ℝ)^steps := hup.le
  have hpowpos : 0 < (2:ℝ)^steps := by positivity
  have hpowBound : (2:ℝ)^steps ≤ 2*C := by
    dsimp [steps]
    rw [pow_succ]
    nlinarith only [hn]
  have hFrameC : frameBudget ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hLipC : 6*Lip ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨steps,hpowBound,?_,?_⟩
  · intro i r
    have heq : (∑ j : Fin 3, |(M i)⁻¹ r j| *(mesh/(2:ℝ)^steps)) =
        (∑ j : Fin 3, |(M i)⁻¹ r j|)*mesh/(2:ℝ)^steps := by
      simp only [Fin.sum_univ_three]
      ring
    rw [heq]
    exact (div_le_one hpowpos).mpr ((hframe i r).trans (hFrameC.trans hpow))
  · have hr : 3*Lip/(2:ℝ)^steps ≤ (1:ℝ)/2 :=
      (div_le_iff₀ hpowpos).mpr (by linarith [hLipC.trans hpow])
    have hh : 3*Lip*(mesh/(2:ℝ)^steps) ≤ mesh/2 := by
      calc
        _ = (3*Lip/(2:ℝ)^steps)*mesh := by ring
        _ ≤ ((1:ℝ)/2)*mesh := mul_le_mul_of_nonneg_right hr hmesh.le
        _ = _ := by ring
    linarith


/-- Resolve base and hidden widths separately. The signal slope is charged
only through Lip*base/hidden, as required for a physical P/a signal. -/
theorem exists_dyadic_joint_resolution {I : Type*}
    (M : I → Matrix (Fin 3) (Fin 3) ℝ) {base hidden additive Lip frameBudget : ℝ}
    (hbase : 0 < base) (hhidden : 0 < hidden) (hadditive : additive ≤ hidden/2)
    (hframe : ∀ i r, (∑ j : Fin 3, |(M i)⁻¹ r j|)*base ≤ frameBudget) :
    ∃ steps : ℕ, (2:ℝ)^steps ≤ 2*max 1 (max frameBudget (6*(Lip*base/hidden))) ∧
      (∀ i r, (∑ j : Fin 3, |(M i)⁻¹ r j| *(base/(2:ℝ)^steps)) ≤ 1) ∧
      additive+3*Lip*(base/(2:ℝ)^steps) ≤ hidden := by
  have hscaled : additive*base/hidden ≤ base/2 := by
    apply (div_le_iff₀ hhidden).mpr
    nlinarith [mul_le_mul_of_nonneg_right hadditive hbase.le]
  obtain ⟨steps,hsteps,hrows,hheight⟩ := exists_dyadic_sharp_resolution M
    (Lip:=Lip*base/hidden) hbase hscaled hframe
  refine ⟨steps,hsteps,hrows,?_⟩
  apply (mul_le_mul_iff_right₀ (div_pos hbase hhidden)).mp
  calc
    _ = additive*base/hidden+3*(Lip*base/hidden)*(base/(2:ℝ)^steps) := by ring
    _ ≤ base := hheight
    _ = (base/hidden)*hidden := by field_simp

/-- A genuine joint support with independently chosen base and hidden
widths. No isotropic intermediate signal mesh is introduced. -/
theorem joint_support_from_sharp_affine_family {I X : Type*} [Fintype I]
    (Z : X → EuclideanSpace ℝ (Fin 3)) (signal : X → ℝ) (A : I → Set X)
    (M : I → Matrix (Fin 3) (Fin 3) ℝ) (shift : I → Fin 3 → ℝ)
    (hM : ∀ i, (M i).det ≠ 0) {base hidden additive Lip frameBudget : ℝ}
    (hbase : 0 < base) (hhidden : 0 < hidden) (hLip : 0 ≤ Lip)
    (hadditive : additive ≤ hidden/2)
    (hframe : ∀ i r, (∑ j : Fin 3, |(M i)⁻¹ r j|)*base ≤ frameBudget)
    (hpoint : ∀ i x, x∈A i → (fun j => Z x j)∈affineCube (M i) (shift i))
    (hpair : ∀ i x, x∈A i → ∀ y, y∈A i →
      |signal x-signal y| ≤ additive+Lip*‖Z x-Z y‖) :
    let C := max 1 (max frameBudget (6*(Lip*base/hidden)))
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ)*base^3 ≤ 864*C^3*(∑ i, |(M i).det|) ∧
      ∀ i x, x∈A i → jointCode base hidden (fun j => Z x j) (signal x)∈S := by
  classical
  dsimp only
  let C := max 1 (max frameBudget (6*(Lip*base/hidden)))
  obtain ⟨steps,hsteps,hrows,hheight⟩ := exists_dyadic_joint_resolution M hbase hhidden hadditive hframe
  let aux := base/(2:ℝ)^steps
  have haux : 0 < aux := by dsimp [aux]; positivity
  obtain ⟨F,hF,hcover⟩ := sharp_affine_joint_family_cover Z signal A M shift hM
    haux hhidden hLip hrows hpoint hpair hheight
  let S := F.image (coarsenJointBaseCode steps)
  have hcard : (S.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_image_le
  have hscale : base=aux*(2:ℝ)^steps := by dsimp [aux]; field_simp
  have hdet : 0 ≤ ∑ i, |(M i).det| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound : (S.card : ℝ)*base^3 ≤ ((2:ℝ)^steps)^3*(108*∑ i, |(M i).det|) := by
    calc
      _ ≤ (F.card : ℝ)*base^3 := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ((2:ℝ)^steps)^3*((F.card : ℝ)*aux^3) := by rw [hscale]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hF (by positivity)
  refine ⟨S,hbound.trans ?_,?_⟩
  · have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2:ℝ)^steps) hsteps 3
    calc
      _ ≤ (2*C)^3*(108*∑ i, |(M i).det|) :=
        mul_le_mul_of_nonneg_right hp (mul_nonneg (by norm_num) hdet)
      _ = _ := by dsimp [C]; ring
  · intro i x hx
    have heq := jointCode_dyadic_base_coarsening steps aux hidden (fun j => Z x j) (signal x)
    rw [←hscale] at heq
    rw [heq]
    exact Finset.mem_image_of_mem _ (hcover i x hx)

/-- The allowed physical slope h/a cancels against the independent joint
mesh condition; it does not contribute an inverse-thickness count. -/
theorem physical_parent_joint_slope_budget {a h base hidden G Lip : ℝ}
    (ha : 0 < a) (hbase : 0 ≤ base) (hhidden : 0 < hidden)
    (hLip : Lip ≤ G*h/a) (hmesh : 6*G*h*base ≤ a*hidden) :
    6*(Lip*base/hidden) ≤ 1 := by
  calc
    _ ≤ 6*((G*h/a)*base/hidden) := by gcongr
    _ = (6*G*h*base)/(a*hidden) := by ring
    _ ≤ 1 := (div_le_one (mul_pos ha hhidden)).mpr hmesh

/-- Under the physical joint mesh condition only the affine resolution
budget remains in the support count. -/
theorem physical_parent_joint_support {I X : Type*} [Fintype I]
    (Z : X → EuclideanSpace ℝ (Fin 3)) (signal : X → ℝ) (A : I → Set X)
    (M : I → Matrix (Fin 3) (Fin 3) ℝ) (shift : I → Fin 3 → ℝ)
    (hM : ∀ i, (M i).det ≠ 0) {a h base hidden additive Lip G frameBudget : ℝ}
    (ha : 0 < a) (hbase : 0 < base) (hhidden : 0 < hidden) (hLip : 0 ≤ Lip)
    (hphysicalLip : Lip ≤ G*h/a) (hmesh : 6*G*h*base ≤ a*hidden)
    (hadditive : additive ≤ hidden/2)
    (hframe : ∀ i r, (∑ j : Fin 3, |(M i)⁻¹ r j|)*base ≤ frameBudget)
    (hpoint : ∀ i x, x∈A i → (fun j => Z x j)∈affineCube (M i) (shift i))
    (hpair : ∀ i x, x∈A i → ∀ y, y∈A i →
      |signal x-signal y| ≤ additive+Lip*‖Z x-Z y‖) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ)*base^3 ≤ 864*(max 1 frameBudget)^3*(∑ i, |(M i).det|) ∧
      ∀ i x, x∈A i → jointCode base hidden (fun j => Z x j) (signal x)∈S := by
  have hslope := physical_parent_joint_slope_budget ha hbase.le hhidden hphysicalLip hmesh
  have heq : max 1 (max frameBudget (6*(Lip*base/hidden)))=max 1 frameBudget := by
    rw [←max_assoc,max_eq_left (hslope.trans (le_max_left _ _))]
  simpa only [heq] using joint_support_from_sharp_affine_family Z signal A M shift hM
    hbase hhidden hLip hadditive hframe hpoint hpair


end
end Submission.Lib.K4JointResolutionSupport
