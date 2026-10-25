/- Sharp old-base pair estimates and isotropic support through an auxiliary base grid.
Written for o265 and its original-field children. Existing affine covers,
norm estimates and integer-floor identities remain library imports. -/
import Submission.Lib.K4AffineCubeSupport.Graph
import Submission.Lib.K4NativePreparationNumerics.Frames
import Submission.Lib.K4XInterface.Basic

set_option autoImplicit false

namespace Submission.Lib.K4SharpAffineSupport

open Set
open Submission.Lib.K4AffineCubeSupport
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells

noncomputable section

/-- Only the base indices are coarsened; the hidden signal bin is unchanged. -/
def coarsenJointBaseCode (steps : ℕ) (q : Fin 4 → ℤ) : Fin 4 → ℤ :=
  Fin.snoc (fun j => q j.castSucc/(2:ℤ)^steps) (q 3)

theorem jointCode_dyadic_base_coarsening (steps : ℕ) (base hidden : ℝ)
    (z : Fin 3 → ℝ) (w : ℝ) :
    jointCode (base*(2:ℝ)^steps) hidden z w =
      coarsenJointBaseCode steps (jointCode base hidden z w) := by
  unfold jointCode coarsenJointBaseCode
  simp only [Fin.snoc_castSucc]
  congr 1
  ext j
  unfold baseCode
  rw [div_mul_eq_div_div,Submission.Lib.K4XInterface.floor_div_two_pow]

/-- A sharp OLD-base pair estimate supplies the accepted affine graph
cover. Its height condition has no inverse fine frame or clock factor. -/
theorem sharp_affine_joint_family_cover {I X : Type*} [Fintype I]
    (Z : X → EuclideanSpace ℝ (Fin 3)) (signal : X → ℝ) (A : I → Set X)
    (M : I → Matrix (Fin 3) (Fin 3) ℝ) (shift : I → Fin 3 → ℝ)
    (hM : ∀ i, (M i).det ≠ 0) {base hidden additive Lip : ℝ}
    (hbase : 0 < base) (hhidden : 0 < hidden) (hLip : 0 ≤ Lip)
    (hrows : ∀ i r, (∑ j : Fin 3, |(M i)⁻¹ r j| *base) ≤ 1)
    (hpoint : ∀ i x, x∈A i → (fun j => Z x j)∈affineCube (M i) (shift i))
    (hpair : ∀ i x, x∈A i → ∀ y, y∈A i →
      |signal x-signal y| ≤ additive+Lip*‖Z x-Z y‖)
    (hheight : additive+3*Lip*base ≤ hidden) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ)*base^3 ≤ 108*(∑ i, |(M i).det|) ∧
      ∀ i x, x∈A i → jointCode base hidden (fun j => Z x j) (signal x)∈S := by
  have hosc (i : I) (x : X) (hx : x∈A i) (y : X) (hy : y∈A i)
      (hcode : baseCode base (fun j => Z x j)=baseCode base (fun j => Z y j)) :
      |signal x-signal y| ≤ 1*hidden := by
    have hcoord (j : Fin 3) : |Z x j-Z y j| ≤ base := by
      have hh := (Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hcode j)).le
      rw [←sub_div,abs_div,abs_of_pos hbase,div_le_one hbase] at hh
      exact hh
    have hnorm : ‖Z x-Z y‖ ≤ 3*base := by
      calc
        _ ≤ ∑ j : Fin 3, |(Z x-Z y) j| :=
          Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _
        _ ≤ ∑ _j : Fin 3, base := Finset.sum_le_sum (fun j _ => hcoord j)
        _ = _ := by simp
    calc
      _ ≤ additive+Lip*‖Z x-Z y‖ := hpair i x hx y hy
      _ ≤ additive+Lip*(3*base) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm hLip)
      _ ≤ _ := by nlinarith only [hheight]
  obtain ⟨S,hS,hcover⟩ := affine_joint_family_cover (fun x j => Z x j) signal A M shift hM
    hbase hhidden (by norm_num : (0:ℝ) ≤ 1) hrows hpoint hosc
  exact ⟨S,by norm_num at hS; exact hS,hcover⟩

/-- A finer auxiliary BASE grid resolves the affine frames. Coarsening
it to the signal width gives a genuine isotropic support; the only cost
is the explicit cube of the dyadic base ratio. -/
theorem isotropic_support_from_sharp_affine_family {I X : Type*} [Fintype I]
    (Z : X → EuclideanSpace ℝ (Fin 3)) (signal : X → ℝ) (A : I → Set X)
    (M : I → Matrix (Fin 3) (Fin 3) ℝ) (shift : I → Fin 3 → ℝ)
    (hM : ∀ i, (M i).det ≠ 0) (steps : ℕ) {mesh additive Lip : ℝ}
    (hmesh : 0 < mesh) (hLip : 0 ≤ Lip)
    (hrows : ∀ i r, (∑ j : Fin 3, |(M i)⁻¹ r j| *(mesh/(2:ℝ)^steps)) ≤ 1)
    (hpoint : ∀ i x, x∈A i → (fun j => Z x j)∈affineCube (M i) (shift i))
    (hpair : ∀ i x, x∈A i → ∀ y, y∈A i →
      |signal x-signal y| ≤ additive+Lip*‖Z x-Z y‖)
    (hheight : additive+3*Lip*(mesh/(2:ℝ)^steps) ≤ mesh) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ)*mesh^3 ≤ 108*((2:ℝ)^steps)^3*(∑ i, |(M i).det|) ∧
      ∀ i x, x∈A i → jointCode mesh mesh (fun j => Z x j) (signal x)∈S := by
  classical
  let base := mesh/(2:ℝ)^steps
  have hbase : 0 < base := by dsimp [base]; positivity
  obtain ⟨F,hF,hcover⟩ := sharp_affine_joint_family_cover Z signal A M shift hM
    hbase hmesh hLip hrows hpoint hpair hheight
  let S := F.image (coarsenJointBaseCode steps)
  have hcard : (S.card : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast Finset.card_image_le
  have hscale : mesh=base*(2:ℝ)^steps := by dsimp [base]; field_simp
  refine ⟨S,?_,?_⟩
  · calc
      _ ≤ (F.card : ℝ)*mesh^3 := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ((2:ℝ)^steps)^3*((F.card : ℝ)*base^3) := by rw [hscale]; ring
      _ ≤ ((2:ℝ)^steps)^3*(108*∑ i, |(M i).det|) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
      _ = _ := by ring
  · intro i x hx
    have hh := jointCode_dyadic_base_coarsening steps base mesh (fun j => Z x j) (signal x)
    rw [←hscale] at hh
    rw [hh]
    exact Finset.mem_image.mpr ⟨jointCode base mesh (fun j => Z x j) (signal x),hcover i x hx,rfl⟩

end

end Submission.Lib.K4SharpAffineSupport
