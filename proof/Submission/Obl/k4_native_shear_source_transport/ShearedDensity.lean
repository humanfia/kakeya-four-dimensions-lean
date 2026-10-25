-- Copied from LOT tree oai_074_kakeya_four_dimensions, obligation o075 (k4_joint_homogenization),
-- branch x0254, file Submission/Obl/k4_joint_homogenization/ShearedDensity.lean (session x0254's own proofs), renamed into this namespace.
import Submission.Obl.k4_native_shear_source_transport.NativeLaw
import Submission.Obl.k4_native_shear_source_transport.PolyAxis

/-!
# The real sheared density and its polynomial sign tables

The native density in sheared coordinates is `φ(z) = ∑ⱼ cⱼ 1[z ∈ Sⱼ]`, where `Sⱼ` is the
sheared selection of the `j`-th prior piece. Its value at `z` only depends on the signs of
the prior and event polynomials evaluated at the (polynomial) unsheared coordinates of `z`.
-/

namespace Submission.Obl.k4_native_shear_source_transport

open MeasureTheory Set MvPolynomial
open scoped ENNReal

/-- The coefficient vector of `shearEquiv.symm z`, as polynomials in `z`. -/
noncomputable def coefPoly : Fin 6 → MvPolynomial (Fin 7) ℝ :=
  ![X 1 - X 0 * X 4, X 2 - X 0 * X 5, X 3 - X 0 * X 6, X 4, X 5, X 6]

/-- The coefficient vector and time of `shearEquiv.symm z` (as `Fin.snoc x t`). -/
noncomputable def coefTimePoly : Fin 7 → MvPolynomial (Fin 7) ℝ :=
  ![X 1 - X 0 * X 4, X 2 - X 0 * X 5, X 3 - X 0 * X 6, X 4, X 5, X 6, X 0]

theorem eval_coefPoly (z : Fin 7 → ℝ) :
    (fun l => eval z (coefPoly l)) = (shearEquiv.symm z).1 := by
  rw [shearEquiv_symm_apply]
  funext l
  fin_cases l <;> simp [coefPoly]

theorem eval_coefTimePoly_castSucc (z : Fin 7 → ℝ) :
    (fun j₁ : Fin 6 => eval z (coefTimePoly j₁.castSucc)) = (shearEquiv.symm z).1 := by
  rw [shearEquiv_symm_apply]
  funext l
  fin_cases l <;> simp [coefTimePoly]

theorem eval_coefTimePoly_six (z : Fin 7 → ℝ) :
    eval z (coefTimePoly 6) = (shearEquiv.symm z).2 := by
  rw [shearEquiv_symm_apply]
  simp [coefTimePoly]

private theorem totalDegree_X_le_two (a : Fin 7) : (X a : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by
  rw [totalDegree_X]; norm_num

private theorem totalDegree_aff_le_two (a b c : Fin 7) :
    (X a - X b * X c : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [totalDegree_X]; norm_num
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X, totalDegree_X]

theorem totalDegree_coefPoly_le (l : Fin 6) : (coefPoly l).totalDegree ≤ 2 := by
  fin_cases l
  · exact totalDegree_aff_le_two 1 0 4
  · exact totalDegree_aff_le_two 2 0 5
  · exact totalDegree_aff_le_two 3 0 6
  · exact totalDegree_X_le_two 4
  · exact totalDegree_X_le_two 5
  · exact totalDegree_X_le_two 6

theorem totalDegree_coefTimePoly_le (l : Fin 7) : (coefTimePoly l).totalDegree ≤ 2 := by
  fin_cases l
  · exact totalDegree_aff_le_two 1 0 4
  · exact totalDegree_aff_le_two 2 0 5
  · exact totalDegree_aff_le_two 3 0 6
  · exact totalDegree_X_le_two 4
  · exact totalDegree_X_le_two 5
  · exact totalDegree_X_le_two 6
  · exact totalDegree_X_le_two 0

/-- The real native density in sheared coordinates. -/
noncomputable def nativeDensityR {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (z : Fin 7 → ℝ) : ℝ :=
  ∑ j, c j * (shearedPiece (A j) (i j) E').indicator 1 z

theorem nativeDensity_eq_ofReal {m : ℕ} {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) :
    nativeDensity c i A E' = fun z => ENNReal.ofReal (nativeDensityR c i A E' z) := by
  funext z
  unfold nativeDensity nativeDensityR
  rw [tsum_fintype, Finset.sum_apply, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (hc j)]
    congr 1
    by_cases hz : z ∈ shearedPiece (A j) (i j) E' <;> simp [hz]
  · intro j _
    exact mul_nonneg (hc j) (indicator_nonneg (fun _ _ => zero_le_one) z)

theorem measurable_nativeDensityR {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    {A : Fin m → Set (Fin 6 → ℝ)} (hA : ∀ j, MeasurableSet (A j))
    {E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hE' : MeasurableSet E') :
    Measurable (nativeDensityR c i A E') := by
  unfold nativeDensityR
  apply Finset.measurable_sum
  intro j _
  exact (measurable_one.indicator (measurableSet_shearedPiece (hA j) (i j) hE')).const_mul _

theorem nativeDensityR_nonneg {m : ℕ} {c : Fin m → ℝ} (hc : ∀ j, 0 ≤ c j) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 6 → ℝ)) (E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (z : Fin 7 → ℝ) :
    0 ≤ nativeDensityR c i A E' z :=
  Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (indicator_nonneg (fun _ _ => zero_le_one) z)

theorem nativeDensityR_le {m : ℕ} {c : Fin m → ℝ} {B : ℝ} (hc : ∀ j, 0 ≤ c j ∧ c j ≤ B)
    (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)) (E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (z : Fin 7 → ℝ) : nativeDensityR c i A E' z ≤ m * B := by
  unfold nativeDensityR
  calc ∑ j, c j * (shearedPiece (A j) (i j) E').indicator 1 z ≤ ∑ _j : Fin m, B := by
        apply Finset.sum_le_sum
        intro j _
        have h1 : (shearedPiece (A j) (i j) E').indicator (1 : (Fin 7 → ℝ) → ℝ) z ≤ 1 :=
          indicator_le_self' (fun _ _ => zero_le_one) z
        have h0 : 0 ≤ (shearedPiece (A j) (i j) E').indicator (1 : (Fin 7 → ℝ) → ℝ) z :=
          indicator_nonneg (fun _ _ => zero_le_one) z
        calc c j * _ ≤ c j * 1 := mul_le_mul_of_nonneg_left h1 (hc j).1
          _ ≤ B := by rw [mul_one]; exact (hc j).2
    _ = m * B := by simp

/-- Points of a sheared piece have bounded coordinates. -/
theorem abs_le_of_mem_shearedPiece {A : Set (Fin 6 → ℝ)} {i : ℕ}
    {E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : ℝ} (hB : 1 ≤ B)
    (hA : ∀ x ∈ A, ∀ l, |x l| ≤ B) (hE' : E' ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {z : Fin 7 → ℝ} (hz : z ∈ shearedPiece A i E') : ∀ l, |z l| ≤ 2 * B := by
  have hz' : z = shearEquiv (shearEquiv.symm z) := (shearEquiv.apply_symm_apply z).symm
  obtain ⟨hxA, hxE⟩ := hz
  set x := (shearEquiv.symm z).1
  set t := (shearEquiv.symm z).2
  have ht : t ∈ Icc (0 : ℝ) 1 := (hE' hxE).2
  have hx := hA x hxA
  have htabs : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have haff : ∀ a b : Fin 6, |x a + t * x b| ≤ 2 * B := by
    intro a b
    calc |x a + t * x b| ≤ |x a| + |t| * |x b| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ B + 1 * B := by
          gcongr
          · exact hx a
          · exact hx b
      _ = 2 * B := by ring
  have hzx : z = ![t, x 0 + t * x 3, x 1 + t * x 4, x 2 + t * x 5, x 3, x 4, x 5] := by
    rw [hz']; exact shearEquiv_apply x t
  intro l
  rw [hzx]
  fin_cases l
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; linarith
  · exact haff 0 3
  · exact haff 1 4
  · exact haff 2 5
  · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]; linarith [hx 3]
  · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]; linarith [hx 4]
  · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]; linarith [hx 5]

theorem abs_le_of_nativeDensityR_ne_zero {m : ℕ} {c : Fin m → ℝ} {i : Fin m → ℕ}
    {A : Fin m → Set (Fin 6 → ℝ)} {E' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : ℝ} (hB : 1 ≤ B)
    (hA : ∀ j, ∀ x ∈ A j, ∀ l, |x l| ≤ B) (hE' : E' ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {z : Fin 7 → ℝ} (hz : nativeDensityR c i A E' z ≠ 0) : ∀ l, |z l| ≤ 2 * B := by
  by_contra hcon
  apply hz
  unfold nativeDensityR
  apply Finset.sum_eq_zero
  intro j _
  have hnot : z ∉ shearedPiece (A j) (i j) E' := fun hmem =>
    hcon (abs_le_of_mem_shearedPiece hB (hA j) hE' hmem)
  simp [hnot]

end Submission.Obl.k4_native_shear_source_transport
