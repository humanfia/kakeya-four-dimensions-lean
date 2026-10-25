import Submission.Lib.K4CubicTests.QuadraticDivision

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Matrix
open scoped BigOperators

noncomputable section

/-- The symmetric cubic associated to a Hessian and a one-form. -/
def fubiniCubic (H : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ)
    (i j k : Fin 3) : ℝ := m i*H j k+m j*H i k+m k*H i j

/-- The curvature commutator of the Hessian equation. -/
def fubiniCommutator (H R : Matrix (Fin 3) (Fin 3) ℝ) (l k i j : Fin 3) : ℝ :=
  R l i*H k j+R l j*H k i-R k i*H l j-R k j*H l i

/-- The formal derivative of the symmetric cubic. -/
def fubiniCubicVariation (H : Matrix (Fin 3) (Fin 3) ℝ)
    (C : Fin 3 → Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (l i j k : Fin 3) : ℝ :=
  M l i*H j k+m i*C l j k+M l j*H i k+m j*C l i k+
    M l k*H i j+m k*C l i j

/-- Differentiating the cubic relation and commuting derivatives controls
all curvature errors, with no derivatives of selected directions. -/
theorem fubini_commutator_identity
    (H M : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ)
    (C : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hM : M.IsSymm) (hC : ∀ l k i, C l k i = C k l i) (l k i j : Fin 3) :
    fubiniCubicVariation H C m M l k i j - fubiniCubicVariation H C m M k l i j =
      fubiniCommutator H (fun i j => M i j-m i*m j) l k i j +
        m k*(C l i j-fubiniCubic H m l i j)-
        m l*(C k i j-fubiniCubic H m k i j) := by
  unfold fubiniCubicVariation fubiniCommutator fubiniCubic
  rw [hM.apply l k, hC l k j, hC l k i]
  ring

/-- Contracting the curvature commutator extracts its scalar Hessian part. -/
theorem fubini_contracted_commutator
    (H R : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (hdet : IsUnit H.det)
    (l i : Fin 3) :
    (∑ k : Fin 3, ∑ j : Fin 3, H⁻¹ k j*fubiniCommutator H R l k i j) =
      3*R l i-(∑ k : Fin 3, ∑ j : Fin 3, H⁻¹ k j*R k j)*H l i := by
  calc
    _ = (∑ k : Fin 3, (H⁻¹*H) k k)*R l i+
        (∑ j : Fin 3, (H⁻¹*H) j i*R l j)-
        (∑ k : Fin 3, (H*H⁻¹) l k*R k i)-
        (∑ k : Fin 3, ∑ j : Fin 3, H⁻¹ k j*R k j)*H l i := by
      simp only [fubiniCommutator, Matrix.mul_apply, Fin.sum_univ_three]
      simp only [hH.apply, hH.inv.apply]
      ring
    _ = _ := by
      rw [Matrix.nonsing_inv_mul H hdet, Matrix.mul_nonsing_inv H hdet]
      simp [Matrix.one_apply]

private theorem abs_double_sum_three_bound (f : Fin 3 → Fin 3 → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ i j, |f i j| ≤ B) :
    |∑ i, ∑ j, f i j| ≤ 9*B := by
  calc
    _ ≤ ∑ i, ∑ j, |f i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, B :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hf i j
    _ = _ := by simp; ring

/-- The scalar Hessian error is linear in the differentiated cubic error. -/
theorem fubini_scalar_error_bound
    (H R : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (hdet : IsUnit H.det)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hinv : ∀ i j, |H⁻¹ i j| ≤ T)
    (hcomm : ∀ l k i j, |fubiniCommutator H R l k i j| ≤ ε) :
    ∀ l i,
      |R l i-((∑ k : Fin 3, ∑ j : Fin 3, H⁻¹ k j*R k j)/3)*H l i| ≤ 3*T*ε := by
  intro l i
  have hb : |∑ k : Fin 3, ∑ j : Fin 3, H⁻¹ k j*fubiniCommutator H R l k i j| ≤ 9*(T*ε) :=
    abs_double_sum_three_bound _ (mul_nonneg hT hε) (fun k j => by
      rw [abs_mul]
      exact mul_le_mul (hinv k j) (hcomm l k i j) (abs_nonneg _) hT)
  rw [fubini_contracted_commutator H R hH hdet] at hb
  have heq : 3*R l i-(∑ k : Fin 3, ∑ j : Fin 3, H⁻¹ k j*R k j)*H l i =
      3*(R l i-((∑ k : Fin 3, ∑ j : Fin 3, H⁻¹ k j*R k j)/3)*H l i) := by ring
  rw [heq, abs_mul] at hb
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 3)] at hb
  nlinarith

/-- One final contraction controls the derivative of the scalar curvature. -/
theorem fubini_contracted_vector
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (hdet : IsUnit H.det)
    (W : Fin 3 → ℝ) (k : Fin 3) :
    (∑ i : Fin 3, ∑ j : Fin 3, H⁻¹ i j*(W k*H i j-W i*H k j)) = 2*W k := by
  calc
    _ = W k*(∑ i : Fin 3, (H⁻¹*H) i i)-
        (∑ i : Fin 3, (H*H⁻¹) k i*W i) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_three]
      simp only [hH.apply, hH.inv.apply]
      ring
    _ = _ := by
      rw [Matrix.nonsing_inv_mul H hdet, Matrix.mul_nonsing_inv H hdet]
      simp [Matrix.one_apply]
      ring

theorem fubini_vector_error_bound
    (H : Matrix (Fin 3) (Fin 3) ℝ) (hH : H.IsSymm) (hdet : IsUnit H.det)
    (W : Fin 3 → ℝ) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hinv : ∀ i j, |H⁻¹ i j| ≤ T)
    (hwedge : ∀ k i j, |W k*H i j-W i*H k j| ≤ ε) :
    ∀ k, |W k| ≤ 5*T*ε := by
  intro k
  have hb : |∑ i : Fin 3, ∑ j : Fin 3, H⁻¹ i j*(W k*H i j-W i*H k j)| ≤ 9*(T*ε) :=
    abs_double_sum_three_bound _ (mul_nonneg hT hε) (fun i j => by
      rw [abs_mul]
      exact mul_le_mul (hinv i j) (hwedge k i j) (abs_nonneg _) hT)
  rw [fubini_contracted_vector H hH hdet, abs_mul] at hb
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 2)] at hb
  nlinarith [abs_nonneg (W k)]


/-- The curvature defect after extracting its scalar Hessian part. -/
def fubiniScalarDefect (H M : Matrix (Fin 3) (Fin 3) ℝ)
    (m : Fin 3 → ℝ) (lam : ℝ) (i j : Fin 3) : ℝ :=
  M i j-m i*m j-lam*H i j

/-- Formal derivative of the scalar curvature defect. -/
def fubiniScalarVariation (H : Matrix (Fin 3) (Fin 3) ℝ)
    (C : Fin 3 → Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) (N : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (lam : ℝ) (dlam : Fin 3 → ℝ) (k i j : Fin 3) : ℝ :=
  N k i j-M k i*m j-m i*M k j-dlam k*H i j-lam*C k i j

theorem fubini_scalar_commutator_identity
    (H M : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ)
    (C N : Fin 3 → Fin 3 → Fin 3 → ℝ) (lam : ℝ) (dlam : Fin 3 → ℝ)
    (hM : M.IsSymm) (hC : ∀ k i j, C k i j = C i k j)
    (hN : ∀ k i j, N k i j = N i k j) (k i j : Fin 3) :
    fubiniScalarVariation H C m M N lam dlam k i j-
        fubiniScalarVariation H C m M N lam dlam i k j =
      -(dlam k-lam*m k)*H i j+(dlam i-lam*m i)*H k j+
        m k*fubiniScalarDefect H M m lam i j-
        m i*fubiniScalarDefect H M m lam k j := by
  unfold fubiniScalarVariation fubiniScalarDefect
  rw [hM.apply k i, hC k i j, hN k i j]
  ring

/-- The final scalar derivative error is linear in the cubic defect and
its derivatives, after the Hessian inverse has been bounded. -/
theorem fubini_scalar_gradient_error_bound
    (H M : Matrix (Fin 3) (Fin 3) ℝ) (m : Fin 3 → ℝ)
    (C N : Fin 3 → Fin 3 → Fin 3 → ℝ) (lam : ℝ) (dlam : Fin 3 → ℝ)
    (hH : H.IsSymm) (hdet : IsUnit H.det)
    (hM : M.IsSymm) (hC : ∀ k i j, C k i j = C i k j)
    (hN : ∀ k i j, N k i j = N i k j)
    {T U τ τ1 : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) (hτ : 0 ≤ τ) (hτ1 : 0 ≤ τ1)
    (hinv : ∀ i j, |H⁻¹ i j| ≤ T) (hm : ∀ i, |m i| ≤ U)
    (hdef : ∀ i j, |fubiniScalarDefect H M m lam i j| ≤ τ)
    (hvar : ∀ k i j, |fubiniScalarVariation H C m M N lam dlam k i j| ≤ τ1) :
    ∀ k, |dlam k-lam*m k| ≤ 10*T*(U*τ+τ1) := by
  have hwedge : ∀ k i j,
      |(dlam k-lam*m k)*H i j-(dlam i-lam*m i)*H k j| ≤ 2*U*τ+2*τ1 := by
    intro k i j
    have hid := fubini_scalar_commutator_identity H M m C N lam dlam hM hC hN k i j
    have heq : (dlam k-lam*m k)*H i j-(dlam i-lam*m i)*H k j =
      m k*fubiniScalarDefect H M m lam i j-m i*fubiniScalarDefect H M m lam k j-
        fubiniScalarVariation H C m M N lam dlam k i j+
        fubiniScalarVariation H C m M N lam dlam i k j := by linarith
    rw [heq]
    calc
      _ ≤ (|m k*fubiniScalarDefect H M m lam i j|+
          |m i*fubiniScalarDefect H M m lam k j|)+
          |fubiniScalarVariation H C m M N lam dlam k i j|+
          |fubiniScalarVariation H C m M N lam dlam i k j| := by
        have h1 := abs_add_le
          (m k*fubiniScalarDefect H M m lam i j-m i*fubiniScalarDefect H M m lam k j-
            fubiniScalarVariation H C m M N lam dlam k i j)
          (fubiniScalarVariation H C m M N lam dlam i k j)
        have h2 := abs_sub
          (m k*fubiniScalarDefect H M m lam i j-m i*fubiniScalarDefect H M m lam k j)
          (fubiniScalarVariation H C m M N lam dlam k i j)
        have h3 := abs_sub (m k*fubiniScalarDefect H M m lam i j)
          (m i*fubiniScalarDefect H M m lam k j)
        linarith
      _ ≤ (U*τ+U*τ)+τ1+τ1 := by
        gcongr
        · exact (abs_mul _ _).trans_le (mul_le_mul (hm k) (hdef i j) (abs_nonneg _) hU)
        · exact (abs_mul _ _).trans_le (mul_le_mul (hm i) (hdef k j) (abs_nonneg _) hU)
        · exact hvar k i j
        · exact hvar i k j
      _ = _ := by ring
  intro k
  have hb := fubini_vector_error_bound H hH hdet (fun k => dlam k-lam*m k)
    hT (by positivity : 0 ≤ 2*U*τ+2*τ1) hinv hwedge k
  convert hb using 1 <;> ring

end

end Submission.Obl.k4_physical_parent_potential_candidates
