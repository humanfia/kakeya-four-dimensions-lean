import Submission.Obl.k4_conditional_common_affine_field.FieldFromAxes

namespace Submission.Obl.k4_conditional_common_affine_field

def returnDegree (P : ℕ) : ℕ := (P+3)*3+6

theorem gridError_bound (P : ℕ) {B H e ω : ℝ}
    (hB : 1000 ≤ B) (hH : H ≤ B) (he : 0 ≤ e) (hω : ω ≤ e) :
    gridError P B H e ω ≤ B^(P+2)*e := by
  have hB0 : 0 ≤ B := by linarith
  have hscale : 3*B+1 ≤ B^2 := by nlinarith [mul_nonneg hB0 (show 0 ≤ B-4 by linarith)]
  have hin : 3*H*e+ω ≤ (3*B+1)*e := by
    nlinarith [mul_le_mul_of_nonneg_right hH he]
  calc
    _ ≤ B^P*((3*B+1)*e) := mul_le_mul_of_nonneg_left hin (pow_nonneg hB0 _)
    _ ≤ B^P*(B^2*e) := by gcongr
    _ = B^(P+2)*e := by rw [pow_add]; ring

theorem mixedError_bound (P : ℕ) {B K H e ω : ℝ}
    (hB : 1000 ≤ B) (hK0 : 0 ≤ K) (hH0 : 0 ≤ H)
    (hK : K ≤ B) (hH : H ≤ B) (he : 0 ≤ e) (hω0 : 0 ≤ ω) (hω : ω ≤ e) :
    mixedError P B K H e ω ≤ B^((P+3)*3+1)*e := by
  have hB0 : 0 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hgrid := gridError_bound P hB hH he hω
  have hBpow : B ≤ B^(P+2) := by
    simpa only [pow_one] using pow_le_pow_right₀ hB1 (show 1 ≤ P+2 by omega)
  have hsum : gridError P B H e ω+K*e ≤ B^(P+3)*e := by
    have hKe : K*e ≤ B^(P+2)*e := mul_le_mul_of_nonneg_right (hK.trans hBpow) he
    calc
      _ ≤ 2*B^(P+2)*e := by linarith
      _ ≤ B*B^(P+2)*e := by gcongr; linarith
      _ = B^(P+3)*e := by rw [show P+3=(P+2)+1 by omega,pow_succ]; ring
  have hsum0 : 0 ≤ gridError P B H e ω+K*e := by
    unfold gridError
    positivity
  have hKK : K*K ≤ B^2 := by
    simpa only [pow_two] using mul_le_mul hK hK hK0 hB0
  have h96 : 96*B^2 ≤ B^3 := by
    nlinarith [mul_nonneg (sq_nonneg B) (show 0 ≤ B-96 by linarith)]
  have hfactor : 96*K*K/((B^P)⁻¹) ≤ B^(P+3) := by
    rw [div_inv_eq_mul]
    calc
      _ ≤ (96*B^2)*B^P := mul_le_mul_of_nonneg_right (by nlinarith) (pow_nonneg hB0 _)
      _ ≤ B^3*B^P := mul_le_mul_of_nonneg_right h96 (pow_nonneg hB0 _)
      _ = B^(P+3) := by rw [pow_add]; ring
  have hfactor0 : 0 ≤ 96*K*K/((B^P)⁻¹) := by positivity
  unfold mixedError
  calc
    _ ≤ 8*(B^(P+3))^2*(B^(P+3)*e) := by
      apply mul_le_mul _ hsum hsum0 (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfactor0 hfactor 2) (by norm_num)
    _ = 8*(B^(P+3))^3*e := by ring
    _ ≤ B*(B^(P+3))^3*e := by gcongr; linarith
    _ = B^((P+3)*3+1)*e := by
      conv_rhs => rw [pow_succ,pow_mul]
      ring

theorem returnError_bound (P : ℕ) {B K H e ω ρ : ℝ}
    (hB : 1000 ≤ B) (hK0 : 0 ≤ K) (hH0 : 0 ≤ H)
    (hK : K ≤ B) (hH : H ≤ B) (he : 0 ≤ e) (hω0 : 0 ≤ ω) (hω : ω ≤ e)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    returnError P B K H e ω ρ ≤ B^(returnDegree P)*e/ρ^2 := by
  have hB0 : 0 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hr2 : 0 < ρ^2 := sq_pos_of_pos hρ
  have hr21 : ρ^2 ≤ 1 := by nlinarith
  let q := (P+3)*3+1
  have hQ : mixedError P B K H e ω ≤ B^q*e :=
    mixedError_bound P hB hK0 hH0 hK hH he hω0 hω
  have hQ0 : 0 ≤ mixedError P B K H e ω := by unfold mixedError gridError; positivity
  have hHsquared : (2*H)^2 ≤ 4*B^2 := by
    nlinarith [mul_le_mul hH hH hH0 hB0]
  have hprod : mixedError P B K H e ω*(2*H)^2 ≤ B^(q+3)*e := by
    calc
      _ ≤ (B^q*e)*(4*B^2) := mul_le_mul hQ hHsquared (sq_nonneg _) (by positivity)
      _ = 4*B^(q+2)*e := by rw [pow_add]; ring
      _ ≤ B*B^(q+2)*e := by gcongr; linarith
      _ = B^(q+3)*e := by rw [show q+3=(q+2)+1 by omega,pow_succ]; ring
  have hgrid : gridError P B H e ω ≤ B^(q+3)*e := by
    apply (gridError_bound P hB hH he hω).trans
    apply mul_le_mul_of_nonneg_right _ he
    apply pow_le_pow_right₀ hB1
    dsimp [q]
    omega
  have hbig0 : 0 ≤ B^(q+3)*e := by positivity
  have hgrid' : gridError P B H e ω ≤ B^(q+3)*e/ρ^2 := by
    apply hgrid.trans
    apply (le_div_iff₀ hr2).mpr
    nlinarith
  have htwo : 2 ≤ B^2 := by nlinarith
  unfold returnError
  calc
    _ ≤ B^(q+3)*e/ρ^2+B^(q+3)*e/ρ^2 :=
      add_le_add hgrid' (div_le_div_of_nonneg_right hprod hr2.le)
    _ = 2*B^(q+3)*e/ρ^2 := by ring
    _ ≤ B^2*B^(q+3)*e/ρ^2 := by gcongr
    _ = B^(returnDegree P)*e/ρ^2 := by
      have hd : returnDegree P=q+5 := by dsimp [returnDegree,q] <;> omega
      have hpow : B^(q+5)=B^2*B^(q+3) := by
        rw [show q+5=2+(q+3) by omega,pow_add]
      rw [hd,hpow]

theorem coefficient_budget_bound (P : ℕ) {B H : ℝ}
    (hB : 1000 ≤ B) (hH0 : 0 ≤ H) (hH : H ≤ B) :
    4*(B^P)*H ≤ B^(returnDegree P) := by
  have hB0 : 0 ≤ B := by linarith
  have hB1 : 1 ≤ B := by linarith
  calc
    _ ≤ B*(B^P)*B := by gcongr; linarith
    _ = B^(P+2) := by rw [pow_add]; ring
    _ ≤ _ := pow_le_pow_right₀ hB1 (by dsimp [returnDegree]; omega)

end Submission.Obl.k4_conditional_common_affine_field
