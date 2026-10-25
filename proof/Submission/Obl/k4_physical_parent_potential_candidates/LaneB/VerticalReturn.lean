import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.QuadraticTube
import Submission.Obl.k4_physical_parent_potential_candidates.Analytic.TransportBounds

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

open MvPolynomial QuadraticTube FubiniQuadric

noncomputable section

namespace VerticalReturn

def affine (c : ℝ) (L : Fin 3 → ℝ) (u : Base) : ℝ := c+∑ i : Fin 3, L i*u i

def substitution (c : ℝ) (L : Fin 3 → ℝ) (s : ℝ) : Fin 4 → Poly :=
  ![X 0,X 1,X 2,C s⁻¹*height c L]

def pull (c : ℝ) (L : Fin 3 → ℝ) (s : ℝ) (Q : Poly) : Poly :=
  bind₁ (substitution c L s) Q

/-- Return from `g=(f-affine)/s`, multiplying the equation by `s` so that
its signed vertical derivative is preserved exactly. -/
def polynomial (c : ℝ) (L : Fin 3 → ℝ) (s : ℝ) (Q : Poly) : Poly := C s*pull c L s Q

theorem degree_pull (c : ℝ) (L : Fin 3 → ℝ) (s : ℝ) (Q : Poly) :
    (pull c L s Q).totalDegree ≤ Q.totalDegree := by
  apply Submission.Obl.k4_quadratic_selector_sweep.totalDegree_bind_affine
  intro i
  fin_cases i
  · change (X (0:Fin 4):Poly).totalDegree ≤ 1
    simp
  · change (X (1:Fin 4):Poly).totalDegree ≤ 1
    simp
  · change (X (2:Fin 4):Poly).totalDegree ≤ 1
    simp
  · change (C s⁻¹*height c L).totalDegree ≤ 1
    exact (totalDegree_mul _ _).trans (by simpa using degree_height c L)

theorem degree_polynomial (c : ℝ) (L : Fin 3 → ℝ) (s : ℝ) (Q : Poly) :
    (polynomial c L s Q).totalDegree ≤ Q.totalDegree := by
  exact (totalDegree_mul _ _).trans (by simpa using degree_pull c L s Q)

theorem eval_pull (c : ℝ) (L : Fin 3 → ℝ) (s : ℝ) (Q : Poly) (u : Base) (w : ℝ) :
    ev (pull c L s Q) u w = ev Q u ((w-affine c L u)/s) := by
  unfold pull ev
  change eval₂Hom (RingHom.id ℝ) (point u w) (bind₁ _ Q) = _
  rw [eval₂Hom_bind₁]
  apply congrArg (fun f : Fin 4 → ℝ => eval₂Hom (RingHom.id ℝ) f Q)
  have hp (u:Base) (w:ℝ) : point u w = ![u 0,u 1,u 2,w] := by
    funext i
    fin_cases i <;> rfl
  simp only [hp]
  funext i
  fin_cases i <;> simp [substitution, height, baseLinear, affine, Fin.sum_univ_three,
    div_eq_mul_inv] <;> ring

theorem eval_polynomial (c : ℝ) (L : Fin 3 → ℝ) (s : ℝ) (Q : Poly) (u : Base) (w : ℝ) :
    ev (polynomial c L s Q) u w = s*ev Q u ((w-affine c L u)/s) := by
  change eval (point u w) (C s*pull c L s Q) = _
  rw [map_mul, eval_C]
  exact congrArg (fun z:ℝ => s*z) (eval_pull c L s Q u w)

theorem hidden_substitution (c : ℝ) (L : Fin 3 → ℝ) (s : ℝ) (i : Fin 4) :
    pderiv (3:Fin 4) (substitution c L s i) = if i=3 then C s⁻¹ else 0 := by
  fin_cases i <;> simp [substitution, pderiv_height]

theorem pderiv_pull (c : ℝ) (L : Fin 3 → ℝ) (s : ℝ) (Q : Poly) :
    pderiv (3:Fin 4) (pull c L s Q) = C s⁻¹*pull c L s (pderiv (3:Fin 4) Q) :=
  pderiv_bind_hidden _ s⁻¹ (hidden_substitution c L s) Q

theorem pderiv_polynomial (c : ℝ) (L : Fin 3 → ℝ) {s : ℝ} (hs : s ≠ 0) (Q : Poly) :
    pderiv (3:Fin 4) (polynomial c L s Q) = pull c L s (pderiv (3:Fin 4) Q) := by
  rw [polynomial, pderiv_C_mul, pderiv_pull, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hs, map_one,
    one_mul]

theorem eval_hidden_derivatives (c : ℝ) (L : Fin 3 → ℝ) {s : ℝ} (hs : s ≠ 0)
    (Q : Poly) (u : Base) (w : ℝ) :
    ev (pderiv (3:Fin 4) (polynomial c L s Q)) u w =
      ev (pderiv (3:Fin 4) Q) u ((w-affine c L u)/s) ∧
    ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) (polynomial c L s Q))) u w =
      s⁻¹*ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u ((w-affine c L u)/s) := by
  rw [pderiv_polynomial c L hs, pderiv_pull, eval_pull]
  refine ⟨rfl,?_⟩
  change eval (point u w) (C s⁻¹*pull c L s _) = _
  rw [map_mul, eval_C]
  exact congrArg (fun z:ℝ => s⁻¹*z) (eval_pull c L s _ u w)

theorem coefficient_bound {c s H Z : ℝ} {L : Fin 3 → ℝ}
    (hH : 1 ≤ H) (hZ : 0 ≤ Z) (hc : |c| ≤ H) (hL : ∀ i, |L i| ≤ H)
    (hs : |s| ≤ H) (hsI : |s⁻¹| ≤ H) (Q : Poly) (hdeg : Q.totalDegree ≤ 2)
    (hcoeff : ∀ e, |Q.coeff e| ≤ Z) (e : Fin 4 →₀ ℕ) :
    |(polynomial c L s Q).coeff e| ≤ 2025*Z*H^5 := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hH2 : 1 ≤ 5*H^2 := by nlinarith [one_le_pow₀ hH (n:=2)]
  have hv : ∀ i, coefficientMass (substitution c L s i) ≤ 5*H^2 := by
    intro i
    fin_cases i
    all_goals first
    | simpa [substitution] using hH2
    | change coefficientMass (C s⁻¹*height c L) ≤ _
      apply (coefficientMass_mul_le _ _).trans
      have hh : coefficientMass (height c L) ≤ 5*H := mass_height hH L hc hL
      calc _ ≤ H*(5*H) := mul_le_mul (by simpa using hsI) hh
              (coefficientMass_nonneg _) hH0
        _ = _ := by ring
  have hmass : coefficientMass Q ≤ 81*Z := by
    simpa using coefficientMass_le_of_degree Q hdeg hZ hcoeff
  calc _ ≤ coefficientMass (polynomial c L s Q) := abs_coeff_le_coefficientMass _ _
    _ ≤ |s| *coefficientMass (pull c L s Q) := by
      simpa only [polynomial, coefficientMass_C] using coefficientMass_mul_le (C s) (pull c L s Q)
    _ ≤ H*(coefficientMass Q*(5*H^2)^Q.totalDegree) :=
      mul_le_mul hs (coefficientMass_bind_le _ _ hH2 hv) (coefficientMass_nonneg _) hH0
    _ ≤ H*((81*Z)*(5*H^2)^2) := by
      apply mul_le_mul_of_nonneg_left _ hH0
      exact mul_le_mul hmass (pow_le_pow_right₀ hH2 hdeg) (by positivity) (by positivity)
    _ = _ := by ring

/-- Return all tube estimates from a normalized graph, with linear value
error and an unchanged signed vertical derivative. -/
theorem tube_certificate (c : ℝ) (L : Fin 3 → ℝ) {s B ε : ℝ}
    (hs : 0 < s) (_hB : 0 ≤ B) (f : Base → ℝ) (U : Set Base) (Q : Poly)
    (hQ : ∀ u ∈ U, ∀ v : ℝ, B*|v-(f u-affine c L u)/s| ≤ 1 →
      |ev Q u v| ≤ B*(ε+|v-(f u-affine c L u)/s|) ∧
      B⁻¹ ≤ ev (pderiv (3:Fin 4) Q) u v ∧
      ev (pderiv (3:Fin 4) Q) u v ≤ B ∧
      |ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) Q)) u v| ≤ B) :
    ∀ u ∈ U, ∀ w : ℝ, B*|w-f u| ≤ s →
      |ev (polynomial c L s Q) u w| ≤ B*(s*ε+|w-f u|) ∧
      B⁻¹ ≤ ev (pderiv (3:Fin 4) (polynomial c L s Q)) u w ∧
      ev (pderiv (3:Fin 4) (polynomial c L s Q)) u w ≤ B ∧
      |ev (pderiv (3:Fin 4) (pderiv (3:Fin 4) (polynomial c L s Q))) u w| ≤ B/s := by
  intro u hu w hw
  have he : |(w-affine c L u)/s-(f u-affine c L u)/s| = |w-f u|/s := by
    rw [← sub_div, abs_div, abs_of_pos hs]
    congr 2
    ring
  have hsmall : B*|(w-affine c L u)/s-(f u-affine c L u)/s| ≤ 1 := by
    rw [he, ← mul_div_assoc]
    exact (div_le_one hs).2 hw
  obtain ⟨hv,hl,hu',hc⟩ := hQ u hu _ hsmall
  obtain ⟨hd1,hd2⟩ := eval_hidden_derivatives c L hs.ne' Q u w
  refine ⟨?_,by rwa [hd1],by rwa [hd1],?_⟩
  · rw [eval_polynomial, abs_mul, abs_of_pos hs]
    rw [he] at hv
    calc _ ≤ s*(B*(ε+|w-f u|/s)) := mul_le_mul_of_nonneg_left hv hs.le
      _ = _ := by field_simp
  · rw [hd2, abs_mul, abs_of_pos (inv_pos.mpr hs)]
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hs.le)

end VerticalReturn

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
