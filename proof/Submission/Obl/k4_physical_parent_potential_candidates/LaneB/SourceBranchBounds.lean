import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceMotion

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set Metric MvPolynomial

noncomputable section

namespace Analytic

/-- Small native curvature preserves a sharp derivative floor on the
actual root. This estimate uses the discriminant identity directly. -/
theorem root_derivative_lower_of_native_fit {a eps A phi bu cu w : ℝ}
    (hA : 2 ≤ A) (hroot : a*phi^2+bu*phi+cu=0)
    (hfit : |a*w^2+bu*w+cu| ≤ eps)
    (hlo : A⁻¹ ≤ |2*a*w+bu|)
    (hsmall : 4*|a| *eps ≤ (2*A^2)⁻¹) :
    (2*A)⁻¹ ≤ |2*a*phi+bu| := by
  have hA0 : 0 < A := by linarith
  have hcorr : |4*a*(a*w^2+bu*w+cu)| ≤ (2*A^2)⁻¹ := by
    calc
      _ = 4*|a| *|a*w^2+bu*w+cu| := by rw [abs_mul,abs_mul]; norm_num
      _ ≤ 4*|a| *eps := mul_le_mul_of_nonneg_left hfit (by positivity)
      _ ≤ _ := hsmall
  have hsq : (A^2)⁻¹ ≤ (2*a*w+bu)^2 := by
    simpa only [inv_pow,sq_abs] using pow_le_pow_left₀ (by positivity) hlo 2
  have hid : (2*a*phi+bu)^2 = (2*a*w+bu)^2-4*a*(a*w^2+bu*w+cu) := by
    linear_combination 4*a*hroot
  have hlow : (A^2)⁻¹-(2*A^2)⁻¹ ≤ (2*a*phi+bu)^2 := by
    rw [hid]
    linarith only [hsq,(abs_le.mp hcorr).2]
  have hquarter : ((2*A)⁻¹)^2 ≤ (A^2)⁻¹-(2*A^2)⁻¹ := by
    have hpos : 0 ≤ (A^2)⁻¹ := by positivity
    have heq : ((2*A)⁻¹)^2 = (A^2)⁻¹/4 := by field_simp; ring
    have heq2 : (2*A^2)⁻¹ = (A^2)⁻¹/2 := by field_simp
    rw [heq,heq2]
    linarith only [hpos]
  apply (sq_le_sq₀ (by positivity : 0 ≤ (2*A)⁻¹) (abs_nonneg _)).mp
  simpa only [sq_abs] using hquarter.trans hlow

/-- An actual normalized source incidence supplies the graph band and
the sharp hidden derivative floor required by normalized restoration. -/
theorem band_and_regular_of_normalizedGroupPoint
    {S0 : Poly} {P0 : MvPolynomial (Fin 3) ℝ} {eps A sigma a : ℝ}
    {Bp Cp : MvPolynomial (Fin 3) ℝ} {f : Base → ℝ}
    (hA : 2 ≤ A) (heps : 0 < eps) (hsmall : 4*|a| *eps ≤ (2*A^2)⁻¹)
    (hroot : ∀ z∈ball (0:Base) 4,
      a*(f z)^2+eval (fun i => z i) Bp*f z+eval (fun i => z i) Cp=0 ∧
      0 < (2*a*f z+eval (fun i => z i) Bp)*sigma)
    (hSeq : ∀ (z:Base) (w:ℝ), eval ![z 0,z 1,z 2,w] S0-eval (fun i => z i) P0=
      a*w^2+eval (fun i => z i) Bp*w+eval (fun i => z i) Cp)
    (hSd : ∀ (z:Base) (w:ℝ), eval ![z 0,z 1,z 2,w] (pderiv 3 S0)=
      2*a*w+eval (fun i => z i) Bp)
    {z:Base} {w:ℝ} (hzw : NormalizedGroupPoint S0 P0 eps A sigma z w) :
    |w-f z| ≤ eps*A^19 ∧ (2*A)⁻¹ ≤ |2*a*f z+eval (fun i => z i) Bp| := by
  refine ⟨band_of_normalizedGroupPoint hA heps hsmall hroot hSeq hSd hzw,?_⟩
  apply root_derivative_lower_of_native_fit hA (hroot z hzw.1).1
    (w := w)
  · simpa only [hSeq] using hzw.2.1
  · simpa only [hSd] using hzw.2.2.2.1
  · exact hsmall

end Analytic

end

end Submission.Obl.k4_physical_parent_potential_candidates
