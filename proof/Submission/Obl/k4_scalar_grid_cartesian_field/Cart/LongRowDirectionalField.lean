-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/LongRowDirectionalField.lean;
-- only the namespace was renamed into o230's.
import Submission.Lib.K4ScalarActualSwitching.LongRowFits
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

theorem directional_residual_le_of_component_fits (T G₀ G₁ F₀ F₁ v V E₀ E₁ : ℝ)
    (hV : |v| ≤ V) (hgraph : |T-G₀-v*G₁| ≤ E₀)
    (hfield₀ : |G₀-F₀| ≤ E₁) (hfield₁ : |G₁-F₁| ≤ E₁) :
    |T-F₀-v*F₁| ≤ E₀+(1+V)*E₁ := by
  have hV0 : 0 ≤ V := (abs_nonneg v).trans hV
  have htri := abs_add_le (T-G₀-v*G₁) ((G₀-F₀)+v*(G₁-F₁))
  have heq : (T-G₀-v*G₁)+((G₀-F₀)+v*(G₁-F₁))=T-F₀-v*F₁ := by ring
  rw [heq] at htri
  have hfield : |(G₀-F₀)+v*(G₁-F₁)| ≤ E₁+V*E₁ := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    exact add_le_add hfield₀ (mul_le_mul hV hfield₁ (abs_nonneg _) hV0)
  exact htri.trans (add_le_add hgraph hfield) |>.trans_eq (by ring)

/-- A field fit and the actual graph equation on one long original row
give the directional equation throughout the block. The extension is
the accepted polynomial Remez theorem, applied to the combined row. -/
theorem directional_field_fit_of_long_row (P : Fin 2 → MvPolynomial (Fin 2) ℝ)
    (D : ℕ) (hP : ∀ i, (P i).totalDegree ≤ D)
    (T : Polynomial ℝ) (hT : T.natDegree ≤ 2)
    (u v V η E₀ E₁ : ℝ) (S : Set ℝ) (G : Fin 2 → ℝ → ℝ)
    (hV : |v| ≤ V) (hη : 0 < η) (hη1 : η ≤ 1) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hS : S ⊆ Icc (-1 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hgraph : ∀ t ∈ S, |T.eval t-G 0 t-v*G 1 t| ≤ E₀)
    (hfield : ∀ t ∈ S, ∀ i, |G i t-eval ![t,u+t*v] (P i)| ≤ E₁) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      |T.eval t-eval ![t,u+t*v] (P 0)-v*eval ![t,u+t*v] (P 1)| ≤
        (16*((D : ℝ)+3)/η)^(D+2)*(E₀+(1+V)*E₁) := by
  let Q := P 0+MvPolynomial.C v*P 1
  have hQ : Q.totalDegree ≤ D :=
    degree_add_le (hP 0) ((degree_C_mul_le _ _).trans (hP 1))
  have hV0 : 0 ≤ V := (abs_nonneg v).trans hV
  have hbound (t : ℝ) (ht : t ∈ S) :
      |eval ![t,u+t*v] Q-T.eval t| ≤ E₀+(1+V)*E₁ := by
    have h := directional_residual_le_of_component_fits (T.eval t) (G 0 t) (G 1 t)
      (eval ![t,u+t*v] (P 0)) (eval ![t,u+t*v] (P 1)) v V E₀ E₁ hV
      (hgraph t ht) (hfield t ht 0) (hfield t ht 1)
    simpa only [Q,map_add,map_mul,eval_C,abs_sub_comm,sub_add_eq_sub_sub,mul_comm] using h
  have h := scalar_quadratic_fit_of_long_row Q D hQ T hT u v S hη hη1
    (by positivity) hS hmass hbound
  intro t ht
  have ht' := h t ht
  simpa only [Q,map_add,map_mul,eval_C,abs_sub_comm,sub_add_eq_sub_sub,mul_comm] using ht'

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
