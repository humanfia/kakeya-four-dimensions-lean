import Submission.Obl.k4_general_parent_projected_layers.Worlds
import Submission.Obl.k4_general_parent_projected_layers.Support.WorldObservation

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_fixed_budget_quadratic_recovery (scalarY scalarX)

noncomputable section

/-- The scalar world associated with one original four-coefficient crop. -/
def coefficientWorld {α : Type} (P : MvPolynomial (Fin 4) ℝ) (b : α → Fin 6 → ℝ)
    (K chi g : ℝ) (C : Set α) (u : Fin 4 → ℤ) : ScalarWorld α where
  crop := projectedWorldCrop C b chi g u
  tag := ![u 0, u 1]
  y₀ := projectedWorldRepresentatives K chi g u 2
  y₁ := projectedWorldRepresentatives K chi g u 3
  coeff := worldScalarCoefficients P b K chi g C u

theorem coefficientWorld_tags {α : Type} (P : MvPolynomial (Fin 4) ℝ) (b : α → Fin 6 → ℝ)
    (K chi g : ℝ) (C : Set α) (u : Fin 4 → ℤ) {l : α}
    (hl : l ∈ (coefficientWorld P b K chi g C u).crop) :
    ⌊b l 3 / chi⌋ = (coefficientWorld P b K chi g C u).tag 0 ∧
      ⌊b l 0 / chi⌋ = (coefficientWorld P b K chi g C u).tag 1 := by
  have h0 := congrFun hl.2 0
  have h1 := congrFun hl.2 1
  exact ⟨h0, h1⟩

theorem coefficientWorld_center {α : Type} (P : MvPolynomial (Fin 4) ℝ) (b : α → Fin 6 → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (chi g : ℝ) (C : Set α) (u : Fin 4 → ℤ) :
    |(coefficientWorld P b K chi g C u).y₀| + |(coefficientWorld P b K chi g C u).y₁| ≤ 2 * K := by
  exact (add_le_add (projectedWorldRepresentatives_bound (chi := chi) (g := g) hK u 2)
    (projectedWorldRepresentatives_bound (chi := chi) (g := g) hK u 3)).trans_eq (by ring)

theorem coefficientWorld_y {α : Type} (P : MvPolynomial (Fin 4) ℝ) (b : α → Fin 6 → ℝ)
    (K chi g : ℝ) (C : Set α) (u : Fin 4 → ℤ) {l : α}
    (hl : l ∈ (coefficientWorld P b K chi g C u).crop) (t : ℝ) :
    scalarY ((coefficientWorld P b K chi g C u).coeff l) t =
      ((Submission.Lib.K4ContactNormalization.point (b l) t) 2 -
        (coefficientWorld P b K chi g C u).y₀ -
          t * (coefficientWorld P b K chi g C u).y₁) / g :=
  nativeScalarCoefficients_y P b g _ _ hl t

theorem coefficientWorld_x {α : Type} (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (b : α → Fin 6 → ℝ) (K chi g : ℝ) (C : Set α) (u : Fin 4 → ℤ) {l : α}
    (hl : l ∈ (coefficientWorld P b K chi g C u).crop) (t : ℝ) :
    scalarX ((coefficientWorld P b K chi g C u).coeff l) t =
      eval (Submission.Lib.K4ContactNormalization.point (b l) t) P :=
  nativeScalarCoefficients_x P hP b g _ _ hl t

end

end Submission.Obl.k4_general_parent_projected_layers
