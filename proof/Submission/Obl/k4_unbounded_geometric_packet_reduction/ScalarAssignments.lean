import Submission.Obl.k4_unbounded_geometric_packet_reduction.ScalarCoordinates
import Submission.Lib.K4XInterface.Formats

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory MvPolynomial
open Submission.Lib.K4XInterface

noncomputable section

/-- Polynomial substitution keeps the test count and multiplies only the
degree bound. -/
theorem gfmt_polynomial_preimage {n m D d : ℕ} {H : ℝ} {S : Set (Fin n → ℝ)}
    (hS : gfmt n H D S) (f : Fin n → MvPolynomial (Fin m) ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ d) :
    gfmt m H (d * D) ((fun x i => eval x (f i)) ⁻¹' S) := by
  obtain ⟨k, hk, p, hp, rule, hrule⟩ := hS
  refine ⟨k, hk, fun i => aeval f (p i), ?_, rule, ?_⟩
  · intro i
    exact (Submission.Obl.k4_quadratic_atlas_normalization.degree_aeval_le_mul
      (p i) f d hf).trans (Nat.mul_le_mul_left d (hp i))
  · intro x
    simpa only [Set.mem_preimage,
      Submission.Obl.k4_eligibility_sign_description.eval_aeval_real] using
        hrule (fun i => eval x (f i))

theorem scalar_assignment_format (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q a : ℝ) (v : Fin 3 → ℝ)
    {H : ℝ} {D : ℕ} {S : Set (Fin 5 → ℝ)} (hS : gfmt 5 H D S) (i : ℕ) :
    gfmt 6 H (2 * D) {z : Fin 6 → ℝ | scalarCoeff P t₀ q a v (i, z) ∈ S} :=
  gfmt_polynomial_preimage hS _ (scalarCoeffPoly_degree P hP t₀ q a v)

theorem scalar_assignment_incidence_format (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (t₀ q a : ℝ) (v : Fin 3 → ℝ)
    {H : ℝ} {D : ℕ} {S : Set (Fin 5 → ℝ)} (hS : gfmt 5 H D S) (i : ℕ) :
    gfmt 7 H (2 * D)
      {z : Fin 7 → ℝ | scalarCoeff P t₀ q a v (i, fun j : Fin 6 => z j.castSucc) ∈ S} := by
  have hh := gfmt_polynomial_preimage hS
    (fun j => rename Fin.castSucc (scalarCoeffPoly P t₀ q a v j))
    (fun j => (totalDegree_rename_le _ _).trans (scalarCoeffPoly_degree P hP t₀ q a v j))
  have heq : {z : Fin 7 → ℝ |
      scalarCoeff P t₀ q a v (i, fun j : Fin 6 => z j.castSucc) ∈ S} =
      (fun z j => eval z (rename Fin.castSucc (scalarCoeffPoly P t₀ q a v j))) ⁻¹' S := by
    ext z
    change ((fun j => eval (fun k : Fin 6 => z k.castSucc)
      (scalarCoeffPoly P t₀ q a v j)) ∈ S) ↔
        (fun j => eval z (rename Fin.castSucc (scalarCoeffPoly P t₀ q a v j))) ∈ S
    simp only [eval_rename, Function.comp_def]
  rw [heq]
  exact hh

theorem scalarCoeff_measurable (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) : Measurable (scalarCoeff P t₀ q a v) := by
  apply Measurable.of_eval
  intro i
  exact (continuous_eval (scalarCoeffPoly P t₀ q a v i)).measurable.comp measurable_snd

/-- Off the fixed packet assignment, use the zero coefficient tuple.  This
does not affect the conditional prior, and makes Q0's global coefficient
bound a pointwise assertion on the entire trajectory space. -/
def clippedScalarCoeff (P : MvPolynomial (Fin 4) ℝ) (t₀ q a : ℝ) (v : Fin 3 → ℝ)
    (A : Set (ℕ × (Fin 6 → ℝ))) (l : ℕ × (Fin 6 → ℝ)) : Fin 5 → ℝ := by
  classical
  exact A.piecewise (scalarCoeff P t₀ q a v) (fun _ => 0) l

theorem clippedScalarCoeff_measurable (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) {A : Set (ℕ × (Fin 6 → ℝ))}
    (hA : MeasurableSet A) : Measurable (clippedScalarCoeff P t₀ q a v A) := by
  classical
  exact (scalarCoeff_measurable P t₀ q a v).piecewise hA measurable_const

theorem clippedScalarCoeff_eq (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) {A : Set (ℕ × (Fin 6 → ℝ))}
    {l : ℕ × (Fin 6 → ℝ)} (hl : l ∈ A) :
    clippedScalarCoeff P t₀ q a v A l = scalarCoeff P t₀ q a v l := by
  classical
  simp [clippedScalarCoeff, hl]

theorem clippedScalarCoeff_bound (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) {A : Set (ℕ × (Fin 6 → ℝ))}
    {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ l ∈ A, ∀ i, |scalarCoeff P t₀ q a v l i| ≤ K)
    (l : ℕ × (Fin 6 → ℝ)) (i : Fin 5) :
    |clippedScalarCoeff P t₀ q a v A l i| ≤ K := by
  classical
  by_cases hl : l ∈ A
  · simpa only [clippedScalarCoeff_eq P t₀ q a v hl] using hb l hl i
  · simpa [clippedScalarCoeff, hl] using hK

theorem clipped_assignment_eq (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) (A : Set (ℕ × (Fin 6 → ℝ)))
    (S : Set (Fin 5 → ℝ)) :
    A ∩ (clippedScalarCoeff P t₀ q a v A) ⁻¹' S =
      A ∩ (scalarCoeff P t₀ q a v) ⁻¹' S := by
  ext l
  constructor <;> rintro ⟨hl, hs⟩ <;>
    exact ⟨hl, by simpa only [Set.mem_preimage, clippedScalarCoeff_eq P t₀ q a v hl] using hs⟩

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
