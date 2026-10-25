import Submission.Obl.k4_scalar_initial_true_horizon.Format
import Submission.Lib.K4FinitePlankAtlases.Assignments

/-! Finite priority assignments have a linear polynomial atom budget. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set MvPolynomial
open scoped BigOperators

/-- Any Boolean rule in finitely many formatted sets uses at most the sum of
those sets' polynomial atoms. The rule itself adds no atoms. -/
theorem Format.of_membership_rule {n t D : ℕ} {B : ℝ} (hB : 1 ≤ B)
    (R : Fin t → ℝ) (A : Fin t → Set (Fin n → ℝ))
    (hA : ∀ i, Format n (R i) D (A i)) (hcount : ∑ i, R i ≤ B)
    (S : Set (Fin t → Prop)) :
    Format n B D {x | (fun i => x ∈ A i) ∈ S} := by
  classical
  choose m hm p hp U hU using hA
  let ι := (i : Fin t) × Fin (m i)
  have hcard : (Fintype.card ι : ℝ) ≤ B := by
    apply le_trans _ hcount
    simpa only [ι, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hm i))
  let V : Set (ι → SignType) :=
    {s | (fun i => (fun j => s ⟨i, j⟩) ∈ U i) ∈ S}
  have hformat := Format.of_family hB hcard
    (fun a : ι => p a.1 a.2) (fun a => (hp a.1 a.2).1) V
  convert hformat using 1
  ext x
  simp only [V, hU, mem_ofPred_eq]

/-- First-fit deletion has linear atom complexity in the number of candidates. -/
theorem Format.firstAssignment {n t D : ℕ} {B R : ℝ}
    (hB : 1 ≤ B) (hcount : (t : ℝ) * R ≤ B)
    (A : Fin t → Set (Fin n → ℝ)) (hA : ∀ i, Format n R D (A i)) (i : Fin t) :
    Format n B D (Submission.Lib.K4FinitePlankAtlases.firstAssignment A i) := by
  have h := Format.of_membership_rule hB (fun _ => R) A hA
    (by simpa using hcount) {s | s i ∧ ∀ j, j < i → ¬ s j}
  exact h

end Submission.Obl.k4_scalar_initial_true_horizon
