/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/FiniteBooleanFormat.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/FiniteBooleanFormat.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Definitions
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

/-! Joint finite Boolean tables use the sum of their polynomial tests.
In particular counting crossing charts does not multiply their degrees.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MvPolynomial Set
open scoped Classical

theorem fmt.of_fintype_tests {n D : ℕ} {ι : Type*} [Fintype ι]
    (p : ι → MvPolynomial (Fin n) ℝ) (hp : ∀ i, (p i).totalDegree ≤ D)
    (b : (ι → Bool) → Bool) {H : ℝ} (hH : (Fintype.card ι : ℝ) ≤ H) :
    fmt n H D {x | b (fun i => decide (0 ≤ eval x (p i))) = true} := by
  classical
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, hH, fun i => p (e.symm i), fun i => hp _,
    fun v => b (fun i => v (e i)), ?_⟩
  intro x
  simp only [mem_ofPred_eq, Equiv.symm_apply_apply]

/-- An arbitrary finite Boolean combination preserves the sum of the input budgets. -/
theorem fmt.boolean {n D : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (Fin n → ℝ)) (H : ι → ℝ)
    (hS : ∀ i, fmt n (H i) D (S i)) (b : (ι → Bool) → Bool) :
    fmt n (∑ i, H i) D {x | b (fun i => decide (x ∈ S i)) = true} := by
  classical
  choose m hm p hp b₀ hb using hS
  let tests : (Σ i, Fin (m i)) → MvPolynomial (Fin n) ℝ := fun ij => p ij.1 ij.2
  have hcard : (Fintype.card (Σ i, Fin (m i)) : ℝ) ≤ ∑ i, H i := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hm i
  have h := fmt.of_fintype_tests tests (fun ij => hp ij.1 ij.2)
    (fun v => b (fun i => b₀ i (fun j => v ⟨i, j⟩))) hcard
  convert h using 1
  ext x
  simp only [mem_ofPred_eq]
  have hbits : (fun i => decide (x ∈ S i)) =
      (fun i => b₀ i (fun j => decide (0 ≤ eval x (tests ⟨i, j⟩)))) := by
    funext i
    simp only [hb i x, Bool.decide_coe, tests]
  rw [hbits]

/-- A finite existential quantifier is a Boolean table of the same total budget. -/
theorem fmt.exists_finite {n D : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (Fin n → ℝ)) (H : ι → ℝ) (hS : ∀ i, fmt n (H i) D (S i)) :
    fmt n (∑ i, H i) D {x | ∃ i, x ∈ S i} := by
  classical
  have h := fmt.boolean S H hS (fun v => decide (∃ i, v i = true))
  simpa only [decide_eq_true_eq] using h

/-- A threshold on the number of successful tests is again one finite Boolean table. -/
theorem fmt.count_le {n D : ℕ} {ι : Type*} [Fintype ι]
    (S : ι → Set (Fin n → ℝ)) (H : ι → ℝ) (hS : ∀ i, fmt n (H i) D (S i))
    (bound : ℝ) :
    fmt n (∑ i, H i) D
      {x | (((Finset.univ : Finset ι).filter (fun i => x ∈ S i)).card : ℝ) ≤ bound} := by
  classical
  have h := fmt.boolean S H hS
    (fun v => decide ((((Finset.univ : Finset ι).filter (fun i => v i = true)).card : ℝ) ≤ bound))
  simpa only [decide_eq_true_eq] using h

end Submission.Obl.k4_balanced_native_packet_transport.CPF
