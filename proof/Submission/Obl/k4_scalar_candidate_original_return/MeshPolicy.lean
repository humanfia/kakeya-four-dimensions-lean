import Submission.Obl.k4_scalar_candidate_original_return.Defs
import Submission.Lib.K4MeshListRecovery.MeshFormat
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.CrossingPolynomials
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Format

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4MeshListRecovery

noncomputable section

/-- The observer retains the exact scalar base and the original hidden bin. -/
def originalObservation (δ : ℝ) (p : Inc) : Base × ℤ :=
  (![p.2, y p.1 p.2], ⌊x p.1 p.2 / δ⌋)

lemma measurable_originalObservation (δ : ℝ) : Measurable (originalObservation δ) := by
  unfold originalObservation
  dsimp [x, y, k4_scalar_linear_critical_extremizers.Split.x,
    k4_scalar_linear_critical_extremizers.Split.y]
  fun_prop

/-- A base mesh retains the original hidden tag, without averaging that tag. -/
def observationMeshTag (ρ : ℝ) (z : Base × ℤ) : Fin 3 → ℤ :=
  ![⌊z.1 0 / ρ⌋, ⌊z.1 1 / ρ⌋, z.2]

def observationMeshCode (ρ : ℝ) (F : Finset (Fin 3 → ℤ)) (z : Base × ℤ) : Option F :=
  finiteObservedCode F (observationMeshTag ρ) z

lemma measurable_observationMeshTag (ρ : ℝ) : Measurable (observationMeshTag ρ) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [observationMeshTag] <;> fun_prop

lemma observationMeshCode_fiber (ρ : ℝ) (F : Finset (Fin 3 → ℤ)) (c : Option F) :
    MeasurableSet {z | observationMeshCode ρ F z = c} :=
  measurableSet_finiteObservedCode F (observationMeshTag ρ)
    (fun c => (measurableSet_singleton c).preimage (measurable_observationMeshTag ρ)) c

/-- The actual finite rule supplied to the original terminal observer. -/
def meshLists {n : ℕ} (ρ : ℝ) (F : Finset (Fin 3 → ℤ))
    (table : Option F → Finset (Fin n)) : (Base × ℤ) → Finset (Fin n) :=
  fun z => table (observationMeshCode ρ F z)

lemma meshLists_card {n D : ℕ} (ρ : ℝ) (F : Finset (Fin 3 → ℤ))
    (table : Option F → Finset (Fin n)) (hD : ∀ c, (table c).card ≤ D) (z : Base × ℤ) :
    (meshLists ρ F table z).card ≤ D := hD _

lemma meshLists_measurable {n : ℕ} (ρ : ℝ) (F : Finset (Fin 3 → ℤ))
    (table : Option F → Finset (Fin n)) (i : Fin n) :
    MeasurableSet {z | i ∈ meshLists ρ F table z} := by
  classical
  have heq : {z | i ∈ meshLists ρ F table z} =
      ⋃ c : Option F, if i ∈ table c then {z | observationMeshCode ρ F z = c} else ∅ := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, Set.mem_ite_empty_right]
    constructor
    · intro hz
      exact ⟨observationMeshCode ρ F z, hz, rfl⟩
    · rintro ⟨c, hi, hc⟩
      simpa only [meshLists, hc] using hi
  rw [heq]
  apply MeasurableSet.iUnion
  intro c
  split
  · exact observationMeshCode_fiber ρ F c
  · exact MeasurableSet.empty

/-- Pulling a finite observer lookup back to the original coefficient/time
coordinates uses at most six tests per mesh cell, all of degree at most three. -/
lemma meshLists_format {n : ℕ} (ρ δ : ℝ) (F : Finset (Fin 3 → ℤ))
    (table : Option F → Finset (Fin n)) (i : Fin n) (z : ℕ) :
    Format 6 (6 * (F.card : ℝ) + 1) 3
      {w | i ∈ meshLists ρ F table
        (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5))} := by
  let P : Fin 3 → MvPolynomial (Fin 6) ℝ :=
    ![k4_scalar_true_atlas_terminal_lists.timePolynomial,
      k4_scalar_true_atlas_terminal_lists.spatialPolynomial,
      k4_scalar_true_atlas_terminal_lists.hiddenPolynomial]
  let widths : Fin 3 → ℝ := ![ρ, ρ, δ]
  have hP (j : Fin 3) : (P j).totalDegree ≤ 3 := by
    fin_cases j
    · exact k4_scalar_true_atlas_terminal_lists.timePolynomial_degree.trans (by omega)
    · exact k4_scalar_true_atlas_terminal_lists.spatialPolynomial_degree.trans (by omega)
    · exact k4_scalar_true_atlas_terminal_lists.hiddenPolynomial_degree
  have htag : (fun w j => (⌊MvPolynomial.eval w (P j) / widths j⌋ : ℤ)) =
      fun w => observationMeshTag ρ
        (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5)) := by
    funext w j
    fin_cases j <;> simp [P, widths, observationMeshTag, originalObservation,
      k4_scalar_true_atlas_terminal_lists.timePolynomial,
      k4_scalar_true_atlas_terminal_lists.spatialPolynomial,
      k4_scalar_true_atlas_terminal_lists.hiddenPolynomial,
      x, y, k4_scalar_linear_critical_extremizers.Split.x,
      k4_scalar_linear_critical_extremizers.Split.y]
  obtain ⟨m, hm, Q, hQ, rule, hrule⟩ := polynomial_mixed_mesh_lookup_format P hP widths F
    {c | i ∈ table c}
  have hcount : (m : ℝ) ≤ 6 * (F.card : ℝ) + 1 := by
    have hm' : (m : ℝ) ≤ (2 * 3 * F.card : ℕ) := hm
    push_cast at hm'
    linarith
  apply k4_scalar_true_atlas_terminal_lists.Format.of_bool_family
    (show 1 ≤ 6 * (F.card : ℝ) + 1 by
      have hc : 0 ≤ (F.card : ℝ) := Nat.cast_nonneg _
      linarith) hcount Q hQ rule
  intro w
  have h := hrule w
  rw [htag] at h
  change i ∈ table (observationMeshCode ρ F
    (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5))) ↔ _
  have hcode : finiteObservedCode F
      (fun w => observationMeshTag ρ
        (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5))) w =
      observationMeshCode ρ F
        (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5)) := by
    rfl
  rw [hcode] at h
  exact h

end

end Submission.Obl.k4_scalar_candidate_original_return
