import Submission.Obl.k4_scalar_candidate_original_return.MeshPolicy

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open Submission.Lib.K4MeshListRecovery

noncomputable section

/-- A genuinely finite observer table, empty on overflow. -/
def restrictTable {τ β : Type*} (F : Finset τ) (table : τ → Finset β) : Option F → Finset β
  | none => ∅
  | some c => table c

lemma restrictTable_card {τ β : Type*} (F : Finset τ) (table : τ → Finset β) {D : ℕ}
    (hD : ∀ c, (table c).card ≤ D) (c : Option F) : (restrictTable F table c).card ≤ D := by
  cases c with
  | none => exact Nat.zero_le _
  | some c => exact hD _

lemma restrictTable_at_hit {X τ β : Type*} (F : Finset τ) (tag : X → τ)
    (table : τ → Finset β) (x : X) (hx : tag x ∈ F) :
    restrictTable F table (finiteObservedCode F tag x) = table (tag x) := by
  rw [(finiteObservedCode_eq_some F tag x ⟨tag x, hx⟩).mpr rfl]
  rfl

/-- Restricting a lookup to finite records loses no selected mass if the
selected law is supported on those records. -/
theorem restrictTable_success {X τ β : Type*} [MeasurableSpace X]
    (μ : Measure X) (C : Set X) (F : Finset τ) (tag : X → τ) (table : τ → Finset β)
    (i : β) (hsupport : μ {x | x ∈ C ∧ tag x ∉ F} = 0) :
    μ {x | x ∈ C ∧ i ∈ table (tag x)} =
      μ {x | x ∈ C ∧ i ∈ restrictTable F table (finiteObservedCode F tag x)} := by
  have hae : ∀ᵐ x ∂μ, x ∈ C → tag x ∈ F := by
    apply ae_iff.mpr
    have heq : {x | ¬(x ∈ C → tag x ∈ F)} = {x | x ∈ C ∧ tag x ∉ F} := by
      ext x
      simp
    rw [heq]
    exact hsupport
  apply measure_congr
  filter_upwards [hae] with x hx
  by_cases hC : x ∈ C
  · have heq := restrictTable_at_hit F tag table x (hx hC)
    simp only [mem_ofPred_eq, hC, true_and, heq]
  · simp only [mem_ofPred_eq, hC, false_and]

/-- The truncated scalar rule is formatted regardless of its table contents. -/
lemma finite_scalar_table_format {n : ℕ} (ρ δ : ℝ) (F : Finset (Fin 3 → ℤ))
    (table : (Fin 3 → ℤ) → Finset (Fin n)) (i : Fin n) (z : ℕ) :
    Format 6 (6 * (F.card : ℝ) + 1) 3
      {w | i ∈ restrictTable F table (observationMeshCode ρ F
        (originalObservation δ ((z, fun e : Fin 5 => w e.castSucc), w 5)))} :=
  meshLists_format ρ δ F (restrictTable F table) i z

end

end Submission.Obl.k4_scalar_candidate_original_return
