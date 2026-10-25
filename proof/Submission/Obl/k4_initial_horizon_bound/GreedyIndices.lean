import Submission.Obl.k4_initial_horizon_bound.Greedy

open Set

namespace Submission.Obl.k4_initial_horizon_bound

variable {α β : Type*}

def priorityPiece (S : β → Set α) (U : Set α) (ps : List β) (k : Fin ps.length) : Set α :=
  {x | x ∈ U ∧ x ∈ S (ps.get k) ∧ ∀ i : Fin ps.length, i < k → x ∉ S (ps.get i)}

theorem priorityPiece_zero (S : β → Set α) (U : Set α) (p : β) (ps : List β) :
    priorityPiece S U (p :: ps) 0 = U ∩ S p := by
  ext x
  simp [priorityPiece]

theorem priorityPiece_succ (S : β → Set α) (U : Set α) (p : β) (ps : List β)
    (k : Fin ps.length) :
    priorityPiece S U (p :: ps) k.succ = priorityPiece S (U \ S p) ps k := by
  ext x
  constructor
  · rintro ⟨hxU, hxS, hprev⟩
    refine ⟨⟨hxU, ?_⟩, hxS, ?_⟩
    · exact hprev 0 (by change 0 < k.val + 1; omega)
    · intro i hi
      exact hprev i.succ (Fin.succ_lt_succ_iff.mpr hi)
  · rintro ⟨⟨hxU, hxnot⟩, hxS, hprev⟩
    refine ⟨hxU, hxS, ?_⟩
    intro i
    exact Fin.cases (fun _ => hxnot)
      (fun j hj => hprev j (Fin.succ_lt_succ_iff.mp hj)) i

theorem priorityPiece_mem_greedyPieces (S : β → Set α) (U : Set α) (ps : List β)
    (k : Fin ps.length) : (ps.get k, priorityPiece S U ps k) ∈ greedyPieces S U ps := by
  induction ps generalizing U with
  | nil => exact Fin.elim0 k
  | cons p ps ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [List.get_cons_zero, priorityPiece_zero, greedyPieces, List.mem_cons, true_or]
    · simp only [List.get_cons_succ, priorityPiece_succ, greedyPieces, List.mem_cons]
      exact Or.inr (ih _ j)

theorem greedyResidual_indices (S : β → Set α) (U : Set α) (ps : List β) :
    greedyResidual S U ps = {x | x ∈ U ∧ ∀ i : Fin ps.length, x ∉ S (ps.get i)} := by
  rw [greedyResidual_eq]
  ext x
  exact and_congr_right (fun _ => List.forall_mem_iff_get)

end Submission.Obl.k4_initial_horizon_bound
