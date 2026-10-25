import Mathlib

namespace Submission.Obl.k4_fixed_menu_density_pruning

open Finset

/-- An injective relabelling cannot increase the number of candidates at an old packet. -/
theorem card_filter_comp_le {n' n C : ℕ} (e : Fin n' → Fin n)
    (he : Function.Injective e) (old : Fin n → Fin C) (b : Fin C) :
    (univ.filter (fun a => old (e a) = b)).card ≤
      (univ.filter (fun a => old a = b)).card := by
  classical
  exact Finset.card_le_card_of_injOn e
    (fun a ha => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩)
    (fun _ _ _ _ h => he h)

/-- Enumerating the retained finite set preserves a sum whose discarded terms vanish. -/
theorem sum_reindex_finset {n : ℕ} {M : Type*} [AddCommMonoid M]
    (S : Finset (Fin n)) (f : Fin n → M) (hf : ∀ a ∉ S, f a = 0) :
    (∑ a : Fin S.card, f (S.orderEmbOfFin rfl a)) = ∑ a : Fin n, f a := by
  classical
  refine Fintype.sum_of_injective _ (S.orderEmbOfFin rfl).injective _ f ?_ (fun _ => rfl)
  intro a ha
  apply hf a
  simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using ha

end Submission.Obl.k4_fixed_menu_density_pruning
