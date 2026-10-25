-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TripleSwap.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleRefinement
import Submission.WZ.Obl.wz_separated_projection_dichotomy.CoverCounting
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Parameters

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set

def swapTriple (p : Triple) : Triple := (p.1, p.2.2, p.2.1)

theorem swapTriple_involutive : Function.Involutive swapTriple := fun _ => rfl

theorem swapTriple_injective : Function.Injective swapTriple := swapTriple_involutive.injective

theorem card_swap_filter (H : Finset Triple) (P : Triple → Prop) [DecidablePred P] :
    ((H.image swapTriple).filter P).card = (H.filter (fun p => P (swapTriple p))).card := by
  classical
  rw [Finset.filter_image]
  exact Finset.card_image_of_injective _ swapTriple_injective

theorem swapTriple_contained {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) : H.image swapTriple ⊆ F ×ˢ (U ×ˢ G) := by
  classical
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  have h := Finset.mem_product.mp (hH hq)
  have h' := Finset.mem_product.mp h.2
  exact Finset.mem_product.mpr ⟨h.1, Finset.mem_product.mpr ⟨h'.2, h'.1⟩⟩

theorem TripleUniform.swap {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) : TripleUniform d F U G (H.image swapTriple) := by
  classical
  intro i p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  rw [card_swap_filter]
  fin_cases i
  · simpa [tripleFiberCapacity, tripleProjection, swapTriple, mul_comm] using h 0 q hq
  · simpa [tripleFiberCapacity, tripleProjection, swapTriple] using h 2 q hq
  · simpa [tripleFiberCapacity, tripleProjection, swapTriple] using h 1 q hq
  · simpa [tripleFiberCapacity, tripleProjection, swapTriple] using h 4 q hq
  · simpa [tripleFiberCapacity, tripleProjection, swapTriple] using h 3 q hq
  · simpa [tripleFiberCapacity, tripleProjection, swapTriple, Prod.ext_iff, and_comm] using h 5 q hq

theorem ProjectionGain.of_neg_dot {δ η ε : ℝ} {Q R : Set Triple}
    (h : ProjectionGain δ η ε Q) (hdot : ∀ t ∈ DotSet Q, -t ∈ DotSet R) :
    ProjectionGain δ η ε R := by
  obtain ⟨ρ, a, L, hρ, hL, hcov⟩ := h
  refine ⟨ρ, -a - L, L, hρ, hL, hcov.neg_image.mono_set ?_⟩
  rintro t ⟨s, hs, rfl⟩
  exact ⟨⟨by linarith [hs.1.1, hs.1.2], by linarith [hs.1.1, hs.1.2]⟩, hdot s hs.2⟩

theorem ProjectionGain.of_swap {δ η ε : ℝ} {H : Finset Triple}
    (h : ProjectionGain δ η ε (↑(H.image swapTriple) : Set Triple)) :
    ProjectionGain δ η ε (↑H : Set Triple) := by
  classical
  apply h.of_neg_dot
  rintro t ⟨p, hp, rfl⟩
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  refine ⟨q, hq, ?_⟩
  simp [swapTriple, ← inner_neg_right]

end WangZahlLot.Obl.wz_separated_projection_dichotomy
