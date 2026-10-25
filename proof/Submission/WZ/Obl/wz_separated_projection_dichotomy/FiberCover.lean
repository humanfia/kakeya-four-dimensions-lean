-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.FiberCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.ProjectionMoment

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable def graphFiber (F : Finset Plane) (H : Finset (Plane × Plane)) (θ : Plane) : Finset Plane :=
  F.filter (fun x => (θ, x) ∈ H)

theorem graphFiber_subset (F : Finset Plane) (H : Finset (Plane × Plane)) (θ : Plane) :
    graphFiber F H θ ⊆ F := Finset.filter_subset _ _

theorem sum_graphFiber_card {F Λ : Finset Plane} {H : Finset (Plane × Plane)}
    (hH : H ⊆ Λ ×ˢ F) : ∑ θ ∈ Λ, (graphFiber F H θ).card = H.card := by
  classical
  have hfib (θ : Plane) : H.filter (fun p => p.1 = θ) = {θ} ×ˢ graphFiber F H θ := by
    ext ⟨u, x⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, graphFiber]
    constructor
    · rintro ⟨hp, rfl⟩
      exact ⟨rfl, (Finset.mem_product.mp (hH hp)).2, hp⟩
    · rintro ⟨rfl, hx, hp⟩
      exact ⟨hp, rfl⟩
  have h := Finset.card_eq_sum_card_fiberwise (s := H) (t := Λ) (f := Prod.fst)
    (fun p hp => (Finset.mem_product.mp (hH hp)).1)
  simpa only [hfib, Finset.card_product, Finset.card_singleton, one_mul] using h.symm

theorem closePairs_card_le_of_injective {X X' Y : Type*} [Fintype X] [Fintype X']
    [PseudoMetricSpace Y] (j : X → X') (hj : Function.Injective j) (f : X' → Y) (r : ℝ) :
    (closePairs (fun x => f (j x)) r).card ≤ (closePairs f r).card := by
  classical
  let J : X × X → X' × X' := fun p => (j p.1, j p.2)
  have hJ : Function.Injective J := by
    intro p q hpq
    exact Prod.ext (hj (congrArg Prod.fst hpq)) (hj (congrArg Prod.snd hpq))
  have hsub : (closePairs (fun x => f (j x)) r).image J ⊆ closePairs f r := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    have hdist : dist (f (j q.1)) (f (j q.2)) ≤ r := by
      simpa only [closePairs, Finset.mem_filter, Finset.mem_univ, true_and] using hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ hJ] at hc

theorem card_sq_le_cover_mul_projectionEnergy {F T : Finset Plane} (hTF : T ⊆ F)
    (θ : Plane) (δ : ℝ) {m : ℕ} {cc : Fin m → ℝ}
    (hc : Covers δ ((fun x => inner ℝ θ x) '' (↑T : Set Plane)) cc) :
    (T.card : ℝ) ^ 2 ≤ (m : ℝ) * projectionEnergy F θ δ := by
  let j : T → F := fun x => ⟨x.val, hTF x.property⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : F => (z : Plane)) hxy
  have hrange : Covers δ (Set.range (fun x : T => inner ℝ θ (x : Plane))) cc := by
    rintro z ⟨x, rfl⟩
    exact hc ⟨x, x.property, rfl⟩
  have h₁ := card_sq_le_cover_mul_closePairs (fun x : T => inner ℝ θ (x : Plane)) δ hrange
  have h₂ : ((closePairs (fun x : T => inner ℝ θ (x : Plane)) (2 * δ)).card : ℝ) ≤
      ((closePairs (fun x : F => inner ℝ θ (x : Plane)) (2 * δ)).card : ℝ) := by
    exact_mod_cast closePairs_card_le_of_injective j hj (fun x : F => inner ℝ θ (x : Plane)) (2 * δ)
  rw [projectionEnergy_eq_closePairs]
  have h₁' : (T.card : ℝ) ^ 2 ≤
      (m : ℝ) * ((closePairs (fun x : T => inner ℝ θ (x : Plane)) (2 * δ)).card : ℝ) := by
    simpa only [Fintype.card_coe] using h₁
  exact h₁'.trans (mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg m))

end WangZahlLot.Obl.wz_separated_projection_dichotomy
