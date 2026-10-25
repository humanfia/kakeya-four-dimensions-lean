-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale.EndpointFinset.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/Multiscale/EndpointFinset.lean (82de8bd).
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Multiscale.EndpointSelection

/-!
# Endpoint selection for finsets

`dense_endpoint_finset` restates x0603's `dense_endpoint_family` (stated for finite types) for
finite sets `I` of columns and `J` of lines: a relation of density `d` with few bad column pairs
has two non-bad endpoint columns, a common family `G ⊆ J` of at least `d² #J / 8` lines through
both, and at least `d #I / 4` columns, each avoiding both endpoints' bad sets and meeting at least
`d #G / 8` lines of `G`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale

open scoped BigOperators

attribute [local instance] Classical.propDecidable

theorem dense_endpoint_finset {α β : Type*} (I : Finset α) (J : Finset β)
    (hI : I.Nonempty) (hJ : J.Nonempty) (R : α → β → Prop) (Bad : α → α → Prop) {d : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hdensity : d * (I.card : ℝ) * J.card ≤ (((I ×ˢ J).filter (fun p => R p.1 p.2)).card : ℝ))
    (hbad : ∀ i ∈ I, ((I.filter (Bad i)).card : ℝ) ≤ d ^ 2 / 16 * I.card) :
    ∃ i₀ ∈ I, ∃ i₁ ∈ I, ∃ G : Finset β, G ⊆ J ∧ ∃ S : Finset α, S ⊆ I ∧
      ¬ Bad i₀ i₁ ∧ (∀ j ∈ G, R i₀ j ∧ R i₁ j) ∧
      d ^ 2 / 8 * (J.card : ℝ) ≤ G.card ∧ d / 4 * (I.card : ℝ) ≤ S.card ∧
      (∀ i ∈ S, ¬ Bad i₀ i ∧ ¬ Bad i₁ i ∧ d / 8 * (G.card : ℝ) ≤ ((G.filter (R i)).card : ℝ)) := by
  classical
  have : Nonempty I := ⟨⟨hI.choose, hI.choose_spec⟩⟩
  have : Nonempty J := ⟨⟨hJ.choose, hJ.choose_spec⟩⟩
  set R' : I → J → Prop := fun i j => R i.1 j.1 with hR'
  set Bad' : I → I → Prop := fun i i' => Bad i.1 i'.1 with hBad'
  have hcardI : (Fintype.card I : ℝ) = I.card := by simp
  have hcardJ : (Fintype.card J : ℝ) = J.card := by simp
  have hdens' : d * (Fintype.card I : ℝ) * Fintype.card J ≤
      ((Finset.univ.filter (fun p : I × J => R' p.1 p.2)).card : ℝ) := by
    rw [hcardI, hcardJ]
    refine hdensity.trans (le_of_eq ?_)
    norm_cast
    apply Finset.card_bij (fun (p : α × β) hp =>
      (⟨⟨p.1, (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1⟩,
        ⟨p.2, (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2⟩⟩ : I × J))
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hR']
      exact (Finset.mem_filter.mp hp).2
    · intro p hp p' hp' h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Prod.ext h.1 h.2
    · intro q hq
      refine ⟨(q.1.1, q.2.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hR'] at hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨q.1.2, q.2.2⟩, hq⟩
  have hbad' : ∀ i : I, ((Finset.univ.filter (Bad' i)).card : ℝ) ≤
      d ^ 2 / 16 * Fintype.card I := by
    intro i
    rw [hcardI]
    refine le_trans (le_of_eq ?_) (hbad i.1 i.2)
    norm_cast
    apply Finset.card_bij (fun (i' : I) _ => i'.1)
    · intro i' hi'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hBad'] at hi'
      exact Finset.mem_filter.mpr ⟨i'.2, hi'⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro x hx
      have hx' := Finset.mem_filter.mp hx
      refine ⟨⟨x, hx'.1⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hBad']
      exact hx'.2
  obtain ⟨i₀, i₁, G, S, hnb, hGR, hGcard, hScard, hS⟩ :=
    dense_endpoint_family R' Bad' hd hd1 hdens' hbad'
  refine ⟨i₀.1, i₀.2, i₁.1, i₁.2, G.map ⟨Subtype.val, Subtype.val_injective⟩, ?_,
    S.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, hnb, ?_, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨j', _, rfl⟩ := Finset.mem_map.mp hj
    exact j'.2
  · intro i hi
    obtain ⟨i', _, rfl⟩ := Finset.mem_map.mp hi
    exact i'.2
  · intro j hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hj
    exact hGR j' hj'
  · rw [Finset.card_map, ← hcardJ]; exact hGcard
  · rw [Finset.card_map, ← hcardI]; exact hScard
  · intro i hi
    obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨h1, h2, h3⟩ := hS i' hi'
    refine ⟨h1, h2, ?_⟩
    rw [Finset.card_map]
    refine h3.trans (le_of_eq ?_)
    norm_cast
    apply Finset.card_bij (fun (j : J) _ => j.1)
    · intro j hj
      have hj' := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_map_of_mem _ hj'.1, hj'.2⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro x hx
      have hx' := Finset.mem_filter.mp hx
      obtain ⟨j', hj', rfl⟩ := Finset.mem_map.mp hx'.1
      exact ⟨j', Finset.mem_filter.mpr ⟨hj', hx'.2⟩, rfl⟩

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Multiscale
