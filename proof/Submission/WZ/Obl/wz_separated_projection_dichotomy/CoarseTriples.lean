-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.CoarseTriples.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.UniformFibers
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Basic

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open scoped BigOperators

/-- Deleting a small set in each coordinate has the elementary three-term
cost, with no assumptions on the original hypergraph. -/
theorem triple_delete_card {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (B₁ B₂ B₃ : Finset Plane) :
    H.card ≤ (H.filter (fun p => p.1 ∉ B₁ ∧ p.2.1 ∉ B₂ ∧ p.2.2 ∉ B₃)).card +
      B₁.card * G.card * U.card + F.card * B₂.card * U.card + F.card * G.card * B₃.card := by
  classical
  let J := H.filter (fun p => p.1 ∉ B₁ ∧ p.2.1 ∉ B₂ ∧ p.2.2 ∉ B₃)
  have hs : H ⊆ ((J ∪ (B₁ ×ˢ (G ×ˢ U))) ∪ (F ×ˢ (B₂ ×ˢ U))) ∪ (F ×ˢ (G ×ˢ B₃)) := by
    intro p hp
    have hpF := Finset.mem_product.mp (hH hp)
    have hpG := Finset.mem_product.mp hpF.2
    by_cases h₁ : p.1 ∈ B₁
    · simp only [Finset.mem_union, Finset.mem_product]
      exact Or.inl (Or.inl (Or.inr ⟨h₁, hpG⟩))
    by_cases h₂ : p.2.1 ∈ B₂
    · simp only [Finset.mem_union, Finset.mem_product]
      exact Or.inl (Or.inr ⟨hpF.1, h₂, hpG.2⟩)
    by_cases h₃ : p.2.2 ∈ B₃
    · simp only [Finset.mem_union, Finset.mem_product]
      exact Or.inr ⟨hpF.1, hpG.1, h₃⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hp, h₁, h₂, h₃⟩)))
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hc₂ := Finset.card_union_le (J ∪ (B₁ ×ˢ (G ×ˢ U))) (F ×ˢ (B₂ ×ˢ U))
  have hc₁ := Finset.card_union_le J (B₁ ×ˢ (G ×ˢ U))
  simp only [Finset.card_product] at hc hc₂ hc₁
  dsimp [J] at *
  simp only [mul_assoc] at *
  omega

def coarseTriple (f g h : Plane → Plane) (p : Triple) : Triple :=
  (f p.1, g p.2.1, h p.2.2)

theorem coarseTriple_contained {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (f g h : Plane → Plane) :
    H.image (coarseTriple f g h) ⊆ F.image f ×ˢ (G.image g ×ˢ U.image h) := by
  classical
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hF, hGU⟩ := Finset.mem_product.mp (hH hq)
  obtain ⟨hG, hU⟩ := Finset.mem_product.mp hGU
  exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q.1, hF, rfl⟩,
    Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨q.2.1, hG, rfl⟩,
      Finset.mem_image.mpr ⟨q.2.2, hU, rfl⟩⟩⟩

/-- Coordinate fiber bounds multiply, giving a density bound for the coarse
hypergraph without requiring injective coordinate maps. -/
theorem coarse_triple_card_bound {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) (f g h : Plane → Plane) {M₁ M₂ M₃ : ℝ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (h₁ : ∀ y ∈ F.image f, ((F.filter (fun x => f x = y)).card : ℝ) ≤ M₁)
    (h₂ : ∀ y ∈ G.image g, ((G.filter (fun x => g x = y)).card : ℝ) ≤ M₂)
    (h₃ : ∀ y ∈ U.image h, ((U.filter (fun x => h x = y)).card : ℝ) ≤ M₃) :
    (H.card : ℝ) ≤ M₁ * M₂ * M₃ * ((H.image (coarseTriple f g h)).card : ℝ) := by
  classical
  apply card_le_upper_fiber_mul_image
  intro q hq
  have hq' := Finset.mem_product.mp (coarseTriple_contained hH f g h hq)
  have hq'' := Finset.mem_product.mp hq'.2
  have hs : H.filter (fun p => coarseTriple f g h p = q) ⊆
      (F.filter (fun x => f x = q.1)) ×ˢ
        ((G.filter (fun x => g x = q.2.1)) ×ˢ (U.filter (fun x => h x = q.2.2))) := by
    intro p hp
    have hpH := (Finset.mem_filter.mp hp).1
    have he := (Finset.mem_filter.mp hp).2
    have hpF := Finset.mem_product.mp (hH hpH)
    have hpG := Finset.mem_product.mp hpF.2
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpF.1, congrArg Prod.fst he⟩,
      Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hpG.1, congrArg (fun p : Triple => p.2.1) he⟩,
        Finset.mem_filter.mpr ⟨hpG.2, congrArg (fun p : Triple => p.2.2) he⟩⟩⟩
  have hc : ((H.filter (fun p => coarseTriple f g h p = q)).card : ℝ) ≤
      ((F.filter (fun x => f x = q.1)).card : ℝ) *
        (((G.filter (fun x => g x = q.2.1)).card : ℝ) *
          ((U.filter (fun x => h x = q.2.2)).card : ℝ)) := by
    exact_mod_cast (Finset.card_le_card hs).trans_eq (by simp only [Finset.card_product])
  calc _ ≤ _ := hc
    _ ≤ M₁ * (M₂ * M₃) := by gcongr; exact h₁ _ hq'.1; exact h₂ _ hq''.1; exact h₃ _ hq''.2
    _ = _ := by ring

end WangZahlLot.Obl.wz_separated_projection_dichotomy
