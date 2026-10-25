-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.SupportedRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.TripleRefinement
import Submission.WZ.Obl.wz_separated_projection_dichotomy.FactorProjections

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set

theorem triple_projection_subsets {F G U : Finset Plane} {H : Finset Triple}
    (hH : H ⊆ F ×ˢ (G ×ˢ U)) :
    H.image Prod.fst ⊆ F ∧ H.image (fun p => p.2.1) ⊆ G ∧ H.image (fun p => p.2.2) ⊆ U := by
  classical
  constructor
  · rintro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (hH hp)).1
  constructor
  · rintro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).1
  · rintro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_product.mp (Finset.mem_product.mp (hH hp)).2).2

theorem triple_subset_projections (H : Finset Triple) :
    H ⊆ H.image Prod.fst ×ˢ (H.image (fun p => p.2.1) ×ˢ H.image (fun p => p.2.2)) := by
  classical
  intro p hp
  exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
    Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩⟩

theorem TripleUniform.mono_factors {d : ℝ} {F G U F' G' U' : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (hd : 0 ≤ d) (hF : F' ⊆ F) (hG : G' ⊆ G) (hU : U' ⊆ U) :
    TripleUniform d F' G' U' H := by
  have hFc : (F'.card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_le_card hF
  have hGc : (G'.card : ℝ) ≤ G.card := by exact_mod_cast Finset.card_le_card hG
  have hUc : (U'.card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hU
  intro i p hp
  apply le_trans _ (h i p hp)
  apply mul_le_mul_of_nonneg_left _ hd
  fin_cases i <;> dsimp [tripleFiberCapacity] <;> gcongr

theorem TripleUniform.mono_density {d d' : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (h : TripleUniform d F G U H) (hdd' : d' ≤ d) : TripleUniform d' F G U H := by
  intro i p hp
  apply le_trans _ (h i p hp)
  apply mul_le_mul_of_nonneg_right hdd'
  fin_cases i <;> dsimp [tripleFiberCapacity] <;> positivity

structure SupportedRefinement (d : ℝ) (F G U : Finset Plane) (H : Finset Triple) where
  first : Finset Plane
  second : Finset Plane
  third : Finset Plane
  edges : Finset Triple
  first_subset : first ⊆ F
  second_subset : second ⊆ G
  third_subset : third ⊆ U
  edges_subset : edges ⊆ H
  nonempty : edges.Nonempty
  contained : edges ⊆ first ×ˢ (second ×ˢ third)
  first_support : ∀ a ∈ first, ∃ x b, (a, x, b) ∈ edges
  second_support : ∀ x ∈ second, ∃ a b, (a, x, b) ∈ edges
  third_support : ∀ b ∈ third, ∃ a x, (a, x, b) ∈ edges
  first_retention : (d / 2) * (F.card : ℝ) ≤ (first.card : ℝ)
  second_retention : (d / 2) * (G.card : ℝ) ≤ (second.card : ℝ)
  third_retention : (d / 2) * (U.card : ℝ) ≤ (third.card : ℝ)
  edge_retention : (H.card : ℝ) / 2 ≤ (edges.card : ℝ)
  uniform : TripleUniform (d / 12) first second third edges
  density : (d / 2) * (first.card : ℝ) * (second.card : ℝ) * (third.card : ℝ) ≤ (edges.card : ℝ)

theorem exists_supported_refinement {F G U : Finset Plane} {H : Finset Triple} {d : ℝ}
    (hd : 0 < d) (hHne : H.Nonempty) (hH : H ⊆ F ×ˢ (G ×ˢ U))
    (hdensity : d * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (H.card : ℝ)) :
    Nonempty (SupportedRefinement d F G U H) := by
  classical
  obtain ⟨S, hSH, hcard, huni⟩ := exists_triple_uniform_refinement hd.le hH hdensity
  have hSpos : (0 : ℝ) < S.card := by
    have hHpos : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hHne
    linarith
  have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hSpos)
  have hSsub := hSH.trans hH
  have hSden : (d / 2) * (F.card : ℝ) * (G.card : ℝ) * (U.card : ℝ) ≤ (S.card : ℝ) := by linarith
  obtain ⟨hFs, hGs, hUs⟩ := triple_projection_subsets hSsub
  obtain ⟨hFr, hGr, hUr⟩ := product_density_projection_cards F G U S hSsub hSne hSden
  have hfirst : ∀ a ∈ S.image Prod.fst, ∃ x b, (a, x, b) ∈ S := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨p.2.1, p.2.2, hp⟩
  have hsecond : ∀ x ∈ S.image (fun p => p.2.1), ∃ a b, (a, x, b) ∈ S := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨p.1, p.2.2, hp⟩
  have hthird : ∀ b ∈ S.image (fun p => p.2.2), ∃ a x, (a, x, b) ∈ S := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨p.1, p.2.1, hp⟩
  have huniform : TripleUniform (d / 12) (S.image Prod.fst)
      (S.image (fun p => p.2.1)) (S.image (fun p => p.2.2)) S :=
    huni.mono_factors (by positivity) hFs hGs hUs
  have hden : (d / 2) * ((S.image Prod.fst).card : ℝ) *
      ((S.image (fun p => p.2.1)).card : ℝ) * ((S.image (fun p => p.2.2)).card : ℝ) ≤ (S.card : ℝ) := by
    have hFc : ((S.image Prod.fst).card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_le_card hFs
    have hGc : ((S.image (fun p => p.2.1)).card : ℝ) ≤ G.card := by exact_mod_cast Finset.card_le_card hGs
    have hUc : ((S.image (fun p => p.2.2)).card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hUs
    apply le_trans _ hSden
    gcongr
  refine ⟨{
    first := S.image Prod.fst
    second := S.image (fun p => p.2.1)
    third := S.image (fun p => p.2.2)
    edges := S
    first_subset := ?_
    second_subset := ?_
    third_subset := ?_
    edges_subset := ?_
    nonempty := ?_
    contained := ?_
    first_support := ?_
    second_support := ?_
    third_support := ?_
    first_retention := ?_
    second_retention := ?_
    third_retention := ?_
    edge_retention := ?_
    uniform := ?_
    density := ?_
  }⟩
  · exact hFs
  · exact hGs
  · exact hUs
  · exact hSH
  · exact hSne
  · exact triple_subset_projections S
  · exact hfirst
  · exact hsecond
  · exact hthird
  · exact hFr
  · exact hGr
  · exact hUr
  · exact hcard
  · exact huniform
  · exact hden

theorem SupportedRefinement.first_nonempty {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (R : SupportedRefinement d F G U H) : R.first.Nonempty := by
  obtain ⟨p, hp⟩ := R.nonempty
  exact ⟨p.1, (Finset.mem_product.mp (R.contained hp)).1⟩

theorem SupportedRefinement.second_nonempty {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (R : SupportedRefinement d F G U H) : R.second.Nonempty := by
  obtain ⟨p, hp⟩ := R.nonempty
  exact ⟨p.2.1, (Finset.mem_product.mp (Finset.mem_product.mp (R.contained hp)).2).1⟩

theorem SupportedRefinement.third_nonempty {d : ℝ} {F G U : Finset Plane} {H : Finset Triple}
    (R : SupportedRefinement d F G U H) : R.third.Nonempty := by
  obtain ⟨p, hp⟩ := R.nonempty
  exact ⟨p.2.2, (Finset.mem_product.mp (Finset.mem_product.mp (R.contained hp)).2).2⟩

end WangZahlLot.Obl.wz_separated_projection_dichotomy
