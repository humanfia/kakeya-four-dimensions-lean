-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GraphRelation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.CartesianFrostman

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

attribute [local instance] Classical.propDecidable

/-- A finite graph in a product is exactly the relation on its ambient
coordinate subtypes. -/
theorem rectangle_relation_image (A B : Finset ℝ) (G : Finset (ℝ × ℝ))
    (hG : G ⊆ A ×ˢ B) :
    (Finset.univ.filter (fun p : A × B => ((p.1 : ℝ), (p.2 : ℝ)) ∈ G)).image
        (fun p => ((p.1 : ℝ), (p.2 : ℝ))) = G := by
  ext p
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hp
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp (hG hp)
    exact ⟨(⟨p.1, ha⟩, ⟨p.2, hb⟩), hp, rfl⟩

theorem rectangle_relation_card (A B : Finset ℝ) (G : Finset (ℝ × ℝ))
    (hG : G ⊆ A ×ˢ B) :
    (Finset.univ.filter (fun p : A × B => ((p.1 : ℝ), (p.2 : ℝ)) ∈ G)).card = G.card := by
  have hinj : Function.Injective (fun p : A × B => ((p.1 : ℝ), (p.2 : ℝ))) := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have hh := congrArg Finset.card (rectangle_relation_image A B G hG)
  rwa [Finset.card_image_of_injective _ hinj] at hh

theorem rectangle_relation_projection (A B : Finset ℝ) (G : Finset (ℝ × ℝ))
    (hG : G ⊆ A ×ˢ B) (t : ℝ) :
    (fun p : A × B => (p.1 : ℝ) + t * (p.2 : ℝ)) ''
        (↑(Finset.univ.filter (fun p : A × B => ((p.1 : ℝ), (p.2 : ℝ)) ∈ G)) : Set (A × B)) =
      (fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑G : Set (ℝ × ℝ)) := by
  conv_rhs => rw [← rectangle_relation_image A B G hG, Finset.coe_image, Set.image_image]

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
