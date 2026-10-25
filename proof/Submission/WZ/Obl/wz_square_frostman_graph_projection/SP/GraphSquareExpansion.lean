-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.GraphSquareExpansion.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RectangleRefinement
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.GraphRelation
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.UniformWeakCoordinates

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
/-- A nearly full graph in two small separated coordinate sets expands in
some positively nonconcentrated direction, assuming only a square-count
Frostman exponent greater than one for the graph itself. The dense subset
whose projection expands may depend on the direction. -/
theorem graph_square_expansion (ε b β : ℝ) (hε : 0 < ε) (hb : 0 < b) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ α γ τ C : ℝ, 0 < δ → δ ≤ δ₀ → 0 ≤ α → α ≤ 1 - ε →
        1 + b ≤ γ → β ≤ τ → 1 ≤ C → C ≤ δ ^ (-η) →
        ∀ (G : Finset (ℝ × ℝ)) (S : Finset ℝ), G.Nonempty → S.Nonempty →
          (∀ p ∈ G, |p.1| ≤ 4 ∧ |p.2| ≤ 4) →
          RectangleFrostman δ C γ G → RealFiniteFrostman δ C τ S →
          (∀ t ∈ S, t ∈ Set.Icc (0 : ℝ) 1) →
          (∀ a ∈ G.image Prod.fst, ∀ a' ∈ G.image Prod.fst, a ≠ a' → δ ≤ dist a a') →
          (∀ a ∈ G.image Prod.snd, ∀ a' ∈ G.image Prod.snd, a ≠ a' → δ ≤ dist a a') →
          ((G.image Prod.fst).card : ℝ) ≤ δ ^ (-α - η) →
          ((G.image Prod.snd).card : ℝ) ≤ δ ^ (-α - η) →
          δ ^ (η - 2 * α) ≤ (G.card : ℝ) →
          ∃ t ∈ S, ∀ H : Finset (ℝ × ℝ), H ⊆ G →
            δ ^ η * (G.card : ℝ) ≤ (H.card : ℝ) →
            CoverLower δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑H : Set (ℝ × ℝ)))
              (δ ^ (-α - η)) := by
  classical
  obtain ⟨θ, rP, hθ, hrP, hrP1, hproject⟩ := uniform_weak_coordinate_expansion ε b β hε hb hβ
  let η := θ / 100
  have hη : 0 < η := by dsimp [η]; positivity
  have hηθ : 100 * η ≤ θ := by dsimp [η]; linarith
  obtain ⟨rC, hrC, hrC1, hconstant⟩ := exists_power_bound 80 hη
  refine ⟨η, min rP rC, hη, lt_min hrP hrC, (min_le_left _ _).trans hrP1, ?_⟩
  intro δ α γ τ C hδ hδs hα hαmax hγ hτ hC hCb G S hGne hSne hbound hGF hSF hSunit hAsep hBsep hAc hBc hGc
  have hδP : δ ≤ rP := hδs.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδP.trans hrP1
  have h80 : 80 ≤ δ ^ (-η) := hconstant δ hδ (hδs.trans (min_le_right _ _))
  have hsmall : δ ^ η ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right h80 (Real.rpow_nonneg hδ.le η)
    rw [← Real.rpow_add hδ, neg_add_cancel, Real.rpow_zero] at hh
    nlinarith [Real.rpow_pos_of_pos hδ η]
  let A := G.image Prod.fst
  let B := G.image Prod.snd
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast (hGne.image Prod.fst).card_pos
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast (hGne.image Prod.snd).card_pos
  have hGp : (0 : ℝ) < G.card := by exact_mod_cast hGne.card_pos
  have hGprod : (G.card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := by
    have hh : G ⊆ A ×ˢ B := fun p hp => Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    have hc := Finset.card_le_card hh
    rw [Finset.card_product] at hc
    exact_mod_cast hc
  have lower {u v : ℝ} (hu : 0 ≤ u) (hprod : (G.card : ℝ) ≤ u * v)
      (hv : v ≤ δ ^ (-α - η)) : δ ^ (2 * η - α) ≤ u := by
    have hh := hGc.trans (hprod.trans (mul_le_mul_of_nonneg_left hv hu))
    calc
      δ ^ (2 * η - α) = δ ^ (η - 2 * α) * δ ^ (α + η) := by
        rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ (u * δ ^ (-α - η)) * δ ^ (α + η) :=
        mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hδ.le _)
      _ = u := by
        rw [mul_assoc, ← Real.rpow_add hδ, show -α - η + (α + η) = 0 by ring,
          Real.rpow_zero, mul_one]
  have hAlow : δ ^ (2 * η - α) ≤ (A.card : ℝ) := lower hAp.le hGprod hBc
  have hBlow : δ ^ (2 * η - α) ≤ (B.card : ℝ) := lower hBp.le (by nlinarith [hGprod]) hAc
  let d := δ ^ (3 * η)
  let e := δ ^ (2 * η) / 4
  have hd : 0 < d := Real.rpow_pos_of_pos hδ _
  have hd1 : d ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by positivity)
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 / 4 := by
    have hh := Real.rpow_le_one hδ.le hδ1 (show 0 ≤ 2 * η by positivity)
    dsimp [e]; linarith
  have hdense : d * (A.card : ℝ) * (B.card : ℝ) ≤ (G.card : ℝ) := by
    calc
      _ ≤ d * δ ^ (-α - η) * δ ^ (-α - η) := by gcongr
      _ = δ ^ (η - 2 * α) := by dsimp [d]; rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; congr 1; ring
      _ ≤ _ := hGc
  obtain ⟨Q, hQG, hQne, hQsize, hQAF, hQBF, hQAlo, hQBlo⟩ :=
    dense_rectangle_frostman_refinement G hδ hC (by linarith) hd hd1 he he1 hGne hGF hbound hdense
  let A' := Q.image Prod.fst
  let B' := Q.image Prod.snd
  let D := 10 * C / (e * d)
  have hed : 0 < e * d := mul_pos he hd
  have hed1 : e * d ≤ 1 := by nlinarith
  have hCD : C ≤ D := by
    dsimp [D]
    apply (le_div_iff₀ hed).mpr
    nlinarith [mul_le_mul_of_nonneg_left hed1 (show 0 ≤ C by linarith)]
  have hD : 1 ≤ D := hC.trans hCD
  have hDb : D ≤ δ ^ (-7 * η) := by
    have heq : D = 40 * C / δ ^ (5 * η) := by
      have hh : e * d = δ ^ (5 * η) / 4 := by
        dsimp [e, d]
        rw [div_mul_eq_mul_div, ← Real.rpow_add hδ]
        congr 1
        congr 1
        ring
      dsimp [D]
      rw [hh]
      field_simp
      ring
    rw [heq]
    calc
      40 * C / δ ^ (5 * η) ≤ δ ^ (-η) * δ ^ (-η) / δ ^ (5 * η) := by gcongr; linarith
      _ = δ ^ (-7 * η) := by rw [← Real.rpow_add hδ, ← Real.rpow_sub hδ]; congr 1; ring
  have hDθ : D ≤ δ ^ (-θ) := hDb.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  have hA'sub : A' ⊆ A := Finset.image_subset_image hQG
  have hB'sub : B' ⊆ B := Finset.image_subset_image hQG
  have hA'c : (A'.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hA'sub
  have hB'c : (B'.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast Finset.card_le_card hB'sub
  have hlower {u v : ℝ} (hu : δ ^ (2 * η - α) ≤ u)
      (hv : (d / 2) * u ≤ v) : δ ^ (6 * η - α) ≤ v := by
    calc
      _ = δ ^ η * δ ^ (5 * η - α) := by rw [← Real.rpow_add hδ]; congr 1; ring
      _ ≤ (1 / 2) * δ ^ (5 * η - α) := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = (d / 2) * δ ^ (2 * η - α) := by
        rw [show 5 * η - α = 3 * η + (2 * η - α) by ring, Real.rpow_add hδ]
        dsimp [d]
        ring
      _ ≤ (d / 2) * u := mul_le_mul_of_nonneg_left hu (by positivity)
      _ ≤ v := hv
  have hA'lo : δ ^ (6 * η - α) ≤ (A'.card : ℝ) := hlower hAlow hQAlo
  have hB'lo : δ ^ (6 * η - α) ≤ (B'.card : ℝ) := hlower hBlow hQBlo
  obtain ⟨t, ht, htexpand⟩ := hproject δ (γ - 1) τ α D hδ hδP (by linarith) hτ hα hαmax hD hDθ
    A' B' S (hQne.image Prod.fst) (hQne.image Prod.snd) hSne hSunit hQAF hQBF (hSF.weaken hδ hCD)
    (fun a ha a' ha' hne => hAsep a (hA'sub ha) a' (hA'sub ha') hne)
    (fun a ha a' ha' hne => hBsep a (hB'sub ha) a' (hB'sub ha') hne)
    ((hA'c.trans hAc).trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))
    ((hB'c.trans hBc).trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))
    ((Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : 6 * η - α ≤ θ - α)).trans hA'lo)
    ((Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : 6 * η - α ≤ θ - α)).trans hB'lo)
  refine ⟨t, ht, ?_⟩
  intro H hHG hHsize
  let L := H ∩ Q
  have hLQ : L ⊆ Q := Finset.inter_subset_right
  have hLH : L ⊆ H := Finset.inter_subset_left
  have hLprod : L ⊆ A' ×ˢ B' := fun p hp => Finset.mem_product.mpr
    ⟨Finset.mem_image.mpr ⟨p, hLQ hp, rfl⟩, Finset.mem_image.mpr ⟨p, hLQ hp, rfl⟩⟩
  have hLsize : (δ ^ η / 2) * (G.card : ℝ) ≤ (L.card : ℝ) := by
    have huc : ((H ∪ Q).card : ℝ) ≤ (G.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.union_subset hHG hQG)
    have hid : ((H ∪ Q).card : ℝ) + (L.card : ℝ) = (H.card : ℝ) + (Q.card : ℝ) := by
      exact_mod_cast Finset.card_union_add_card_inter H Q
    have he2 : 2 * e ≤ δ ^ η / 2 := by
      have hh := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show η ≤ 2 * η by linarith)
      dsimp [e]; linarith
    nlinarith [mul_le_mul_of_nonneg_right he2 hGp.le]
  have hLbig : δ ^ (5 * η) * (A.card : ℝ) * (B.card : ℝ) ≤ (L.card : ℝ) := by
    calc
      _ = δ ^ η * (δ ^ (4 * η) * (A.card : ℝ) * (B.card : ℝ)) := by rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hδ]; congr 3; ring
      _ ≤ (1 / 2) * (δ ^ (4 * η) * (A.card : ℝ) * (B.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = (δ ^ η / 2) * (d * (A.card : ℝ) * (B.card : ℝ)) := by
        rw [show 4 * η = η + 3 * η by ring, Real.rpow_add hδ]
        dsimp [d]
        ring
      _ ≤ (δ ^ η / 2) * (G.card : ℝ) := mul_le_mul_of_nonneg_left hdense (by positivity)
      _ ≤ _ := hLsize
  have hrel : δ ^ θ * (A'.card : ℝ) * (B'.card : ℝ) ≤
      ((Finset.univ.filter (fun p : A' × B' => ((p.1 : ℝ), (p.2 : ℝ)) ∈ L)).card : ℝ) := by
    rw [rectangle_relation_card A' B' L hLprod]
    calc
      _ ≤ δ ^ (5 * η) * (A.card : ℝ) * (B.card : ℝ) := by
        have hp : δ ^ θ ≤ δ ^ (5 * η) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        exact mul_le_mul (mul_le_mul hp hA'c (Nat.cast_nonneg _)
          (Real.rpow_nonneg hδ.le _)) hB'c (Nat.cast_nonneg _)
          (mul_nonneg (Real.rpow_nonneg hδ.le _) (Nat.cast_nonneg _))
      _ ≤ _ := hLbig
  have hlarge := htexpand (fun a b => ((a : ℝ), (b : ℝ)) ∈ L) (by convert hrel using 1 <;> congr)
  have heq : (fun q : A' × B' => (q.1 : ℝ) + t * (q.2 : ℝ)) ''
      (↑(Finset.univ.filter (fun q : A' × B' => ((q.1 : ℝ), (q.2 : ℝ)) ∈ L)) : Set (A' × B')) =
      (fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑L : Set (ℝ × ℝ)) :=
    rectangle_relation_projection A' B' L hLprod t
  have hlarge' : CoverLower δ ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑L : Set (ℝ × ℝ)))
      (δ ^ (-θ) * (A'.card : ℝ)) := by
    rw [← heq]
    convert hlarge using 1 <;> congr
  apply (hlarge'.mono_set (Set.image_mono (show (↑L : Set (ℝ × ℝ)) ⊆ ↑H from hLH))).weaken
  calc
    δ ^ (-α - η) ≤ δ ^ (6 * η - α - θ) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    _ = δ ^ (-θ) * δ ^ (6 * η - α) := by rw [← Real.rpow_add hδ]; congr 1; ring
    _ ≤ δ ^ (-θ) * (A'.card : ℝ) := mul_le_mul_of_nonneg_left hA'lo (by positivity)

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
