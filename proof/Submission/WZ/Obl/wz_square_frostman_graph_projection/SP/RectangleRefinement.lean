-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RectangleRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.RectangleFrostman
import Submission.WZ.Obl.wz_separated_projection_dichotomy.Refinement

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Prune the two coordinate fibers simultaneously, using the actual occupied
coordinate sets to measure the cost. -/
theorem coordinate_min_degree_core (G : Finset (ℝ × ℝ)) {m n : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) :
    ∃ H ⊆ G, (G.card : ℝ) - m * (G.image Prod.fst).card -
        n * (G.image Prod.snd).card ≤ (H.card : ℝ) ∧
      (∀ a ∈ H.image Prod.fst, m ≤ ((H.filter (fun p => p.1 = a)).card : ℝ)) ∧
      (∀ b ∈ H.image Prod.snd, n ≤ ((H.filter (fun p => p.2 = b)).card : ℝ)) := by
  classical
  let f : Bool → (ℝ × ℝ) → ℝ := fun b => if b then Prod.snd else Prod.fst
  let t : Bool → ℝ := fun b => if b then n else m
  have ht : ∀ b, 0 ≤ t b := by intro b; cases b <;> assumption
  obtain ⟨H, hHG, hcard, hdegree⟩ :=
    WangZahlLot.Obl.wz_separated_projection_dichotomy.exists_dense_fiber_refinement G f t ht
  refine ⟨H, hHG, ?_, ?_, ?_⟩
  · simp only [Fintype.sum_bool, f, t, Bool.false_eq_true, ↓reduceIte] at hcard
    linarith
  · intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    exact hdegree false p hp
  · intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact hdegree true p hp

/-- A dense graph with planar dimension greater than one has a large
subgraph whose two coordinate sets are positively nonconcentrated. -/
theorem dense_rectangle_frostman_refinement (G : Finset (ℝ × ℝ))
    {δ C β d e : ℝ} (hδ : 0 < δ) (hC : 1 ≤ C) (hβ : 1 ≤ β)
    (hd : 0 < d) (hd1 : d ≤ 1) (he : 0 < e) (he1 : e ≤ 1 / 4)
    (hGne : G.Nonempty) (hG : RectangleFrostman δ C β G)
    (hbound : ∀ p ∈ G, |p.1| ≤ 4 ∧ |p.2| ≤ 4)
    (hdense : d * ((G.image Prod.fst).card : ℝ) * (G.image Prod.snd).card ≤ (G.card : ℝ)) :
    ∃ H ⊆ G, H.Nonempty ∧ (1 - 2 * e) * (G.card : ℝ) ≤ (H.card : ℝ) ∧
      RealFiniteFrostman δ (10 * C / (e * d)) (β - 1) (H.image Prod.fst) ∧
      RealFiniteFrostman δ (10 * C / (e * d)) (β - 1) (H.image Prod.snd) ∧
      (d / 2) * ((G.image Prod.fst).card : ℝ) ≤ (H.image Prod.fst).card ∧
      (d / 2) * ((G.image Prod.snd).card : ℝ) ≤ (H.image Prod.snd).card := by
  classical
  let A := G.image Prod.fst
  let B := G.image Prod.snd
  have hAp : (0 : ℝ) < A.card := by exact_mod_cast (hGne.image Prod.fst).card_pos
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast (hGne.image Prod.snd).card_pos
  have hGp : (0 : ℝ) < G.card := by exact_mod_cast hGne.card_pos
  obtain ⟨H, hHG, hsize, hrows, hcols⟩ := coordinate_min_degree_core G
    (m := e * d * (B.card : ℝ)) (n := e * d * (A.card : ℝ)) (by positivity) (by positivity)
  have hkeep : (1 - 2 * e) * (G.card : ℝ) ≤ (H.card : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hdense (show 0 ≤ 2 * e by positivity)
    dsimp [A, B] at hsize ⊢
    nlinarith [hh]
  have hhalf : (1 / 2 : ℝ) * (G.card : ℝ) ≤ (H.card : ℝ) := by nlinarith
  have hHp : (0 : ℝ) < H.card := by nlinarith
  have hHne : H.Nonempty := Finset.card_pos.mp (by exact_mod_cast hHp)
  have hAmono : ((H.image Prod.fst).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image hHG)
  have hBmono : ((H.image Prod.snd).card : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.image_subset_image hHG)
  have hHF : RectangleFrostman δ (2 * C) β H := by
    convert hG.subset hδ (show 0 ≤ C by linarith) (by norm_num : (0 : ℝ) < 1 / 2) hHG hhalf using 1 <;> ring
  have hed : 0 < e * d := mul_pos he hd
  have hed1 : e * d ≤ 1 := by nlinarith
  have hrow' : ∀ a ∈ H.image Prod.fst,
      (e * d) * ((H.image Prod.snd).card : ℝ) ≤ ((H.filter (fun p => p.1 = a)).card : ℝ) :=
    fun a ha => (mul_le_mul_of_nonneg_left hBmono hed.le).trans (hrows a ha)
  have hcol' : ∀ b ∈ H.image Prod.snd,
      (e * d) * ((H.image Prod.fst).card : ℝ) ≤ ((H.filter (fun p => p.2 = b)).card : ℝ) :=
    fun b hb => (mul_le_mul_of_nonneg_left hAmono hed.le).trans (hcols b hb)
  have hAF := hHF.first_marginal hδ (by linarith) hβ hed hed1 hHne
    (fun p hp => (hbound p (hHG hp)).2) hrow'
  have hBF := hHF.second_marginal hδ (by linarith) hβ hed hed1 hHne
    (fun p hp => (hbound p (hHG hp)).1) hcol'
  have hHprod : (H.card : ℝ) ≤ ((H.image Prod.fst).card : ℝ) * (H.image Prod.snd).card := by
    have hh : H ⊆ (H.image Prod.fst) ×ˢ (H.image Prod.snd) := fun p hp =>
      Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    have hh' := Finset.card_le_card hh
    rw [Finset.card_product] at hh'
    exact_mod_cast hh'
  refine ⟨H, hHG, hHne, hkeep, ?_, ?_, ?_, ?_⟩
  · convert hAF using 1 <;> ring
  · convert hBF using 1 <;> ring
  · have hh := mul_le_mul_of_nonneg_left hBmono (Nat.cast_nonneg (H.image Prod.fst).card)
    apply (mul_le_mul_iff_left₀ hBp).mp
    nlinarith [hHprod, hh]
  · have hh := mul_le_mul_of_nonneg_right hAmono (Nat.cast_nonneg (H.image Prod.snd).card)
    apply (mul_le_mul_iff_right₀ hAp).mp
    nlinarith [hHprod, hh]

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
