-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_square_frostman_graph_projection.SP.RectangleFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o157/x0572, commit 9dec67f2c5b299a992cba3feba903e42a6e4275b.
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.Basic
import Submission.WZ.Obl.wz_square_frostman_graph_projection.SP.CartesianFrostman
import Submission.WZ.Obl.wz_nonconcentrated_dot_products.RealCover

namespace WangZahlLot.Obl.wz_square_frostman_graph_projection.SP

open WangZahlLot.Obl.wz_nonconcentrated_dot_products

open WangZahlLot.Obl.wz_nonconcentrated_dot_products
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Square counts in Cartesian coordinates. -/
def RectangleFrostman (δ C β : ℝ) (G : Finset (ℝ × ℝ)) : Prop :=
  ∀ x y r : ℝ, δ ≤ r →
    ((G.filter (fun p => dist p.1 x ≤ r ∧ dist p.2 y ≤ r)).card : ℝ) ≤
      C * r ^ β * (G.card : ℝ)

/-- Covering the bounded second coordinate by intervals loses one dimension
when a square-count bound is transferred to a vertical strip. -/
theorem RectangleFrostman.first_strip {δ C β r : ℝ} {G : Finset (ℝ × ℝ)}
    (hG : RectangleFrostman δ C β G) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hbound : ∀ p ∈ G, |p.2| ≤ 4) (hr : δ ≤ r) (hr1 : r ≤ 1) (x : ℝ) :
    ((G.filter (fun p => dist p.1 x ≤ r)).card : ℝ) ≤
      5 * C * r ^ (β - 1) * (G.card : ℝ) := by
  classical
  have hrp : 0 < r := hδ.trans_le hr
  let n := ⌊4 / r⌋₊
  have hnlow : 4 / r < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one (4 / r)
  have hnhi : (n : ℝ) ≤ 4 / r := by
    exact Nat.floor_le (by positivity)
  obtain ⟨cc, hcover⟩ := real_closedBall_mul_cover r n
  let W := G.filter (fun p => dist p.1 x ≤ r)
  let U (i : Fin (n + 1)) := G.filter (fun p => dist p.1 x ≤ r ∧ dist p.2 (cc i) ≤ r)
  have hsub : W ⊆ Finset.univ.biUnion U := by
    intro p hp
    obtain ⟨hpG, hpx⟩ := Finset.mem_filter.mp hp
    have hR : 4 ≤ ((n + 1 : ℕ) : ℝ) * r := by
      have hh := (div_lt_iff₀ hrp).mp hnlow
      push_cast
      linarith
    have hpball : p.2 ∈ Metric.closedBall 0 (((n + 1 : ℕ) : ℝ) * r) := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using (hbound p hpG).trans hR
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hpball)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hpG, hpx, hi⟩⟩
  have hc : (W.card : ℝ) ≤ ∑ i : Fin (n + 1), ((U i).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hn : ((n + 1 : ℕ) : ℝ) ≤ 5 / r := by
    have hh := (le_div_iff₀ hrp).mp hnhi
    apply (le_div_iff₀ hrp).mpr
    push_cast
    nlinarith
  calc
    (W.card : ℝ) ≤ ∑ i : Fin (n + 1), ((U i).card : ℝ) := hc
    _ ≤ ∑ _i : Fin (n + 1), C * r ^ β * (G.card : ℝ) :=
      Finset.sum_le_sum (fun i _ => hG x (cc i) r hr)
    _ = ((n + 1 : ℕ) : ℝ) * (C * r ^ β * (G.card : ℝ)) := by simp
    _ ≤ (5 / r) * (C * r ^ β * (G.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = 5 * C * r ^ (β - 1) * (G.card : ℝ) := by
      rw [Real.rpow_sub hrp, Real.rpow_one]
      ring

/-- Passing to a subset costs only its reciprocal relative cardinality. -/
theorem RectangleFrostman.subset {δ C β d : ℝ} {G H : Finset (ℝ × ℝ)}
    (hG : RectangleFrostman δ C β G) (hδ : 0 < δ) (hC : 0 ≤ C) (hd : 0 < d)
    (hHG : H ⊆ G) (hsize : d * (G.card : ℝ) ≤ (H.card : ℝ)) :
    RectangleFrostman δ (C / d) β H := by
  intro x y r hr
  have hrp : 0 < r := hδ.trans_le hr
  have hc : ((H.filter (fun p => dist p.1 x ≤ r ∧ dist p.2 y ≤ r)).card : ℝ) ≤
      ((G.filter (fun p => dist p.1 x ≤ r ∧ dist p.2 y ≤ r)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hHG)
  calc
    _ ≤ ((G.filter (fun p => dist p.1 x ≤ r ∧ dist p.2 y ≤ r)).card : ℝ) := hc
    _ ≤ C * r ^ β * (G.card : ℝ) := hG x y r hr
    _ ≤ (C / d) * r ^ β * (H.card : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ (C / d) * r ^ β)
      convert hh using 1 <;> field_simp <;> ring

/-- A coordinate projection of a graph with positive minimum degree inherits
one less dimension than the graph's square-count bound. -/
theorem RectangleFrostman.first_marginal {δ C β d : ℝ} {G : Finset (ℝ × ℝ)}
    (hG : RectangleFrostman δ C β G) (hδ : 0 < δ) (hC : 1 ≤ C) (hβ : 1 ≤ β)
    (hd : 0 < d) (hd1 : d ≤ 1) (hGne : G.Nonempty)
    (hbound : ∀ p ∈ G, |p.2| ≤ 4)
    (hdegree : ∀ a ∈ G.image Prod.fst,
      d * ((G.image Prod.snd).card : ℝ) ≤ ((G.filter (fun p => p.1 = a)).card : ℝ)) :
    RealFiniteFrostman δ (5 * C / d) (β - 1) (G.image Prod.fst) := by
  classical
  let A := G.image Prod.fst
  let B := G.image Prod.snd
  have hBp : (0 : ℝ) < B.card := by exact_mod_cast (hGne.image Prod.snd).card_pos
  have hGc : (G.card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := by
    have hh : G ⊆ A ×ˢ B := fun p hp => Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    have hh' := Finset.card_le_card hh
    rw [Finset.card_product] at hh'
    exact_mod_cast hh'
  intro x r hr
  have hrp : 0 < r := hδ.trans_le hr
  change ((A.filter (fun a => dist a x ≤ r)).card : ℝ) ≤ _
  by_cases hr1 : r ≤ 1
  · let T := A.filter (fun a => dist a x ≤ r)
    have heq : (∑ a ∈ T, ((G.filter (fun p => p.1 = a)).card : ℝ)) =
        ((G.filter (fun p => dist p.1 x ≤ r)).card : ℝ) := by
      have hh := Finset.sum_card_fiberwise_eq_card_filter G T Prod.fst
      have hf : G.filter (fun p => p.1 ∈ T) = G.filter (fun p => dist p.1 x ≤ r) := by
        apply Finset.filter_congr
        intro p hp
        have hpa : p.1 ∈ A := Finset.mem_image.mpr ⟨p, hp, rfl⟩
        simp [T, hpa]
      rw [hf] at hh
      exact_mod_cast hh
    have hcount : d * (B.card : ℝ) * (T.card : ℝ) ≤
        5 * C * r ^ (β - 1) * (A.card : ℝ) * (B.card : ℝ) := by
      calc
        _ = ∑ _a ∈ T, d * (B.card : ℝ) := by simp; ring
        _ ≤ ∑ a ∈ T, ((G.filter (fun p => p.1 = a)).card : ℝ) :=
          Finset.sum_le_sum (fun a ha => hdegree a (Finset.mem_filter.mp ha).1)
        _ = ((G.filter (fun p => dist p.1 x ≤ r)).card : ℝ) := heq
        _ ≤ 5 * C * r ^ (β - 1) * (G.card : ℝ) := hG.first_strip hδ (by linarith) hbound hr hr1 x
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left hGc
            (by positivity : 0 ≤ 5 * C * r ^ (β - 1))
          nlinarith [hh]
    have hc : d * (T.card : ℝ) ≤ 5 * C * r ^ (β - 1) * (A.card : ℝ) := by
      apply (mul_le_mul_iff_left₀ hBp).mp
      nlinarith [hcount]
    change (T.card : ℝ) ≤ _
    calc
      _ ≤ (5 * C * r ^ (β - 1) * (A.card : ℝ)) / d := (le_div_iff₀ hd).mpr (by nlinarith)
      _ = _ := by ring
  · have hrp : 1 ≤ r := (lt_of_not_ge hr1).le
    have hpow : 1 ≤ r ^ (β - 1) := Real.one_le_rpow hrp (by linarith)
    have hconst : 1 ≤ 5 * C / d := (le_div_iff₀ hd).mpr (by linarith)
    have hh : 1 ≤ (5 * C / d) * r ^ (β - 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ 5 * C / d)]
    have hcard : ((A.filter (fun a => dist a x ≤ r)).card : ℝ) ≤ (A.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le A _
    exact hcard.trans (by nlinarith [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg A.card)])

theorem RectangleFrostman.swap {δ C β : ℝ} {G : Finset (ℝ × ℝ)}
    (hG : RectangleFrostman δ C β G) : RectangleFrostman δ C β (G.image Prod.swap) := by
  intro x y r hr
  have heq : (G.image Prod.swap).filter (fun p => dist p.1 x ≤ r ∧ dist p.2 y ≤ r) =
      (G.filter (fun p => dist p.1 y ≤ r ∧ dist p.2 x ≤ r)).image Prod.swap := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨q, hq, rfl⟩, h⟩
      exact ⟨q, ⟨hq, h.2, h.1⟩, rfl⟩
    · rintro ⟨q, ⟨hq, h⟩, rfl⟩
      exact ⟨⟨q, hq, rfl⟩, h.2, h.1⟩
  rw [heq, Finset.card_image_of_injective _ Prod.swap_injective,
    Finset.card_image_of_injective _ Prod.swap_injective]
  exact hG y x r hr

theorem RectangleFrostman.second_marginal {δ C β d : ℝ} {G : Finset (ℝ × ℝ)}
    (hG : RectangleFrostman δ C β G) (hδ : 0 < δ) (hC : 1 ≤ C) (hβ : 1 ≤ β)
    (hd : 0 < d) (hd1 : d ≤ 1) (hGne : G.Nonempty)
    (hbound : ∀ p ∈ G, |p.1| ≤ 4)
    (hdegree : ∀ b ∈ G.image Prod.snd,
      d * ((G.image Prod.fst).card : ℝ) ≤ ((G.filter (fun p => p.2 = b)).card : ℝ)) :
    RealFiniteFrostman δ (5 * C / d) (β - 1) (G.image Prod.snd) := by
  have hbound' : ∀ p ∈ G.image Prod.swap, |p.2| ≤ 4 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact hbound q hq
  have hdegree' : ∀ a ∈ (G.image Prod.swap).image Prod.fst,
      d * (((G.image Prod.swap).image Prod.snd).card : ℝ) ≤
        (((G.image Prod.swap).filter (fun p => p.1 = a)).card : ℝ) := by
    intro a ha
    have ha' : a ∈ G.image Prod.snd := by simpa [Finset.image_image, Function.comp_def] using ha
    have heq : (G.image Prod.swap).filter (fun p => p.1 = a) =
        (G.filter (fun p => p.2 = a)).image Prod.swap := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, h⟩
        exact ⟨q, ⟨hq, h⟩, rfl⟩
      · rintro ⟨q, ⟨hq, h⟩, rfl⟩
        exact ⟨⟨q, hq, rfl⟩, h⟩
    rw [heq, Finset.card_image_of_injective _ Prod.swap_injective]
    simpa [Finset.image_image, Function.comp_def] using hdegree a ha'
  simpa [Finset.image_image, Function.comp_def] using hG.swap.first_marginal hδ hC hβ hd hd1
    (hGne.image Prod.swap) hbound' hdegree'

end WangZahlLot.Obl.wz_square_frostman_graph_projection.SP
