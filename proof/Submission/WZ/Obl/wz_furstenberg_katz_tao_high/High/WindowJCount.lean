-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowJCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/WindowJCount.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowLineFrostman
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseAObjects

/-!
# The number of `δ`-lines of a window tube

* `plain_tubes_le_composed`: the occupied plain `ρ`-tubes `tb h (cls q)` are at most
  `nearTubeConst` times the occupied composed tubes `tb h (tb a (cls q))` (the reverse of x0688's
  `composed_tubes_le`, with the same packing argument).
* `window_lines_card_le`: by the balances of `tb a ∘ cls` and of the composed map,
  `#J(T) ≤ K² #(δ-lines) / #(composed tubes)`, `K = r^-ε`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- **Plain tubes against composed tubes** (packing; adapted from x0688's `composed_tubes_le`
in `High/TubeDictionary.lean`). -/
theorem plain_tubes_le_composed {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : 2 * δ ≤ ρ) (hρ2 : 67 * ρ ≤ 1 / 2)
    {S J₀ J₁ : Finset (E2 × E2)} {cls tbA tbH : E2 × E2 → E2 × E2}
    (hcls : ∀ q ∈ S, cls q ∈ J₀) (hJ₀4 : ∀ ℓ ∈ J₀, ‖ℓ.1‖ ≤ 4)
    (htbA : ∀ ℓ ∈ J₀, tbA ℓ ∈ J₀)
    (htbAgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tbA ℓ).1) (tbA ℓ).2| < 9 * δ ∧
      (dist ℓ.2 (tbA ℓ).2 < δ ∨ dist ℓ.2 (-(tbA ℓ).2) < δ))
    (htbH : ∀ ℓ ∈ J₀, tbH ℓ ∈ J₁)
    (htbHgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tbH ℓ).1) (tbH ℓ).2| < 9 * ρ ∧
      (dist ℓ.2 (tbH ℓ).2 < ρ ∨ dist ℓ.2 (-(tbH ℓ).2) < ρ))
    (hJ₁ : ∀ j ∈ J₁, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hJ₁sep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep ρ x y) :
    ((S.image (fun q => tbH (cls q))).card : ℝ) ≤
      nearTubeConst * (S.image (fun q => tbH (tbA (cls q)))).card := by
  classical
  have hρ : 0 < ρ := by linarith
  set Near : E2 × E2 → Finset (E2 × E2) := fun k =>
    J₁.filter (fun j => ¬ StripSep (67 * ρ) j k ∨ ¬ StripSep (67 * ρ) k j)
    with hNear
  have hsub : S.image (fun q => tbH (cls q)) ⊆
      (S.image (fun q => tbH (tbA (cls q)))).biUnion Near := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    have hℓ := hcls q hq
    have hℓa := htbA _ hℓ
    have hclose : |inner ℝ ((tbA (cls q)).1 - (cls q).1) (cls q).2| < 9 * (δ + δ) ∧
        (dist (tbA (cls q)).2 (cls q).2 < δ + δ ∨ dist (tbA (cls q)).2 (-(cls q).2) < δ + δ) := by
      obtain ⟨g1, g2⟩ := htbAgeo _ hℓ
      have hn' := normal_close_symm g2
      have hv : ‖(tbA (cls q)).1 - (cls q).1‖ ≤ 8 := by
        calc ‖(tbA (cls q)).1 - (cls q).1‖ ≤ ‖(tbA (cls q)).1‖ + ‖(cls q).1‖ := norm_sub_le _ _
          _ ≤ 8 := by linarith [hJ₀4 _ hℓa, hJ₀4 _ hℓ]
      have hA : |inner ℝ ((tbA (cls q)).1 - (cls q).1) (tbA (cls q)).2| < 9 * δ := by
        rw [show (tbA (cls q)).1 - (cls q).1 = -((cls q).1 - (tbA (cls q)).1) by abel,
          inner_neg_left, abs_neg]
        exact g1
      have hb := inner_le_of_close hv hA (normal_close_symm hn')
      refine ⟨by linarith, ?_⟩
      rcases hn' with h | h
      · left; linarith
      · right; linarith
    have hnot := tubes_close_of_lines_close (hJ₀4 _ hℓa) (hJ₀4 _ hℓ) (hJ₁ _ (htbH _ hℓa)).1
      (hJ₁ _ (htbH _ hℓ)).1 hclose (htbHgeo _ hℓa) (htbHgeo _ hℓ)
    refine Finset.mem_biUnion.mpr ⟨tbH (tbA (cls q)), Finset.mem_image_of_mem _ hq, ?_⟩
    refine Finset.mem_filter.mpr ⟨htbH _ hℓ, Or.inr ?_⟩
    intro hs
    exact hnot (stripSep_mono (by linarith) hs)
  have hNearle : ∀ k ∈ S.image (fun q => tbH (tbA (cls q))), ((Near k).card : ℝ) ≤
      nearTubeConst := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    exact near_tubes_le (W := 67 * ρ) hρ hρ2 le_rfl hJ₁ hJ₁sep (htbH _ (htbA _ (hcls q hq)))
  calc ((S.image (fun q => tbH (cls q))).card : ℝ)
      ≤ ((S.image (fun q => tbH (tbA (cls q)))).biUnion Near).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ k ∈ S.image (fun q => tbH (tbA (cls q))), ((Near k).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ S.image (fun q => tbH (tbA (cls q))), nearTubeConst := Finset.sum_le_sum hNearle
    _ = nearTubeConst * (S.image (fun q => tbH (tbA (cls q)))).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The `δ`-lines of a window tube**: `#J(T) ≤ K² #(δ-lines) / #(composed tubes)`. -/
theorem window_lines_card_le {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2}
    {D S J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
    {tb : ℕ → E2 × E2 → E2 × E2}
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {a h : ℕ} (ha : a ≤ n) (hh : h ≤ n)
    {T : E2 × E2} (hT : T ∈ S.image (fun q => tb h (tb a (cls q)))) :
    ((windowLines S cls tb a h T).card : ℝ) *
        (S.image (fun q => tb h (tb a (cls q)))).card ≤
      (r ^ (-ε)) ^ 2 * (S.image (fun q => tb a (cls q))).card := by
  classical
  set K := r ^ (-ε) with hK
  have hr0 : 0 < r := hC.fail.r_pos
  have hK0 : 0 < K := Real.rpow_pos_of_pos hr0 _
  obtain ⟨qT, hqT, hqTT⟩ := Finset.mem_image.mp hT
  set FT := S.filter (fun q => tb h (tb a (cls q)) = T) with hFT
  have hS0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨qT, hqT⟩
  -- the composed tube holds at most `K |S| / #composed` labels
  have hup := fiber_le_of_balanced (hC.bal_tube2 h hh a ha) hqT
  rw [hqTT] at hup
  -- each `δ`-line holds at least `|S| / (K #δ-lines)` labels
  have hlow : ∀ j ∈ windowLines S cls tb a h T,
      (S.card : ℝ) ≤ K * (S.image (fun q => tb a (cls q))).card *
        (S.filter (fun q => tb a (cls q) = j)).card := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact fiber_ge_of_balanced (hC.bal_tube a ha) (mem_windowLabels.mp hq).1
  -- the `δ`-lines of `T` hold disjoint sets of labels of `T`
  have hdisj : ((windowLines S cls tb a h T : Finset (E2 × E2)) : Set (E2 × E2)).PairwiseDisjoint
      (fun j => S.filter (fun q => tb a (cls q) = j)) := by
    intro j _ j' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro q hq hq'
    exact hne ((Finset.mem_filter.mp hq).2.symm.trans (Finset.mem_filter.mp hq').2)
  have hsub : (windowLines S cls tb a h T).biUnion (fun j => S.filter (fun q => tb a (cls q) = j))
      ⊆ FT := by
    intro q hq
    obtain ⟨j, hj, hqj⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hqS, hqj'⟩ := Finset.mem_filter.mp hqj
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hj
    refine Finset.mem_filter.mpr ⟨hqS, ?_⟩
    rw [hqj']; exact (mem_windowLabels.mp hq').2
  have hsum := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
  rw [Finset.card_biUnion hdisj] at hsum
  push_cast at hsum
  set NA := ((S.image (fun q => tb a (cls q))).card : ℝ) with hNA
  set NC := ((S.image (fun q => tb h (tb a (cls q)))).card : ℝ) with hNC
  have hNA0 : 0 < NA := by
    rw [hNA]; exact_mod_cast Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ hqT⟩
  have hlow' : ∀ j ∈ windowLines S cls tb a h T,
      (S.card : ℝ) / (K * NA) ≤ ((S.filter (fun q => tb a (cls q) = j)).card : ℝ) := by
    intro j hj
    rw [div_le_iff₀ (by positivity)]
    have := hlow j hj
    linarith
  have hsumlow : ((windowLines S cls tb a h T).card : ℝ) * ((S.card : ℝ) / (K * NA)) ≤
      ∑ j ∈ windowLines S cls tb a h T, ((S.filter (fun q => tb a (cls q) = j)).card : ℝ) := by
    have := Finset.sum_le_sum hlow'
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  -- combine
  have h1 : ((windowLines S cls tb a h T).card : ℝ) * ((S.card : ℝ) / (K * NA)) * NC ≤ K * S.card :=
    calc ((windowLines S cls tb a h T).card : ℝ) * ((S.card : ℝ) / (K * NA)) * NC
        ≤ (FT.card : ℝ) * NC := mul_le_mul_of_nonneg_right (hsumlow.trans hsum) (Nat.cast_nonneg _)
      _ ≤ K * S.card := by rw [hFT]; exact hup
  have h2 : ((windowLines S cls tb a h T).card : ℝ) * NC * S.card ≤ K ^ 2 * NA * S.card := by
    have e : ((windowLines S cls tb a h T).card : ℝ) * ((S.card : ℝ) / (K * NA)) * NC =
        ((windowLines S cls tb a h T).card : ℝ) * NC * S.card / (K * NA) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)] at h1
    nlinarith
  have := le_of_mul_le_mul_right h2 hS0
  linarith

/-- **`#J(T)` against the arc averages.** With `K = r^-ε`, `avg_j = arcAvg (palScale r n j) S p₀`:
`#J(T) · (avg_a / (K² C))² · (r^(ε-s) / (2·49·K·avg_h))² ≤ K² · quadConst · #lines ·
nearTubeConst · pinConst`. -/
theorem window_lines_card_le_avg {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2}
    {D S J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)}
    {tb : ℕ → E2 × E2 → E2 × E2}
    (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {a h : ℕ} (ha : a ≤ n) (hh : h ≤ n)
    (hrδ : 10 * r ≤ palScale r n a) (hδρ : 2 * palScale r n a ≤ palScale r n h)
    (hρ2 : 142 * palScale r n h ≤ 1 / 2)
    {T : E2 × E2} (hT : T ∈ S.image (fun q => tb h (tb a (cls q))))
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst) {c : ℝ} (hrc : r ≤ c)
    (hcfar : r ^ (-κ) * c ^ (1 - s) ≤ 1 / 2) (KY : ℕ)
    (hKY : ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY) :
    ((windowLines S cls tb a h T).card : ℝ) *
        ((arcAvg (palScale r n a) S p₀ / ((r ^ (-ε)) ^ 2 * arcTubeConst)) ^ 2 *
          (r ^ (ε - s) / (2 * (49 * (r ^ (-ε) * arcAvg (palScale r n h) S p₀)))) ^ 2) ≤
      (r ^ (-ε)) ^ 2 * (quadConst r s ε (r ^ (-ε)) c * (S.image cls).card) *
        (nearTubeConst * pinConst (palScale r n h)
          (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY) := by
  classical
  have hr0 : 0 < r := hC.fail.r_pos
  set δ := palScale r n a with hδ
  set ρ := palScale r n h with hρ
  have hδ0 : 0 < δ := by linarith
  set NA := ((S.image (fun q => tb a (cls q))).card : ℝ) with hNA
  set NC := ((S.image (fun q => tb h (tb a (cls q)))).card : ℝ) with hNC
  set NP := ((S.image (fun q => tb h (cls q))).card : ℝ) with hNP
  set X := (arcAvg δ S p₀ / ((r ^ (-ε)) ^ 2 * arcTubeConst)) ^ 2 with hX
  set Y := (r ^ (ε - s) / (2 * (49 * (r ^ (-ε) * arcAvg ρ S p₀)))) ^ 2 with hY
  set Q := quadConst r s ε (r ^ (-ε)) c * (S.image cls).card with hQ
  set PC := pinConst ρ (r ^ (-ε) / r / ((S.image Prod.fst).card : ℝ)) KY with hPC
  have h1 := window_lines_card_le hC ha hh hT
  have h2 : NA * X ≤ Q := hC.tubes_upper hs0 hs1 ha hrδ (by linarith) hp₀ hrc hcfar
  have h3 : Y ≤ PC * NP := hC.tubes_lower hh (by linarith) (by linarith) hp₀ KY hKY
  -- plain tubes against composed tubes
  have h4 : NP ≤ nearTubeConst * NC := by
    refine plain_tubes_le_composed hδ0 hδρ (by linarith) (J₀ := J₀) (J₁ := J₁ h)
      (fun q hq => hC.cls_mem q (hC.sub hq))
      (fun ℓ hℓ => (hC.fail.P_norm _ (hC.fail.D_mem ℓ (hC.lines_sub hℓ)).1))
      (fun ℓ hℓ => hC.tubes_sub a (hC.tube_mem a ha ℓ hℓ))
      (fun ℓ hℓ => hC.tube_geo a ha ℓ hℓ)
      (fun ℓ hℓ => hC.tube_mem h hh ℓ hℓ)
      (fun ℓ hℓ => hC.tube_geo h hh ℓ hℓ)
      (fun j hj => ⟨hC.fail.P_norm _ (hC.fail.D_mem j (hC.lines_sub (hC.tubes_sub h hj))).1,
        (hC.fail.D_mem j (hC.lines_sub (hC.tubes_sub h hj))).2⟩)
      (fun x hx y hy hne => hC.tubes_sep h hh x hx y hy hne)
  have hX0 : 0 ≤ X := sq_nonneg _
  have hY0 : 0 ≤ Y := sq_nonneg _
  have hK2 : 0 ≤ (r ^ (-ε)) ^ 2 := sq_nonneg _
  have hJ0 : (0 : ℝ) ≤ (windowLines S cls tb a h T).card := Nat.cast_nonneg _
  have hNC0 : 0 ≤ NC := Nat.cast_nonneg _
  have hNP0 : 0 ≤ NP := Nat.cast_nonneg _
  have hPC0 : 0 ≤ PC := pinConst_nonneg' (by linarith) (by linarith) (by positivity)
  have hnTC : 0 ≤ nearTubeConst := nearTubeConst_pos.le
  have hY' : Y ≤ PC * (nearTubeConst * NC) :=
    h3.trans (mul_le_mul_of_nonneg_left h4 hPC0)
  have h1' : ((windowLines S cls tb a h T).card : ℝ) * NC ≤ (r ^ (-ε)) ^ 2 * NA := by
    rw [hNC, hNA]; exact h1
  calc ((windowLines S cls tb a h T).card : ℝ) * (X * Y)
      ≤ ((windowLines S cls tb a h T).card : ℝ) * (X * (PC * (nearTubeConst * NC))) := by
        apply mul_le_mul_of_nonneg_left _ hJ0
        exact mul_le_mul_of_nonneg_left hY' hX0
    _ = (((windowLines S cls tb a h T).card : ℝ) * NC) * X * (nearTubeConst * PC) := by ring
    _ ≤ ((r ^ (-ε)) ^ 2 * NA) * X * (nearTubeConst * PC) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hnTC hPC0)
        exact mul_le_mul_of_nonneg_right h1' hX0
    _ = (r ^ (-ε)) ^ 2 * (NA * X) * (nearTubeConst * PC) := by ring
    _ ≤ (r ^ (-ε)) ^ 2 * Q * (nearTubeConst * PC) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hnTC hPC0)
        exact mul_le_mul_of_nonneg_left h2 hK2

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
