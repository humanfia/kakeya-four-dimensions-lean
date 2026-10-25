-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.TubeDictionary.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/TubeDictionary.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CoarseWolff
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CoarseTubeCounts

/-!
# Labels per tube at two palette scales

For the tube-line Frostman bound of a coarse tube (`coarse_square_count`) one needs
`L_max,w / L_T ≲ (w / ρ) ^ (2 s)`: the labels of a `w`-tube against those of the `ρ`-tube `T`.
This file collects the counting steps.

* `fiber_le_of_balanced`, `fiber_ge_of_balanced`: a balanced map has fibers `≍ |S| / #image`.
* `composed_tubes_le`: the `ρ`-tubes of the `δ`-tubes of the labels are, up to
  `nearTubeConst`, no more than the `ρ`-tubes of the labels.
* `pinTubes_ge_of_caps`: a pin meets at least `|bush| / (2 · 49 M)` tubes at scale `w` when every
  `w`-arc holds at most `M` of its normals.
* `occupied_tubes_ge`: x0563/x0675's Cauchy--Schwarz (`cell_tubes_bound`, as inside
  `tube_lines_upper`): `B² ≤ pinConst w C_Y K_Y · #occupied tubes` when every pin meets `≥ B`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_tower_balanced_refinement

attribute [local instance] Classical.propDecidable

/-- A balanced map has every fiber at most `K |S| / #image`. -/
theorem fiber_le_of_balanced {α β : Type*} [DecidableEq α] [DecidableEq β] {S : Finset α}
    {f : α → β} {K : ℝ} (hbal : Balanced S f K) {q : α} (hq : q ∈ S) :
    ((S.filter (fun q' => f q' = f q)).card : ℝ) * (S.image f).card ≤ K * S.card := by
  classical
  have h1 := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := S.image f)
    (fun x hx => Finset.mem_image_of_mem f hx)
  have hfib : ∀ b ∈ S.image f, ((S.filter (fun q' => f q' = f q)).card : ℝ) ≤
      K * (S.filter (fun q' => f q' = b)).card := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    have e1 : S.filter (fun q' => f q' = f q) = leafFiber S f q := by
      ext a; simp [leafFiber]
    have e2 : S.filter (fun q' => f q' = f x) = leafFiber S f x := by
      ext a; simp [leafFiber]
    rw [e1, e2]; exact hbal q hq x hx
  calc ((S.filter (fun q' => f q' = f q)).card : ℝ) * (S.image f).card
      = ∑ _b ∈ S.image f, ((S.filter (fun q' => f q' = f q)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ b ∈ S.image f, K * ((S.filter (fun q' => f q' = b)).card : ℝ) :=
        Finset.sum_le_sum hfib
    _ = K * S.card := by
        rw [← Finset.mul_sum]
        congr 1
        exact_mod_cast h1.symm

/-- A balanced map has every fiber at least `|S| / (K #image)`. -/
theorem fiber_ge_of_balanced {α β : Type*} [DecidableEq α] [DecidableEq β] {S : Finset α}
    {f : α → β} {K : ℝ} (hbal : Balanced S f K) {q : α} (hq : q ∈ S) :
    (S.card : ℝ) ≤ K * (S.image f).card * (S.filter (fun q' => f q' = f q)).card := by
  classical
  have h1 := Finset.card_eq_sum_card_fiberwise (f := f) (s := S) (t := S.image f)
    (fun x hx => Finset.mem_image_of_mem f hx)
  have hfib : ∀ b ∈ S.image f, ((S.filter (fun q' => f q' = b)).card : ℝ) ≤
      K * (S.filter (fun q' => f q' = f q)).card := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    have e1 : S.filter (fun q' => f q' = f q) = leafFiber S f q := by
      ext a; simp [leafFiber]
    have e2 : S.filter (fun q' => f q' = f x) = leafFiber S f x := by
      ext a; simp [leafFiber]
    rw [e1, e2]; exact hbal x hx q hq
  calc (S.card : ℝ) = ∑ b ∈ S.image f, ((S.filter (fun q' => f q' = b)).card : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ _b ∈ S.image f, K * ((S.filter (fun q' => f q' = f q)).card : ℝ) :=
        Finset.sum_le_sum hfib
    _ = K * (S.image f).card * (S.filter (fun q' => f q' = f q)).card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Composed tubes are not more numerous.** The `ρ`-tubes of the `δ`-tubes of the labels are at
most `nearTubeConst` times the `ρ`-tubes of the labels (`δ ≤ ρ`, `67 ρ ≤ 1/2`). -/
theorem composed_tubes_le {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : 2 * δ ≤ ρ) (hρ2 : 67 * ρ ≤ 1 / 2)
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
    ((S.image (fun q => tbH (tbA (cls q)))).card : ℝ) ≤
      nearTubeConst * (S.image (fun q => tbH (cls q))).card := by
  classical
  have hρ : 0 < ρ := by linarith
  set Near : E2 × E2 → Finset (E2 × E2) := fun k =>
    J₁.filter (fun j => ¬ StripSep (67 * ρ) j k ∨ ¬ StripSep (67 * ρ) k j)
    with hNear
  have hsub : S.image (fun q => tbH (tbA (cls q))) ⊆
      (S.image (fun q => tbH (cls q))).biUnion Near := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    have hℓ := hcls q hq
    have hℓa := htbA _ hℓ
    -- the `δ`-tube of `cls q` and `cls q` itself are `(9δ, δ)`-close
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
    have h25 : 25 * (δ + δ) + 42 * ρ ≤ 67 * ρ := by linarith
    refine Finset.mem_biUnion.mpr ⟨tbH (cls q), Finset.mem_image_of_mem _ hq, ?_⟩
    refine Finset.mem_filter.mpr ⟨htbH _ hℓa, Or.inl ?_⟩
    intro hs
    exact hnot (stripSep_mono (by linarith) hs)
  have hNearle : ∀ k ∈ S.image (fun q => tbH (cls q)), ((Near k).card : ℝ) ≤ nearTubeConst := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    exact near_tubes_le (W := 67 * ρ) hρ hρ2 le_rfl hJ₁ hJ₁sep (htbH _ (hcls q hq))
  calc ((S.image (fun q => tbH (tbA (cls q)))).card : ℝ)
      ≤ ((S.image (fun q => tbH (cls q))).biUnion Near).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ k ∈ S.image (fun q => tbH (cls q)), ((Near k).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ S.image (fun q => tbH (cls q)), nearTubeConst := Finset.sum_le_sum hNearle
    _ = nearTubeConst * (S.image (fun q => tbH (cls q))).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Labels of a pin in one tube.** Their normals lie within `r + w ≤ 3 w` of `± (tube normal)`,
so at most `2 · 49 · M` of them when every `w`-arc holds at most `M` normals of the pin. -/
theorem pin_tube_labels_le_caps {r w M : ℝ} (hr : 0 ≤ r) (hrw : r ≤ 2 * w) (hw : 0 < w)
    (hM0 : 0 ≤ M) {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2} {p : E2}
    (hgeo : ∀ q ∈ S, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (htb : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb (cls q)).1) (tb (cls q)).2| < 9 * w ∧
      (dist (cls q).2 (tb (cls q)).2 < w ∨ dist (cls q).2 (-(tb (cls q)).2) < w))
    (hM : ∀ e ∈ bushOf S p, ((arcNormals w S p e).card : ℝ) ≤ M)
    {q : E2 × E2} (hq : q ∈ S) (hqp : q.1 = p) :
    ((S.filter (fun a => a.1 = p ∧ tb (cls a) = tb (cls q))).card : ℝ) ≤ 2 * (49 * M) := by
  classical
  set k := tb (cls q) with hk
  set A := S.filter (fun a => a.1 = p ∧ tb (cls a) = k) with hA
  have hinj : (A.image Prod.snd).card = A.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2.1
    have hb' := (Finset.mem_filter.mp hb).2.1
    exact Prod.ext (ha'.trans hb'.symm) hab
  have hsub : A.image Prod.snd ⊆ (bushOf S p).filter (fun e => dist e k.2 ≤ 3 * w) ∪
      (bushOf S p).filter (fun e => dist e (-k.2) ≤ 3 * w) := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨haS, hap, hak⟩ := Finset.mem_filter.mp ha
    have hmem : a.2 ∈ bushOf S p := by rw [mem_bushOf, ← hap]; exact haS
    have hn := normal_close_trans (hgeo a haS).2 (htb a haS).2
    rw [hak] at hn
    rcases hn with hn | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, by linarith⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem, by linarith⟩)
  have h1 := bush_cap_le_arcs (u := k.2) hw hM0 hM
  have h2 := bush_cap_le_arcs (u := -k.2) hw hM0 hM
  calc (A.card : ℝ) = (A.image Prod.snd).card := by rw [hinj]
    _ ≤ ((bushOf S p).filter (fun e => dist e k.2 ≤ 3 * w) ∪
          (bushOf S p).filter (fun e => dist e (-k.2) ≤ 3 * w)).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((bushOf S p).filter (fun e => dist e k.2 ≤ 3 * w)).card +
          ((bushOf S p).filter (fun e => dist e (-k.2) ≤ 3 * w)).card := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ 49 * M + 49 * M := add_le_add h1 h2
    _ = 2 * (49 * M) := by ring

/-- **A pin meets many tubes.** `|bush p| ≤ #tubes(p) · 98 M` (`bush_le_pinTubes`). -/
theorem pinTubes_ge_of_caps {r w M : ℝ} (hr : 0 ≤ r) (hrw : r ≤ 2 * w) (hw : 0 < w)
    (hM0 : 0 ≤ M) {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2} (p : E2)
    (hgeo : ∀ q ∈ S, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (htb : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb (cls q)).1) (tb (cls q)).2| < 9 * w ∧
      (dist (cls q).2 (tb (cls q)).2 < w ∨ dist (cls q).2 (-(tb (cls q)).2) < w))
    (hM : ∀ e ∈ bushOf S p, ((arcNormals w S p e).card : ℝ) ≤ M) :
    ((bushOf S p).card : ℝ) ≤ (pinTubes S cls tb p).card * (2 * (49 * M)) :=
  bush_le_pinTubes p (fun q hq hqp => pin_tube_labels_le_caps hr hrw hw hM0 hgeo htb hM hq hqp)

/-- **Occupied tubes, Cauchy--Schwarz with the pins as points** (`cell_tubes_bound`, as inside
`tube_lines_upper`): if every pin meets at least `B` tubes,
`B² ≤ pinConst w (r^(-η') / r / #pins) K_Y · #occupied tubes`. -/
theorem occupied_tubes_ge {r s ε₀ η' w B : ℝ} (hrw : r ≤ w) (hw2 : 26 * w ≤ 1 / 2) (hB : 0 ≤ B)
    {S : Finset (E2 × E2)} (hS : FailData r s ε₀ η' (S.image Prod.fst) S)
    {cls tb : E2 × E2 → E2 × E2} {J₁ : Finset (E2 × E2)}
    (hcls4 : ∀ q ∈ S, ‖(cls q).1‖ ≤ 4) (hcls1 : ∀ q ∈ S, ‖(cls q).2‖ = 1)
    (hgeo : ∀ q ∈ S, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (htbJ : ∀ q ∈ S, tb (cls q) ∈ J₁) (hJ₁ : ∀ j ∈ J₁, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hJ₁sep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep w x y)
    (htb : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb (cls q)).1) (tb (cls q)).2| < 9 * w ∧
      (dist (cls q).2 (tb (cls q)).2 < w ∨ dist (cls q).2 (-(tb (cls q)).2) < w))
    (hBpin : ∀ p ∈ S.image Prod.fst, B ≤ ((pinTubes S cls tb p).card : ℝ))
    (KY : ℕ) (hKY : ((S.image Prod.fst).card : ℝ) ≤ 2 ^ KY) :
    B ^ 2 ≤ pinConst w (r ^ (-η') / r / ((S.image Prod.fst).card : ℝ)) KY *
      (S.image (fun q => tb (cls q))).card := by
  classical
  have hr := hS.r_pos
  have hw : 0 < w := lt_of_lt_of_le hr hrw
  set Q := S.image Prod.fst with hQ
  set T := S.image (fun a => tb (cls a)) with hT
  have hQpos : (0 : ℝ) < Q.card := by
    obtain ⟨a, ha⟩ := hS.P_ne
    exact_mod_cast Finset.card_pos.mpr ⟨a, ha⟩
  have hCY0 : 0 ≤ r ^ (-η') / r / (Q.card : ℝ) :=
    div_nonneg (div_nonneg (Real.rpow_nonneg hr.le _) hr.le) hQpos.le
  have hYfr : ∀ (x : E2) (t : ℝ), w ≤ t →
      ((Q.filter (fun z => z ∈ Metric.closedBall x t)).card : ℝ) ≤
        (r ^ (-η') / r / (Q.card : ℝ)) * t * Q.card := by
    intro x t ht
    have h1 := hS.P_kt x t (hrw.trans ht)
    have heq : Q.filter (fun z => z ∈ Metric.closedBall x t) = Q.filter (fun p => dist p x ≤ t) := by
      ext z; simp [Metric.mem_closedBall]
    rw [heq]
    calc ((Q.filter (fun p => dist p x ≤ t)).card : ℝ) ≤ r ^ (-η') * (t / r) := h1
      _ = (r ^ (-η') / r / (Q.card : ℝ)) * t * Q.card := by field_simp
  have hY4 : ∀ y ∈ Q, ‖y‖ ≤ 4 := fun y hy => hS.P_norm y hy
  have hTJ₁ : T ⊆ J₁ := by
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
    exact htbJ a ha
  have hTprop : ∀ j ∈ T, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1 := fun j hj => hJ₁ j (hTJ₁ hj)
  have hinc : ∀ y ∈ Q, B ≤ ((T.filter (fun j => |inner ℝ (y - j.1) j.2| < 26 * w)).card : ℝ) := by
    intro y hy
    refine (hBpin y hy).trans ?_
    have hsub : pinTubes S cls tb y ⊆ T.filter (fun j => |inner ℝ (y - j.1) j.2| < 26 * w) := by
      intro j hj
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨hbS, hby⟩ := Finset.mem_filter.mp hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨b, hbS, rfl⟩, ?_⟩
      have hj1 : ‖(tb (cls b)).2‖ = 1 := (hJ₁ _ (htbJ b hbS)).2
      have hb4 : ‖b.1‖ ≤ 4 := hS.P_norm _ (Finset.mem_image_of_mem _ hbS)
      have hnear := pin_near_tube hb4 (hcls4 b hbS) (hcls1 b hbS) hj1
        (hgeo b hbS).1 (htb b hbS).1 (htb b hbS).2
      rw [← hby]
      linarith
    exact_mod_cast Finset.card_le_card hsub
  have hQne : Q.Nonempty := hS.P_ne
  have hCS := cell_tubes_bound hw (by linarith : w ≤ 26 * w) hw2 hCY0 hB Q hQne hY4 hYfr T hTprop
    (fun x hx y hy hne => hJ₁sep x (hTJ₁ hx) y (hTJ₁ hy) hne) KY hKY hinc
  have hCSeq : 128000 * (64 * (26 * w) / w + 2) * (36 * (26 * w) / w + 2) *
      (r ^ (-η') / r / (Q.card : ℝ)) * (1 + Real.log (1 / (26 * w))) * ((KY : ℝ) + 1) ^ 2 *
        T.card = pinConst w (r ^ (-η') / r / (Q.card : ℝ)) KY * T.card := by
    unfold pinConst; ring
  rw [hCSeq] at hCS
  exact hCS

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
