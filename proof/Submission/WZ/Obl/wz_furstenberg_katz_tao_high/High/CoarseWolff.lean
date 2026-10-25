-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CoarseWolff.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/CoarseWolff.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Hairbrush
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeUpper
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.Maximal

/-!
# Wolff's hairbrush at a coarse scale

Points `P'` that are `3 ρ`-separated (for instance one pin per occupied `ρ`-cell), their fine
labels `D'`, the fine lines `cls` (geometry `9 r` / `r` of `FailData.classes`) and the coarse
tubes `tb` of those lines at scale `ρ` (geometry `9 ρ` / `ρ` of `exists_coarse_tubes`).
Composing the two maps sends every label to a coarse tube with the geometry `9 (3ρ)` / `3ρ`
(`pin_near_tube`, `normal_close_trans`), so x0672's `separated_hairbrush` applies at the
separation `3 ρ`:

`coarse_hairbrush`: `|P'| Nb (Nb - 2 Kθ) ≤ 4 (49 M)² (900/θ₀ + 3)² #(coarse tubes of D')²`,

where `Nb` bounds the fine bushes from below, `Kθ` bounds their `θ₀`-caps and `M` bounds the
normals of one bush in one `ρ`-arc (a `3ρ`-cap of a bush meets at most `49` arcs,
`bush_cap_le_arcs`). With balanced arcs (`M ≈` normals per (pin, arc)) and the tube count
`#tubes ≲ #lines / M²`, this is the coarse Wolff constraint `#cells(ρ) ≲ #arcs(ρ)²`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

/-- A coordinate of a vector in the plane is at most its norm. -/
theorem abs_coord_le_norm (v : E2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h := PiLp.norm_apply_le v i
  simpa [Real.norm_eq_abs] using h

/-- Floors of two reals at distance at most `3` differ by at most `3`. -/
theorem floor_sub_le_three {x y : ℝ} (h : |x - y| ≤ 3) :
    ⌊y⌋ - 3 ≤ ⌊x⌋ ∧ ⌊x⌋ ≤ ⌊y⌋ + 3 := by
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  constructor
  · have : ⌊y⌋ - 3 ≤ ⌊x⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith [Int.floor_le y]
    exact this
  · have : ⌊x⌋ < ⌊y⌋ + 4 := by
      rw [Int.floor_lt]
      push_cast
      linarith [Int.lt_floor_add_one y]
    omega

/-- The `ρ`-arcs (squares of the `ρ`-grid) met by the normals within `3 ρ` of `u` lie in a
`7 × 7` box. -/
theorem arcOf_mem_box {ρ : ℝ} (hρ : 0 < ρ) {e u : E2} (h : dist e u ≤ 3 * ρ) :
    arcOf ρ e ∈ (Finset.Icc (⌊u 0 / ρ⌋ - 3) (⌊u 0 / ρ⌋ + 3) ×ˢ
      Finset.Icc (⌊u 1 / ρ⌋ - 3) (⌊u 1 / ρ⌋ + 3)) := by
  have hcoord : ∀ i : Fin 2, |e i / ρ - u i / ρ| ≤ 3 := by
    intro i
    have h1 : |e i - u i| ≤ dist e u := by
      rw [dist_eq_norm]
      have := abs_coord_le_norm (e - u) i
      simpa using this
    rw [← sub_div, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
    linarith
  obtain ⟨a0, b0⟩ := floor_sub_le_three (hcoord 0)
  obtain ⟨a1, b1⟩ := floor_sub_le_three (hcoord 1)
  simp only [arcOf, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨a0, b0⟩, ⟨a1, b1⟩⟩

/-- A `3 ρ`-cap of a bush meets at most `49` arcs: if every arc holds at most `M` normals of
the bush of `p`, the cap holds at most `49 M`. -/
theorem bush_cap_le_arcs {ρ M : ℝ} (hρ : 0 < ρ) (hM0 : 0 ≤ M) {S : Finset (E2 × E2)} {p u : E2}
    (hM : ∀ e ∈ bushOf S p, ((arcNormals ρ S p e).card : ℝ) ≤ M) :
    (((bushOf S p).filter (fun e => dist e u ≤ 3 * ρ)).card : ℝ) ≤ 49 * M := by
  classical
  set A := (bushOf S p).filter (fun e => dist e u ≤ 3 * ρ) with hA
  set box : Finset (ℤ × ℤ) := Finset.Icc (⌊u 0 / ρ⌋ - 3) (⌊u 0 / ρ⌋ + 3) ×ˢ
      Finset.Icc (⌊u 1 / ρ⌋ - 3) (⌊u 1 / ρ⌋ + 3) with hbox
  have hboxcard : (box.card : ℝ) ≤ 49 := by
    have : box.card = 49 := by
      rw [hbox, Finset.card_product, Int.card_Icc, Int.card_Icc]
      have e1 : (⌊u 0 / ρ⌋ + 3 + 1 - (⌊u 0 / ρ⌋ - 3)).toNat = 7 := by omega
      have e2 : (⌊u 1 / ρ⌋ + 3 + 1 - (⌊u 1 / ρ⌋ - 3)).toNat = 7 := by omega
      rw [e1, e2]
    rw [this]; norm_num
  have himg : A.image (arcOf ρ) ⊆ box := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    exact arcOf_mem_box hρ (Finset.mem_filter.mp he).2
  have hfib : ∀ a ∈ A.image (arcOf ρ), ((A.filter (fun e => arcOf ρ e = a)).card : ℝ) ≤ M := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    have hsub : A.filter (fun f => arcOf ρ f = arcOf ρ e) ⊆ arcNormals ρ S p e := by
      intro f hf
      obtain ⟨hfA, hfa⟩ := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hfA).1, hfa⟩
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub)
      (hM e (Finset.mem_filter.mp he).1)
  have hsum : (A.card : ℝ) ≤ ∑ a ∈ A.image (arcOf ρ),
      ((A.filter (fun e => arcOf ρ e = a)).card : ℝ) := by
    have := Finset.card_eq_sum_card_image (arcOf ρ) A
    exact_mod_cast this.le
  calc (A.card : ℝ) ≤ ∑ a ∈ A.image (arcOf ρ), ((A.filter (fun e => arcOf ρ e = a)).card : ℝ) :=
        hsum
    _ ≤ ∑ _a ∈ A.image (arcOf ρ), M := Finset.sum_le_sum hfib
    _ = (A.image (arcOf ρ)).card * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (box.card : ℝ) * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        exact_mod_cast Finset.card_le_card himg
    _ ≤ 49 * M := mul_le_mul_of_nonneg_right hboxcard hM0

/-- **Wolff's hairbrush for coarse tubes.** `3 ρ`-separated points with their fine labels,
fine lines `cls` (geometry `9 r` / `r`) and coarse tubes `tb` of those lines (geometry
`9 ρ` / `ρ`): the composed map is a class map at separation `3 ρ`, and x0672's
`separated_hairbrush` bounds the number of occupied coarse tubes from below. -/
theorem coarse_hairbrush {r ρ θ₀ Nb Kθ M : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (hθ₀ : 6 * ρ ≤ θ₀) (hθ₀2 : θ₀ ≤ 2) (hNb : 2 * Kθ ≤ Nb) (hNb0 : 0 < Nb) (hM0 : 0 ≤ M)
    {P' : Finset E2} {D' : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2}
    (hsep : ∀ p ∈ P', ∀ p' ∈ P', p ≠ p' → 3 * ρ ≤ dist p p')
    (hD : ∀ q ∈ D', q.1 ∈ P' ∧ ‖q.2‖ = 1) (hPne : P'.Nonempty)
    (hP4 : ∀ p ∈ P', ‖p‖ ≤ 4)
    (hbush : ∀ p ∈ P', Nb ≤ ((bushOf D' p).card : ℝ))
    (hkθ : ∀ p ∈ P', ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D' p).filter (fun e => dist e u ≤ θ₀)).card : ℝ) ≤ Kθ)
    (harc : ∀ p ∈ P', ∀ e ∈ bushOf D' p, ((arcNormals ρ D' p e).card : ℝ) ≤ M)
    (hcls4 : ∀ q ∈ D', ‖(cls q).1‖ ≤ 4) (hcls1 : ∀ q ∈ D', ‖(cls q).2‖ = 1)
    (hgeo : ∀ q ∈ D', |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (htb1 : ∀ q ∈ D', ‖(tb (cls q)).2‖ = 1)
    (htb : ∀ q ∈ D', |inner ℝ ((cls q).1 - (tb (cls q)).1) (tb (cls q)).2| < 9 * ρ ∧
      (dist (cls q).2 (tb (cls q)).2 < ρ ∨ dist (cls q).2 (-(tb (cls q)).2) < ρ)) :
    (P'.card : ℝ) * Nb * (Nb - 2 * Kθ) ≤
      4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2 *
        ((D'.image (fun q => tb (cls q))).card : ℝ) ^ 2 := by
  classical
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
  have hδ : 0 < 3 * ρ := by linarith
  refine separated_hairbrush (δ := 3 * ρ) (Kδ := 49 * M) (cls := fun q => tb (cls q))
    (J₀ := D'.image (fun q => tb (cls q))) hδ (by linarith) hθ₀2 hNb (by positivity)
    hsep hD hPne hNb0 hbush hkθ ?_ ?_ ?_ ?_
  · intro p hp u _
    exact bush_cap_le_arcs hρ hM0 (fun e he => harc p hp e he)
  · intro q hq
    exact Finset.mem_image_of_mem _ hq
  · intro q hq
    obtain ⟨g1, g2⟩ := hgeo q hq
    obtain ⟨t1, t2⟩ := htb q hq
    have hq4 : ‖q.1‖ ≤ 4 := hP4 q.1 (hD q hq).1
    have hpin := pin_near_tube hq4 (hcls4 q hq) (hcls1 q hq) (htb1 q hq) g1 t1 t2
    have hn := normal_close_trans g2 t2
    refine ⟨by linarith, ?_⟩
    rcases hn with hn | hn
    · left; linarith
    · right; linarith
  · intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact htb1 q hq

/-- A maximal `δ`-separated subset of a finite set of points covers it at distance `< δ`. -/
theorem exists_separated_reps (Q : Finset E2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ P' ⊆ Q, (∀ p ∈ P', ∀ p' ∈ P', p ≠ p' → δ ≤ dist p p') ∧
      ∀ q ∈ Q, ∃ p ∈ P', dist q p < δ := by
  classical
  obtain ⟨J, hJQ, hJsep, hJmax⟩ := exists_maximal_pairwise Q (fun p p' => δ ≤ dist p p')
  refine ⟨J, hJQ, hJsep, ?_⟩
  intro q hq
  by_cases hqJ : q ∈ J
  · exact ⟨q, hqJ, by rw [dist_self]; exact hδ⟩
  · obtain ⟨j, hj, h⟩ := hJmax q hq hqJ
    rcases h with h | h
    · exact ⟨j, hj, lt_of_not_ge h⟩
    · exact ⟨j, hj, by rw [dist_comm]; exact lt_of_not_ge h⟩

/-- Points covered by the `δ`-balls of `P'`, at most `B` of them in each ball, number at most
`|P'| B`. -/
theorem card_le_reps_mul {Q P' : Finset E2} {δ B : ℝ}
    (hcover : ∀ q ∈ Q, ∃ p ∈ P', dist q p < δ)
    (hB : ∀ p ∈ P', ((Q.filter (fun q => dist q p < δ)).card : ℝ) ≤ B) :
    (Q.card : ℝ) ≤ P'.card * B := by
  classical
  have hsub : Q ⊆ P'.biUnion (fun p => Q.filter (fun q => dist q p < δ)) := by
    intro q hq
    obtain ⟨p, hp, hd⟩ := hcover q hq
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hq, hd⟩⟩
  calc (Q.card : ℝ) ≤ (P'.biUnion (fun p => Q.filter (fun q => dist q p < δ))).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P', ((Q.filter (fun q => dist q p < δ)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P', B := Finset.sum_le_sum hB
    _ = P'.card * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- A `3 ρ`-ball meets at most `49` cells of the `ρ`-grid: if every cell holds at most `n`
points of `Q`, the ball holds at most `49 n`. -/
theorem ball_le_cells {ρ n : ℝ} (hρ : 0 < ρ) (hn : 0 ≤ n) {Q : Finset E2} {x : E2}
    (hcell : ∀ q ∈ Q, ((cellPins ρ Q q).card : ℝ) ≤ n) :
    ((Q.filter (fun q => dist q x < 3 * ρ)).card : ℝ) ≤ 49 * n := by
  classical
  set A := Q.filter (fun q => dist q x < 3 * ρ) with hA
  set box : Finset (ℤ × ℤ) := Finset.Icc (⌊x 0 / ρ⌋ - 3) (⌊x 0 / ρ⌋ + 3) ×ˢ
      Finset.Icc (⌊x 1 / ρ⌋ - 3) (⌊x 1 / ρ⌋ + 3) with hbox
  have hboxcard : (box.card : ℝ) ≤ 49 := by
    have : box.card = 49 := by
      rw [hbox, Finset.card_product, Int.card_Icc, Int.card_Icc]
      have e1 : (⌊x 0 / ρ⌋ + 3 + 1 - (⌊x 0 / ρ⌋ - 3)).toNat = 7 := by omega
      have e2 : (⌊x 1 / ρ⌋ + 3 + 1 - (⌊x 1 / ρ⌋ - 3)).toNat = 7 := by omega
      rw [e1, e2]
    rw [this]; norm_num
  have himg : A.image (cellOf ρ) ⊆ box := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    exact arcOf_mem_box hρ (le_of_lt (Finset.mem_filter.mp hq).2)
  have hfib : ∀ a ∈ A.image (cellOf ρ), ((A.filter (fun q => cellOf ρ q = a)).card : ℝ) ≤ n := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    have hsub : A.filter (fun f => cellOf ρ f = cellOf ρ q) ⊆ cellPins ρ Q q := by
      intro f hf
      obtain ⟨hfA, hfa⟩ := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hfA).1, hfa⟩
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub)
      (hcell q (Finset.mem_filter.mp hq).1)
  have hsum : (A.card : ℝ) ≤ ∑ a ∈ A.image (cellOf ρ),
      ((A.filter (fun q => cellOf ρ q = a)).card : ℝ) := by
    have := Finset.card_eq_sum_card_image (cellOf ρ) A
    exact_mod_cast this.le
  calc (A.card : ℝ) ≤ ∑ a ∈ A.image (cellOf ρ), ((A.filter (fun q => cellOf ρ q = a)).card : ℝ) :=
        hsum
    _ ≤ ∑ _a ∈ A.image (cellOf ρ), n := Finset.sum_le_sum hfib
    _ = (A.image (cellOf ρ)).card * n := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (box.card : ℝ) * n := by
        apply mul_le_mul_of_nonneg_right _ hn
        exact_mod_cast Finset.card_le_card himg
    _ ≤ 49 * n := mul_le_mul_of_nonneg_right hboxcard hn

/-- **Wolff at the coarse scale `ρ`.** All pins `Q` (at most `n` per `ρ`-cell), their labels
`S` (bushes of at least `Nb` normals, `θ₀`-caps at most `Kθ`, at most `M` normals per
`ρ`-arc), fine lines `cls` and coarse tubes `tb`: the pins are at most
`49 n · 4 (49 M)² (900/θ₀ + 3)² / (Nb (Nb - 2 Kθ))` times the square of the number of
occupied coarse tubes. Read with `n` the pins per cell: the number of occupied `ρ`-cells is
`≲ (M / Nb)² #tubes²`, i.e. `≲ #arcs² ` once `#tubes ≲ #lines / M²`. -/
theorem coarse_wolff {r ρ θ₀ Nb Kθ M n : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (hθ₀ : 6 * ρ ≤ θ₀) (hθ₀2 : θ₀ ≤ 2) (hNb : 2 * Kθ ≤ Nb) (hNb0 : 0 < Nb) (hM0 : 0 ≤ M)
    (hn : 0 ≤ n) {Q : Finset E2} {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2}
    (hS : ∀ q ∈ S, q.1 ∈ Q ∧ ‖q.2‖ = 1) (hQ4 : ∀ p ∈ Q, ‖p‖ ≤ 4)
    (hcell : ∀ q ∈ Q, ((cellPins ρ Q q).card : ℝ) ≤ n)
    (hbush : ∀ p ∈ Q, Nb ≤ ((bushOf S p).card : ℝ))
    (hkθ : ∀ p ∈ Q, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf S p).filter (fun e => dist e u ≤ θ₀)).card : ℝ) ≤ Kθ)
    (harc : ∀ p ∈ Q, ∀ e ∈ bushOf S p, ((arcNormals ρ S p e).card : ℝ) ≤ M)
    (hcls4 : ∀ q ∈ S, ‖(cls q).1‖ ≤ 4) (hcls1 : ∀ q ∈ S, ‖(cls q).2‖ = 1)
    (hgeo : ∀ q ∈ S, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (htb1 : ∀ q ∈ S, ‖(tb (cls q)).2‖ = 1)
    (htb : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb (cls q)).1) (tb (cls q)).2| < 9 * ρ ∧
      (dist (cls q).2 (tb (cls q)).2 < ρ ∨ dist (cls q).2 (-(tb (cls q)).2) < ρ)) :
    (Q.card : ℝ) * Nb * (Nb - 2 * Kθ) ≤
      49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2 *
        ((S.image (fun q => tb (cls q))).card : ℝ) ^ 2) := by
  classical
  have hρ : 0 < ρ := lt_of_lt_of_le hr hrρ
  have hδ : 0 < 3 * ρ := by linarith
  have hgap : 0 ≤ Nb - 2 * Kθ := by linarith
  by_cases hQne : Q.Nonempty
  · obtain ⟨P', hP'Q, hP'sep, hcover⟩ := exists_separated_reps Q hδ
    have hP'ne : P'.Nonempty := by
      obtain ⟨q, hq⟩ := hQne
      obtain ⟨p, hp, _⟩ := hcover q hq
      exact ⟨p, hp⟩
    set D' := S.filter (fun q => q.1 ∈ P') with hD'
    have hD'S : D' ⊆ S := Finset.filter_subset _ _
    have hbushD' : ∀ p ∈ P', bushOf D' p = bushOf S p := by
      intro p hp
      ext e
      rw [mem_bushOf, mem_bushOf, hD', Finset.mem_filter]
      exact ⟨fun h => h.1, fun h => ⟨h, hp⟩⟩
    have harcD' : ∀ p ∈ P', ∀ e ∈ bushOf D' p, ((arcNormals ρ D' p e).card : ℝ) ≤ M := by
      intro p hp e he
      have h1 : arcNormals ρ D' p e = arcNormals ρ S p e := by
        unfold arcNormals; rw [hbushD' p hp]
      rw [h1]
      exact harc p (hP'Q hp) e (by rw [← hbushD' p hp]; exact he)
    have hhb := coarse_hairbrush (D' := D') (cls := cls) (tb := tb) hr hrρ hθ₀ hθ₀2 hNb hNb0 hM0
      hP'sep
      (fun q hq => ⟨(Finset.mem_filter.mp hq).2, (hS q (hD'S hq)).2⟩) hP'ne
      (fun p hp => hQ4 p (hP'Q hp))
      (fun p hp => by rw [hbushD' p hp]; exact hbush p (hP'Q hp))
      (fun p hp u hu => by rw [hbushD' p hp]; exact hkθ p (hP'Q hp) u hu)
      harcD'
      (fun q hq => hcls4 q (hD'S hq)) (fun q hq => hcls1 q (hD'S hq))
      (fun q hq => hgeo q (hD'S hq)) (fun q hq => htb1 q (hD'S hq))
      (fun q hq => htb q (hD'S hq))
    have hT : ((D'.image (fun q => tb (cls q))).card : ℝ) ≤
        (S.image (fun q => tb (cls q))).card := by
      exact_mod_cast Finset.card_le_card (Finset.image_subset_image hD'S)
    have hcount := card_le_reps_mul (Q := Q) (P' := P') (δ := 3 * ρ) (B := 49 * n) hcover
      (fun p _ => ball_le_cells hρ hn hcell)
    have hP'c : (0 : ℝ) ≤ P'.card := by positivity
    have hT0 : (0 : ℝ) ≤ (D'.image (fun q => tb (cls q))).card := by positivity
    have hC0 : (0 : ℝ) ≤ 4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2 := by
      have : 0 < θ₀ := by linarith
      positivity
    calc (Q.card : ℝ) * Nb * (Nb - 2 * Kθ) ≤ (P'.card * (49 * n)) * Nb * (Nb - 2 * Kθ) := by
          apply mul_le_mul_of_nonneg_right _ hgap
          exact mul_le_mul_of_nonneg_right hcount hNb0.le
      _ = 49 * n * ((P'.card : ℝ) * Nb * (Nb - 2 * Kθ)) := by ring
      _ ≤ 49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2 *
            ((D'.image (fun q => tb (cls q))).card : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left hhb (by positivity)
      _ ≤ 49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2 *
            ((S.image (fun q => tb (cls q))).card : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ hC0
          exact pow_le_pow_left₀ hT0 hT 2
  · rw [Finset.not_nonempty_iff_eq_empty] at hQne
    rw [hQne, Finset.card_empty, Nat.cast_zero, zero_mul, zero_mul]
    have : 0 < θ₀ := by linarith
    positivity

/-- Two labels of one pin with normals at most `2 ρ` apart have `(36 ρ, 4 ρ)`-close lines
(for `10 r ≤ ρ`). -/
theorem lines_close_same_arc {r ρ : ℝ} (hrρ : 10 * r ≤ ρ) {p e e' : E2} {ℓ ℓ' : E2 × E2}
    (hp4 : ‖p‖ ≤ 4) (hℓ4 : ‖ℓ.1‖ ≤ 4)
    (hg : |inner ℝ (p - ℓ.1) ℓ.2| < 9 * r ∧ (dist e ℓ.2 < r ∨ dist e (-ℓ.2) < r))
    (hg' : |inner ℝ (p - ℓ'.1) ℓ'.2| < 9 * r ∧ (dist e' ℓ'.2 < r ∨ dist e' (-ℓ'.2) < r))
    (hee' : dist e e' ≤ 2 * ρ) (hr : 0 < r) :
    |inner ℝ (ℓ.1 - ℓ'.1) ℓ'.2| < 9 * (4 * ρ) ∧
      (dist ℓ.2 ℓ'.2 < 4 * ρ ∨ dist ℓ.2 (-ℓ'.2) < 4 * ρ) := by
  have h1 : dist ℓ.2 e < r ∨ dist ℓ.2 (-e) < r := normal_close_symm hg.2
  have h2 : dist e e' < 2 * ρ + r ∨ dist e (-e') < 2 * ρ + r := Or.inl (by linarith)
  have h12 := normal_close_trans h1 h2
  have h123 := normal_close_trans h12 hg'.2
  -- the normals of the two lines are within `3 r + 2 ρ`
  have hn : dist ℓ.2 ℓ'.2 < 3 * r + 2 * ρ ∨ dist ℓ.2 (-ℓ'.2) < 3 * r + 2 * ρ := by
    rcases h123 with h | h
    · left; linarith
    · right; linarith
  refine ⟨?_, ?_⟩
  · have hv : ‖ℓ.1 - p‖ ≤ 8 := by
      calc ‖ℓ.1 - p‖ ≤ ‖ℓ.1‖ + ‖p‖ := norm_sub_le _ _
        _ ≤ 8 := by linarith
    have hA : |inner ℝ (ℓ.1 - p) ℓ.2| < 9 * r := by
      rw [show ℓ.1 - p = -(p - ℓ.1) by abel, inner_neg_left, abs_neg]; exact hg.1
    have hn' : dist ℓ'.2 ℓ.2 < 3 * r + 2 * ρ ∨ dist ℓ'.2 (-ℓ.2) < 3 * r + 2 * ρ :=
      normal_close_symm hn
    have hb := inner_le_of_close hv hA hn'
    have hsplit : inner ℝ (ℓ.1 - ℓ'.1) ℓ'.2 = inner ℝ (ℓ.1 - p) ℓ'.2 + inner ℝ (p - ℓ'.1) ℓ'.2 := by
      rw [← inner_add_left]; congr 1; abel
    rw [hsplit]
    calc |inner ℝ (ℓ.1 - p) ℓ'.2 + inner ℝ (p - ℓ'.1) ℓ'.2|
        ≤ |inner ℝ (ℓ.1 - p) ℓ'.2| + |inner ℝ (p - ℓ'.1) ℓ'.2| := abs_add_le _ _
      _ < (9 * r + 8 * (3 * r + 2 * ρ)) + 9 * r := by linarith [hg'.1]
      _ ≤ 9 * (4 * ρ) := by linarith
  · rcases hn with h | h
    · left; linarith
    · right; linarith

/-- The packing constant of `strip_neighbor_count` at the ratio `142`. -/
noncomputable def arcTubeConst : ℝ := 2 * (64 * 142 + 2) * (36 * 142 + 2)

/-- **Tubes of a pin versus its arcs.** The labels of one pin with normals in one `ρ`-arc have
`(36 ρ, 4 ρ)`-close lines (`lines_close_same_arc`), hence coarse tubes that are not
`StripSep (142 ρ)`-separated (`tubes_close_of_lines_close`); a `StripSep ρ` family has at
most `arcTubeConst` such tubes (`strip_neighbor_count`). So a pin meets at most
`arcTubeConst` tubes per occupied arc. -/
theorem pinTubes_le_arcs {r ρ : ℝ} (hr : 0 < r) (hrρ : 10 * r ≤ ρ) (hρ2 : 142 * ρ ≤ 1 / 2)
    {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2} {p : E2} (hp4 : ‖p‖ ≤ 4)
    (hcls4 : ∀ q ∈ S, ‖(cls q).1‖ ≤ 4)
    (hgeo : ∀ q ∈ S, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (htb4 : ∀ q ∈ S, ‖(tb (cls q)).1‖ ≤ 4 ∧ ‖(tb (cls q)).2‖ = 1)
    (htb : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb (cls q)).1) (tb (cls q)).2| < 9 * ρ ∧
      (dist (cls q).2 (tb (cls q)).2 < ρ ∨ dist (cls q).2 (-(tb (cls q)).2) < ρ))
    (hsep : ∀ x ∈ S.image (fun a => tb (cls a)), ∀ y ∈ S.image (fun a => tb (cls a)), x ≠ y →
      StripSep ρ x y) :
    ((pinTubes S cls tb p).card : ℝ) ≤ arcTubeConst * ((bushOf S p).image (arcOf ρ)).card := by
  classical
  have hρ : 0 < ρ := by linarith
  set J := S.image (fun a => tb (cls a)) with hJ
  have hJ4 : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1 := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact htb4 q hq
  have hJsep : (J : Set (E2 × E2)).Pairwise (StripSep ρ) := by
    intro x hx y hy hxy
    exact hsep x (by simpa using hx) y (by simpa using hy) hxy
  set arcs := (bushOf S p).image (arcOf ρ) with harcs
  set tubesOfArc : ℤ × ℤ → Finset (E2 × E2) := fun a =>
    (S.filter (fun q => q.1 = p ∧ arcOf ρ q.2 = a)).image (fun q => tb (cls q)) with htoa
  have hsub : pinTubes S cls tb p ⊆ arcs.biUnion tubesOfArc := by
    intro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hqS, hqp⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_biUnion.mpr ⟨arcOf ρ q.2, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨q.2, ?_, rfl⟩
      rw [mem_bushOf, ← hqp]
      exact hqS
    · exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hqS, hqp, rfl⟩, rfl⟩
  have hper : ∀ a ∈ arcs, ((tubesOfArc a).card : ℝ) ≤ arcTubeConst := by
    intro a _
    by_cases hne : (S.filter (fun q => q.1 = p ∧ arcOf ρ q.2 = a)).Nonempty
    · obtain ⟨q₀, hq₀⟩ := hne
      obtain ⟨hq₀S, hq₀p, hq₀a⟩ := Finset.mem_filter.mp hq₀
      have hk : tb (cls q₀) ∈ J := Finset.mem_image_of_mem _ hq₀S
      have hsubk : tubesOfArc a ⊆
          J.filter (fun j =>
            ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep (142 * ρ) j (tb (cls q₀)) ∨
            ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep (142 * ρ) (tb (cls q₀)) j) := by
        intro j hj
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
        obtain ⟨hqS, hqp, hqa⟩ := Finset.mem_filter.mp hq
        refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hqS, Or.inl ?_⟩
        have hee : dist q.2 q₀.2 ≤ 2 * ρ := dist_le_of_arcOf_eq hρ (hqa.trans hq₀a.symm)
        have hg : |inner ℝ (p - (cls q).1) (cls q).2| < 9 * r ∧
            (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r) := by
          rw [← hqp]; exact hgeo q hqS
        have hg₀ : |inner ℝ (p - (cls q₀).1) (cls q₀).2| < 9 * r ∧
            (dist q₀.2 (cls q₀).2 < r ∨ dist q₀.2 (-(cls q₀).2) < r) := by
          rw [← hq₀p]; exact hgeo q₀ hq₀S
        have hclose := lines_close_same_arc hrρ hp4 (hcls4 q hqS) hg hg₀ hee hr
        have hnot := tubes_close_of_lines_close (hcls4 q hqS) (hcls4 q₀ hq₀S)
          (htb4 q hqS).1 (htb4 q₀ hq₀S).1 hclose (htb q hqS) (htb q₀ hq₀S)
        have h142 : 25 * (4 * ρ) + 42 * ρ = 142 * ρ := by ring
        rw [h142] at hnot
        exact hnot
      have hcount := strip_neighbor_count hρ (by linarith : 0 < 142 * ρ) hρ2 J hJ4 hJsep hk
      have hr64 : 64 * (142 * ρ) / ρ = 64 * 142 := by field_simp
      have hr36 : 36 * (142 * ρ) / ρ = 36 * 142 := by field_simp
      rw [hr64, hr36] at hcount
      calc ((tubesOfArc a).card : ℝ) ≤ (J.filter (fun j =>
            ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep (142 * ρ) j (tb (cls q₀)) ∨
            ¬ WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs.StripSep (142 * ρ) (tb (cls q₀)) j)).card := by
            exact_mod_cast Finset.card_le_card hsubk
        _ ≤ arcTubeConst := by rw [arcTubeConst]; linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have : tubesOfArc a = ∅ := by
        simp only [htoa, hne, Finset.image_empty]
      rw [this, Finset.card_empty, Nat.cast_zero, arcTubeConst]
      norm_num
  calc ((pinTubes S cls tb p).card : ℝ) ≤ (arcs.biUnion tubesOfArc).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ a ∈ arcs, ((tubesOfArc a).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ arcs, arcTubeConst := Finset.sum_le_sum hper
    _ = arcTubeConst * arcs.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- A bush holds at least `(#arcs) · μ` normals if every occupied arc holds at least `μ`. -/
theorem arcs_mul_le_bush {ρ μ : ℝ} {S : Finset (E2 × E2)} {p : E2}
    (hμ : ∀ e ∈ bushOf S p, μ ≤ ((arcNormals ρ S p e).card : ℝ)) :
    (((bushOf S p).image (arcOf ρ)).card : ℝ) * μ ≤ (bushOf S p).card := by
  classical
  have hsum := Finset.card_eq_sum_card_image (arcOf ρ) (bushOf S p)
  have hfib : ∀ a ∈ (bushOf S p).image (arcOf ρ),
      μ ≤ (((bushOf S p).filter (fun e => arcOf ρ e = a)).card : ℝ) := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    exact hμ e he
  calc (((bushOf S p).image (arcOf ρ)).card : ℝ) * μ = ∑ _a ∈ (bushOf S p).image (arcOf ρ), μ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ a ∈ (bushOf S p).image (arcOf ρ),
          (((bushOf S p).filter (fun e => arcOf ρ e = a)).card : ℝ) := Finset.sum_le_sum hfib
    _ = (bushOf S p).card := by exact_mod_cast hsum.symm

/-- **The Wolff leaf, in counts.** Data at the coarse scale `ρ`: at most `n` pins per
`ρ`-cell, bushes of at least `Nb` normals with `θ₀`-caps at most `Kθ`, between `M / K` and
`M` normals per occupied (pin, arc), lines `cls` and coarse tubes `tb` with their geometry,
labels per (pin, tube) balanced with ratio `K`, and the quadratic bound
`(labels per (pin, tube))² ≤ C_q #(lines in the tube)` (x0675's `tube_quadratic_of_fail`).
Then
`|Q| Nb (Nb - 2 Kθ) M² ≤ 49 n · 4 · 49² (900/θ₀ + 3)² C_q² K⁸ arcTubeConst⁴ #lines²`,
i.e. `#cells(ρ) ≲ (#lines / (Nb M))²`: the coarse Wolff constraint `G(a) ≤ 2 F(a) + O(ε)`. -/
theorem wolff_leaf_count {r ρ θ₀ Nb Kθ M n K Cq : ℝ} (hr : 0 < r) (hrρ : 10 * r ≤ ρ)
    (hρ2 : 142 * ρ ≤ 1 / 2) (hθ₀ : 6 * ρ ≤ θ₀) (hθ₀2 : θ₀ ≤ 2) (hNb : 2 * Kθ ≤ Nb)
    (hNb0 : 0 < Nb) (hM0 : 0 < M) (hn : 0 ≤ n) (hK : 0 < K) (hCq : 0 ≤ Cq)
    {Q : Finset E2} {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2}
    (hS : ∀ q ∈ S, q.1 ∈ Q ∧ ‖q.2‖ = 1) (hQ4 : ∀ p ∈ Q, ‖p‖ ≤ 4)
    (hcell : ∀ q ∈ Q, ((cellPins ρ Q q).card : ℝ) ≤ n)
    (hbush : ∀ p ∈ Q, Nb ≤ ((bushOf S p).card : ℝ))
    (hkθ : ∀ p ∈ Q, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf S p).filter (fun e => dist e u ≤ θ₀)).card : ℝ) ≤ Kθ)
    (harc : ∀ p ∈ Q, ∀ e ∈ bushOf S p, ((arcNormals ρ S p e).card : ℝ) ≤ M)
    (harcmin : ∀ p ∈ Q, ∀ e ∈ bushOf S p, M ≤ K * ((arcNormals ρ S p e).card : ℝ))
    (hcls4 : ∀ q ∈ S, ‖(cls q).1‖ ≤ 4) (hcls1 : ∀ q ∈ S, ‖(cls q).2‖ = 1)
    (hgeo : ∀ q ∈ S, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (htb4 : ∀ q ∈ S, ‖(tb (cls q)).1‖ ≤ 4 ∧ ‖(tb (cls q)).2‖ = 1)
    (htb : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb (cls q)).1) (tb (cls q)).2| < 9 * ρ ∧
      (dist (cls q).2 (tb (cls q)).2 < ρ ∨ dist (cls q).2 (-(tb (cls q)).2) < ρ))
    (hsep : ∀ x ∈ S.image (fun a => tb (cls a)), ∀ y ∈ S.image (fun a => tb (cls a)), x ≠ y →
      StripSep ρ x y)
    (hbal : WangZahlLot.Obl.wz_tower_balanced_refinement.Balanced S
      (fun q => (q.1, tb (cls q))) K)
    (hquad : ∀ q₀ ∈ S,
      ((S.filter (fun q => q.1 = q₀.1 ∧ tb (cls q) = tb (cls q₀))).card : ℝ) ^ 2 ≤
        Cq * ((S.filter (fun q => tb (cls q) = tb (cls q₀))).image cls).card) :
    (Q.card : ℝ) * Nb * (Nb - 2 * Kθ) * M ^ 2 ≤
      49 * n * (4 * 49 ^ 2 * (900 / θ₀ + 3) ^ 2) * Cq ^ 2 * K ^ 8 * arcTubeConst ^ 4 *
        ((S.image cls).card : ℝ) ^ 2 := by
  classical
  have hρ : 0 < ρ := by linarith
  have hθ₀pos : 0 < θ₀ := by linarith
  have hgap : 0 ≤ Nb - 2 * Kθ := by linarith
  have hCp : 0 < arcTubeConst := by rw [arcTubeConst]; norm_num
  set T : ℝ := ((S.image (fun q => tb (cls q))).card : ℝ) with hT
  set L : ℝ := ((S.image cls).card : ℝ) with hL
  set m₁ : ℝ := M / (K ^ 2 * arcTubeConst) with hm₁
  have hm₁pos : 0 < m₁ := by positivity
  -- step 1: the hairbrush at the coarse scale
  have h1 := coarse_wolff hr (by linarith) hθ₀ hθ₀2 hNb hNb0 hM0.le hn hS hQ4 hcell hbush hkθ
    harc hcls4 hcls1 hgeo (fun q hq => (htb4 q hq).2) htb
  -- step 2: every (pin, tube) holds at least `m₁` labels
  have h2 : ∀ q ∈ S, m₁ ≤ ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) := by
    intro q hq
    have hqQ := (hS q hq).1
    have hsh := shared_tubes_pin hbal hq
    have hpt := pinTubes_le_arcs (p := q.1) hr hrρ hρ2 (hQ4 _ hqQ) hcls4 hgeo htb4 htb hsep
    have hμ : ∀ e ∈ bushOf S q.1, M / K ≤ ((arcNormals ρ S q.1 e).card : ℝ) := by
      intro e he
      rw [div_le_iff₀ hK]
      linarith [harcmin q.1 hqQ e he]
    have hab := arcs_mul_le_bush hμ
    set A : ℝ := (((bushOf S q.1).image (arcOf ρ)).card : ℝ) with hA
    set mq : ℝ := ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) with hmq
    have hApos : 0 < A := by
      have hmem : q.2 ∈ bushOf S q.1 := by rw [mem_bushOf]; exact hq
      have : ((bushOf S q.1).image (arcOf ρ)).Nonempty := ⟨_, Finset.mem_image_of_mem _ hmem⟩
      rw [hA]; exact_mod_cast Finset.card_pos.mpr this
    have hmq0 : 0 ≤ mq := by positivity
    -- A (M/K) ≤ |bush| ≤ #pinTubes K mq ≤ arcTubeConst A K mq
    have hchain : A * (M / K) ≤ arcTubeConst * A * (K * mq) := by
      calc A * (M / K) ≤ (bushOf S q.1).card := hab
        _ ≤ (pinTubes S cls tb q.1).card * (K * mq) := hsh
        _ ≤ (arcTubeConst * A) * (K * mq) := by
            apply mul_le_mul_of_nonneg_right hpt (by positivity)
        _ = arcTubeConst * A * (K * mq) := by ring
    have hchain' : M / K ≤ arcTubeConst * (K * mq) := by
      have := hchain
      have h' : A * (M / K) ≤ A * (arcTubeConst * (K * mq)) := by linarith
      exact le_of_mul_le_mul_left h' hApos
    rw [hm₁, div_le_iff₀ (by positivity)]
    have : M ≤ K * (arcTubeConst * (K * mq)) := by
      rw [div_le_iff₀ hK] at hchain'; linarith
    nlinarith
  -- step 3: the tube count
  have h3 : T * m₁ ^ 2 ≤ Cq * L := by
    have := tube_count (S := S) (cls := cls) (tb := tb) (C := Cq) (m := m₁) hCq (fun q₀ hq₀ => by
      have hle := h2 q₀ hq₀
      have hsq : m₁ ^ 2 ≤ ((S.filter (fun a => a.1 = q₀.1 ∧ tb (cls a) = tb (cls q₀))).card : ℝ) ^ 2 :=
        pow_le_pow_left₀ hm₁pos.le hle 2
      exact hsq.trans (hquad q₀ hq₀))
    have hsub : S.image cls ⊆ S.image cls := le_rfl
    simpa [hT, hL] using this
  -- step 4: combine
  have hT0 : 0 ≤ T := by positivity
  have hTle : T ≤ Cq * L / m₁ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; exact h3
  have hTsq : T ^ 2 ≤ (Cq * L / m₁ ^ 2) ^ 2 := pow_le_pow_left₀ hT0 hTle 2
  have hC0 : 0 ≤ 49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2) := by positivity
  have h4 : (Q.card : ℝ) * Nb * (Nb - 2 * Kθ) ≤
      49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2) * (Cq * L / m₁ ^ 2) ^ 2 := by
    calc (Q.card : ℝ) * Nb * (Nb - 2 * Kθ)
        ≤ 49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2 * T ^ 2) := h1
      _ = 49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2) * T ^ 2 := by ring
      _ ≤ 49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2) * (Cq * L / m₁ ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hTsq hC0
  have hid : 49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2) * (Cq * L / m₁ ^ 2) ^ 2 * M ^ 2 =
      49 * n * (4 * 49 ^ 2 * (900 / θ₀ + 3) ^ 2) * Cq ^ 2 * K ^ 8 * arcTubeConst ^ 4 * L ^ 2 := by
    rw [hm₁]
    field_simp
  calc (Q.card : ℝ) * Nb * (Nb - 2 * Kθ) * M ^ 2
      ≤ 49 * n * (4 * (49 * M) ^ 2 * (900 / θ₀ + 3) ^ 2) * (Cq * L / m₁ ^ 2) ^ 2 * M ^ 2 :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = _ := hid

/-- **Geometry of the composed class map.** A label within `9 r` / `r` of its line, a line
within `9 ρ` / `ρ` of its coarse tube: the label is within `9 (3 ρ)` / `3 ρ` of the tube
(`r ≤ ρ`). -/
theorem coarse_cls_geom {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r ≤ ρ) {q ℓ j : E2 × E2}
    (hq4 : ‖q.1‖ ≤ 4) (hℓ4 : ‖ℓ.1‖ ≤ 4) (hℓ1 : ‖ℓ.2‖ = 1) (hj1 : ‖j.2‖ = 1)
    (hgeo : |inner ℝ (q.1 - ℓ.1) ℓ.2| < 9 * r ∧ (dist q.2 ℓ.2 < r ∨ dist q.2 (-ℓ.2) < r))
    (htb : |inner ℝ (ℓ.1 - j.1) j.2| < 9 * ρ ∧ (dist ℓ.2 j.2 < ρ ∨ dist ℓ.2 (-j.2) < ρ)) :
    |inner ℝ (q.1 - j.1) j.2| < 9 * (3 * ρ) ∧ (dist q.2 j.2 < 3 * ρ ∨ dist q.2 (-j.2) < 3 * ρ) := by
  have hpin := pin_near_tube hq4 hℓ4 hℓ1 hj1 hgeo.1 htb.1 htb.2
  have hn := normal_close_trans hgeo.2 htb.2
  refine ⟨by linarith, ?_⟩
  rcases hn with hn | hn
  · left; linarith
  · right; linarith

/-- **Every (pin, coarse tube) holds at least `M / (K² arcTubeConst)` labels** when the labels
per (pin, tube) are balanced with ratio `K` and the normals per occupied (pin, `ρ`-arc) lie
in `[M / K, M]`. -/
theorem pin_tube_labels_ge {r ρ M K : ℝ} (hr : 0 < r) (hrρ : 10 * r ≤ ρ)
    (hρ2 : 142 * ρ ≤ 1 / 2) (hK : 0 < K)
    {Q : Finset E2} {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2}
    (hS : ∀ q ∈ S, q.1 ∈ Q ∧ ‖q.2‖ = 1) (hQ4 : ∀ p ∈ Q, ‖p‖ ≤ 4)
    (harcmin : ∀ p ∈ Q, ∀ e ∈ bushOf S p, M ≤ K * ((arcNormals ρ S p e).card : ℝ))
    (hcls4 : ∀ q ∈ S, ‖(cls q).1‖ ≤ 4)
    (hgeo : ∀ q ∈ S, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * r ∧
      (dist q.2 (cls q).2 < r ∨ dist q.2 (-(cls q).2) < r))
    (htb4 : ∀ q ∈ S, ‖(tb (cls q)).1‖ ≤ 4 ∧ ‖(tb (cls q)).2‖ = 1)
    (htb : ∀ q ∈ S, |inner ℝ ((cls q).1 - (tb (cls q)).1) (tb (cls q)).2| < 9 * ρ ∧
      (dist (cls q).2 (tb (cls q)).2 < ρ ∨ dist (cls q).2 (-(tb (cls q)).2) < ρ))
    (hsep : ∀ x ∈ S.image (fun a => tb (cls a)), ∀ y ∈ S.image (fun a => tb (cls a)), x ≠ y →
      StripSep ρ x y)
    (hbal : WangZahlLot.Obl.wz_tower_balanced_refinement.Balanced S
      (fun q => (q.1, tb (cls q))) K)
    {q : E2 × E2} (hq : q ∈ S) :
    M / (K ^ 2 * arcTubeConst) ≤
      ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) := by
  classical
  have hCp : 0 < arcTubeConst := by rw [arcTubeConst]; norm_num
  have hqQ := (hS q hq).1
  have hsh := shared_tubes_pin hbal hq
  have hpt := pinTubes_le_arcs (p := q.1) hr hrρ hρ2 (hQ4 _ hqQ) hcls4 hgeo htb4 htb hsep
  have hμ : ∀ e ∈ bushOf S q.1, M / K ≤ ((arcNormals ρ S q.1 e).card : ℝ) := by
    intro e he
    rw [div_le_iff₀ hK]
    linarith [harcmin q.1 hqQ e he]
  have hab := arcs_mul_le_bush hμ
  set A : ℝ := (((bushOf S q.1).image (arcOf ρ)).card : ℝ) with hA
  set mq : ℝ := ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ) with hmq
  have hApos : 0 < A := by
    have hmem : q.2 ∈ bushOf S q.1 := by rw [mem_bushOf]; exact hq
    have : ((bushOf S q.1).image (arcOf ρ)).Nonempty := ⟨_, Finset.mem_image_of_mem _ hmem⟩
    rw [hA]; exact_mod_cast Finset.card_pos.mpr this
  have hmq0 : 0 ≤ mq := by positivity
  have hchain : A * (M / K) ≤ A * (arcTubeConst * (K * mq)) := by
    calc A * (M / K) ≤ (bushOf S q.1).card := hab
      _ ≤ (pinTubes S cls tb q.1).card * (K * mq) := hsh
      _ ≤ (arcTubeConst * A) * (K * mq) := by
          apply mul_le_mul_of_nonneg_right hpt (by positivity)
      _ = A * (arcTubeConst * (K * mq)) := by ring
  have hchain' : M / K ≤ arcTubeConst * (K * mq) := le_of_mul_le_mul_left hchain hApos
  rw [div_le_iff₀ (by positivity)]
  have : M ≤ K * (arcTubeConst * (K * mq)) := by
    rw [div_le_iff₀ hK] at hchain'; linarith
  nlinarith

/-- **Number of occupied coarse tubes.** With the quadratic bound
`(labels per (pin, tube))² ≤ C_q #(lines in the tube)` at every label and the lower bound
`pin_tube_labels_ge`: `#tubes · (M / (K² arcTubeConst))² ≤ C_q #lines`. -/
theorem coarse_lines_count {m₁ Cq : ℝ} (hm₁ : 0 ≤ m₁) (hCq : 0 ≤ Cq)
    {S : Finset (E2 × E2)} {cls tb : E2 × E2 → E2 × E2}
    (hlow : ∀ q ∈ S, m₁ ≤ ((S.filter (fun a => a.1 = q.1 ∧ tb (cls a) = tb (cls q))).card : ℝ))
    (hquad : ∀ q₀ ∈ S,
      ((S.filter (fun q => q.1 = q₀.1 ∧ tb (cls q) = tb (cls q₀))).card : ℝ) ^ 2 ≤
        Cq * ((S.filter (fun q => tb (cls q) = tb (cls q₀))).image cls).card) :
    ((S.image (fun q => tb (cls q))).card : ℝ) * m₁ ^ 2 ≤ Cq * (S.image cls).card :=
  tube_count (S := S) (cls := cls) (tb := tb) (C := Cq) (m := m₁) hCq (fun q₀ hq₀ =>
    (pow_le_pow_left₀ hm₁ (hlow q₀ hq₀) 2).trans (hquad q₀ hq₀))

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
