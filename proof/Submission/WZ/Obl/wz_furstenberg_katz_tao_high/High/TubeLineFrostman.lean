-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.TubeLineFrostman.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/TubeLineFrostman.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.TubeTransfer
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeUpper
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CoarseTubeCounts

/-!
# Tube-line Frostman in tube coordinates (input of `coarse_tube_false`)

`coarse_tube_false` (x0665, ported under `O214/`) needs the lines `J` of one coarse tube to be
`(1 + b)`-Frostman in the tube coordinates `tubeLine v c_T a_T λ`:
`#{j ∈ J : tubeLine j in a ρ-square} ≤ K₀ ρ ^ (1 + b) #J` for `ρ ≥ δ`.

* `tubeLine_square_close`: two labels with transverse normals (`1/2 ≤ |⟨e, v^⊥⟩|`) whose tube
  lines lie in one `ρ`-square are `(9 W, W)`-close with `W = 5 λ ρ`
  (`chart_offset_bound`, `normal_distance_of_slope`).
* `tubeLine_frostman_of_close`: hence the chart Frostman bound follows from the same bound for
  the `(9 (5 λ ρ), 5 λ ρ)`-neighbourhoods of the members of `J`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

/-- **Chart squares are closeness balls.** Labels with unit, transverse normals whose tube
lines lie in a common `ρ`-square are `(9 W, W)`-close, `W = 5 λ ρ`. -/
theorem tubeLine_square_close {v : Plane} (hv : ‖v‖ = 1) {cT aT lam ρ c a : ℝ}
    (hlam : 0 < lam) (hρ : 0 < ρ) {j j₀ : Plane × Plane}
    (hj1 : ‖j.2‖ = 1) (hj₀1 : ‖j₀.2‖ = 1) (hj4 : ‖j.1‖ ≤ 4)
    (hjt : 1 / 2 ≤ |inner ℝ j.2 (perp v)|) (hj₀t : 1 / 2 ≤ |inner ℝ j₀.2 (perp v)|)
    (hsq : |(tubeLine v cT aT lam j).1 - c| ≤ ρ ∧ |(tubeLine v cT aT lam j).2 - a| ≤ ρ)
    (hsq₀ : |(tubeLine v cT aT lam j₀).1 - c| ≤ ρ ∧ |(tubeLine v cT aT lam j₀).2 - a| ≤ ρ) :
    |inner ℝ (j.1 - j₀.1) j₀.2| < 9 * (5 * lam * ρ) ∧
      (dist j.2 j₀.2 < 5 * lam * ρ ∨ dist j.2 (-j₀.2) < 5 * lam * ρ) := by
  -- chart differences
  have hcot : |(lineChart v j).1 - (lineChart v j₀).1| ≤ 2 * lam * ρ := by
    have e : (lineChart v j).1 - (lineChart v j₀).1 =
        lam * ((tubeLine v cT aT lam j).1 - (tubeLine v cT aT lam j₀).1) := by
      simp only [tubeLine]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hlam]
    have : |(tubeLine v cT aT lam j).1 - (tubeLine v cT aT lam j₀).1| ≤ 2 * ρ := by
      calc |(tubeLine v cT aT lam j).1 - (tubeLine v cT aT lam j₀).1|
          ≤ |(tubeLine v cT aT lam j).1 - c| + |c - (tubeLine v cT aT lam j₀).1| :=
            abs_sub_le _ _ _
        _ ≤ ρ + ρ := by rw [abs_sub_comm c]; linarith [hsq.1, hsq₀.1]
        _ = 2 * ρ := by ring
    nlinarith
  have hint : |(lineChart v j₀).2 - (lineChart v j).2| ≤ 2 * lam * ρ := by
    have e : (lineChart v j₀).2 - (lineChart v j).2 =
        lam * ((tubeLine v cT aT lam j₀).2 - (tubeLine v cT aT lam j).2) := by
      simp only [tubeLine]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hlam]
    have : |(tubeLine v cT aT lam j₀).2 - (tubeLine v cT aT lam j).2| ≤ 2 * ρ := by
      calc |(tubeLine v cT aT lam j₀).2 - (tubeLine v cT aT lam j).2|
          ≤ |(tubeLine v cT aT lam j₀).2 - a| + |a - (tubeLine v cT aT lam j).2| :=
            abs_sub_le _ _ _
        _ ≤ ρ + ρ := by rw [abs_sub_comm a]; linarith [hsq.2, hsq₀.2]
        _ = 2 * ρ := by ring
    nlinarith
  have hcot' : |(lineChart v j₀).1 - (lineChart v j).1| ≤ 2 * lam * ρ := by
    rw [abs_sub_comm]; exact hcot
  have hne₀ : inner ℝ j₀.2 (perp v) ≠ 0 := by
    intro h; rw [h, abs_zero] at hj₀t; norm_num at hj₀t
  have hpos : 0 < lam * ρ := mul_pos hlam hρ
  refine ⟨?_, ?_⟩
  · -- the offset, measured with the normal of `j₀`
    have hb := chart_offset_bound (p := j₀.1) (p' := j.1) (e := j₀.2) (e' := j.2) hv hj₀1 hne₀ hj4
    have hpair₀ : (j₀.1, j₀.2) = j₀ := rfl
    have hpair : (j.1, j.2) = j := rfl
    rw [hpair₀, hpair] at hb
    have hflip : inner ℝ (j.1 - j₀.1) j₀.2 = -inner ℝ (j₀.1 - j.1) j₀.2 := by
      rw [← inner_neg_left, neg_sub]
    rw [hflip, abs_neg]
    calc |inner ℝ (j₀.1 - j.1) j₀.2|
        ≤ |(lineChart v j₀).2 - (lineChart v j).2| +
            4 * |(lineChart v j₀).1 - (lineChart v j).1| := hb
      _ ≤ 2 * lam * ρ + 4 * (2 * lam * ρ) := by linarith
      _ < 9 * (5 * lam * ρ) := by nlinarith
  · have hd := normal_distance_of_slope hv hj1 hj₀1 (by norm_num : (0 : ℝ) < 1 / 2) hjt hj₀t
    have hcotN : |cotNormal v j.2 - cotNormal v j₀.2| ≤ 2 * lam * ρ := by
      simpa [lineChart] using hcot
    rcases hd with hd | hd
    · left; linarith
    · right; linarith

/-- **Chart Frostman from closeness counts.** If every member of `J` has at most
`K₀ ρ ^ β #J` members of `J` in its `(9 (5 λ ρ), 5 λ ρ)`-neighbourhood (for `ρ ≥ δ`), then
every `ρ`-square of the tube chart holds at most `K₀ ρ ^ β #J` tube lines of `J`. -/
theorem tubeLine_frostman_of_close {v : Plane} (hv : ‖v‖ = 1) {cT aT lam δ K₀ β : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) {J : Finset (Plane × Plane)}
    (hJ : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)|)
    (hclose : ∀ j₀ ∈ J, ∀ ρ : ℝ, δ ≤ ρ →
      ((J.filter (fun j => |inner ℝ (j.1 - j₀.1) j₀.2| < 9 * (5 * lam * ρ) ∧
        (dist j.2 j₀.2 < 5 * lam * ρ ∨ dist j.2 (-j₀.2) < 5 * lam * ρ))).card : ℝ) ≤
        K₀ * ρ ^ β * J.card)
    (hK₀ : 0 ≤ K₀) :
    ∀ c a ρ : ℝ, δ ≤ ρ →
      ((J.filter (fun j => |(tubeLine v cT aT lam j).1 - c| ≤ ρ ∧
        |(tubeLine v cT aT lam j).2 - a| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ β * J.card := by
  classical
  intro c a ρ hρδ
  have hρ : 0 < ρ := lt_of_lt_of_le hδ hρδ
  set Sq := J.filter (fun j => |(tubeLine v cT aT lam j).1 - c| ≤ ρ ∧
    |(tubeLine v cT aT lam j).2 - a| ≤ ρ) with hSq
  by_cases hne : Sq.Nonempty
  · obtain ⟨j₀, hj₀⟩ := hne
    obtain ⟨hj₀J, hj₀sq⟩ := Finset.mem_filter.mp hj₀
    obtain ⟨hj₀1, -, hj₀t⟩ := hJ j₀ hj₀J
    have hsub : Sq ⊆ J.filter (fun j => |inner ℝ (j.1 - j₀.1) j₀.2| < 9 * (5 * lam * ρ) ∧
        (dist j.2 j₀.2 < 5 * lam * ρ ∨ dist j.2 (-j₀.2) < 5 * lam * ρ)) := by
      intro j hj
      obtain ⟨hjJ, hjsq⟩ := Finset.mem_filter.mp hj
      obtain ⟨hj1, hj4, hjt⟩ := hJ j hjJ
      exact Finset.mem_filter.mpr ⟨hjJ,
        tubeLine_square_close hv hlam hρ hj1 hj₀1 hj4 hjt hj₀t hjsq hj₀sq⟩
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (hclose j₀ hj₀J ρ hρδ)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty, Nat.cast_zero]
    positivity

/-- The members of a finset of lines whose tube lines lie in a `ρ`-square are, if there is one
such member `j₀`, among the `(9 (5 λ ρ), 5 λ ρ)`-neighbours of `j₀`. -/
theorem square_subset_close {v : Plane} (hv : ‖v‖ = 1) {cT aT lam ρ c a : ℝ}
    (hlam : 0 < lam) (hρ : 0 < ρ) {J : Finset (Plane × Plane)}
    (hJ : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)|)
    {j₀ : Plane × Plane} (hj₀ : j₀ ∈ J)
    (hj₀sq : |(tubeLine v cT aT lam j₀).1 - c| ≤ ρ ∧ |(tubeLine v cT aT lam j₀).2 - a| ≤ ρ) :
    J.filter (fun j => |(tubeLine v cT aT lam j).1 - c| ≤ ρ ∧
        |(tubeLine v cT aT lam j).2 - a| ≤ ρ) ⊆
      J.filter (fun j => |inner ℝ (j.1 - j₀.1) j₀.2| < 9 * (5 * lam * ρ) ∧
        (dist j.2 j₀.2 < 5 * lam * ρ ∨ dist j.2 (-j₀.2) < 5 * lam * ρ)) := by
  intro j hj
  obtain ⟨hjJ, hjsq⟩ := Finset.mem_filter.mp hj
  obtain ⟨hj1, hj4, hjt⟩ := hJ j hjJ
  obtain ⟨hj₀1, -, hj₀t⟩ := hJ j₀ hj₀
  exact Finset.mem_filter.mpr ⟨hjJ,
    tubeLine_square_close hv hlam hρ hj1 hj₀1 hj4 hjt hj₀t hjsq hj₀sq⟩

/-- **Chart squares of a coarse tube, counted through labels.** `J(T)` = the `δ`-tubes (`tbA`)
of the labels of the `ρ`-tube `T` (`tbH`); `tbI` a family at the scale `w ≥ 5 λ ρ'`. Then every
`ρ'`-square of the chart of `(v, c_T, a_T, λ)` holds `#J(T)`-proportionally few members:
`#square · (L_min,a · L_T) ≤ nearTubeConst² · L_max,w · L_max,a · #J(T)`. -/
theorem coarse_square_count {v : Plane} (hv : ‖v‖ = 1) {cT aT lam ρ' c a : ℝ}
    (hlam : 0 < lam) (hρ' : 0 < ρ') {δ w LminA LmaxA LmaxI : ℝ} (hδ : 0 < δ) (hδw : δ ≤ w)
    (hw2 : 67 * w ≤ 1 / 2) (hWw : 5 * lam * ρ' ≤ w) (hLmaxI : 0 ≤ LmaxI)
    (hLminA : 0 ≤ LminA)
    {S J₀ J₁ : Finset (Plane × Plane)} {cls tbA tbI tbH : Plane × Plane → Plane × Plane}
    {T : Plane × Plane}
    (hcls : ∀ q ∈ S, cls q ∈ J₀) (hJ₀4 : ∀ ℓ ∈ J₀, ‖ℓ.1‖ ≤ 4)
    (htbA : ∀ ℓ ∈ J₀, tbA ℓ ∈ J₀)
    (htbAgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tbA ℓ).1) (tbA ℓ).2| < 9 * δ ∧
      (dist ℓ.2 (tbA ℓ).2 < δ ∨ dist ℓ.2 (-(tbA ℓ).2) < δ))
    (htbI : ∀ ℓ ∈ J₀, tbI ℓ ∈ J₁)
    (htbIgeo : ∀ ℓ ∈ J₀, |inner ℝ (ℓ.1 - (tbI ℓ).1) (tbI ℓ).2| < 9 * w ∧
      (dist ℓ.2 (tbI ℓ).2 < w ∨ dist ℓ.2 (-(tbI ℓ).2) < w))
    (hJ₁ : ∀ j ∈ J₁, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hJ₁sep : ∀ x ∈ J₁, ∀ y ∈ J₁, x ≠ y → StripSep w x y)
    (hLminA' : ∀ q ∈ S, LminA ≤ ((S.filter (fun q' => tbA (cls q') = tbA (cls q))).card : ℝ))
    (hLmaxA' : ∀ q ∈ S, ((S.filter (fun q' => tbA (cls q') = tbA (cls q))).card : ℝ) ≤ LmaxA)
    (hLmaxI' : ∀ k' ∈ J₁, ((S.filter (fun q => tbI (cls q) = k')).card : ℝ) ≤ LmaxI)
    (hJt : ∀ j ∈ (S.filter (fun q => tbH (cls q) = T)).image (fun q => tbA (cls q)),
      ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)|) :
    ((((S.filter (fun q => tbH (cls q) = T)).image (fun q => tbA (cls q))).filter
        (fun j => |(tubeLine v cT aT lam j).1 - c| ≤ ρ' ∧
          |(tubeLine v cT aT lam j).2 - a| ≤ ρ')).card : ℝ) *
        (LminA * ((S.filter (fun q => tbH (cls q) = T)).card : ℝ)) ≤
      nearTubeConst ^ 2 * LmaxI * LmaxA *
        (((S.filter (fun q => tbH (cls q) = T)).image (fun q => tbA (cls q))).card : ℝ) := by
  classical
  set J := (S.filter (fun q => tbH (cls q) = T)).image (fun q => tbA (cls q)) with hJ
  set Sq := J.filter (fun j => |(tubeLine v cT aT lam j).1 - c| ≤ ρ' ∧
    |(tubeLine v cT aT lam j).2 - a| ≤ ρ') with hSq
  by_cases hne : Sq.Nonempty
  · obtain ⟨j₀, hj₀⟩ := hne
    obtain ⟨hj₀J, hj₀sq⟩ := Finset.mem_filter.mp hj₀
    have hsub := square_subset_close hv hlam hρ' hJt hj₀J hj₀sq
    have hcc := coarse_close_count (W := 5 * lam * ρ') hδ hδw hw2 (by positivity) hWw hLmaxI
      hLminA hcls hJ₀4 htbA htbAgeo htbI htbIgeo hJ₁ hJ₁sep hLminA' hLmaxA' hLmaxI' hj₀J
    have hle : (Sq.card : ℝ) ≤ ((J.filter (fun j => |inner ℝ (j.1 - j₀.1) j₀.2| <
        9 * (5 * lam * ρ') ∧ (dist j.2 j₀.2 < 5 * lam * ρ' ∨
          dist j.2 (-j₀.2) < 5 * lam * ρ'))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    calc (Sq.card : ℝ) * (LminA * ((S.filter (fun q => tbH (cls q) = T)).card : ℝ))
        ≤ ((J.filter (fun j => |inner ℝ (j.1 - j₀.1) j₀.2| < 9 * (5 * lam * ρ') ∧
            (dist j.2 j₀.2 < 5 * lam * ρ' ∨ dist j.2 (-j₀.2) < 5 * lam * ρ'))).card : ℝ) *
            (LminA * ((S.filter (fun q => tbH (cls q) = T)).card : ℝ)) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hLminA (Nat.cast_nonneg _))
      _ ≤ _ := hcc
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty, Nat.cast_zero, zero_mul]
    by_cases hJne : J.Nonempty
    · obtain ⟨j, hj⟩ := hJne
      obtain ⟨q, hq, -⟩ := Finset.mem_image.mp hj
      have hLmaxA0 : 0 ≤ LmaxA :=
        le_trans (Nat.cast_nonneg _) (hLmaxA' q (Finset.mem_filter.mp hq).1)
      exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg nearTubeConst_pos.le 2) hLmaxI)
        hLmaxA0) (Nat.cast_nonneg _)
    · rw [Finset.not_nonempty_iff_eq_empty] at hJne
      rw [hJne, Finset.card_empty, Nat.cast_zero, mul_zero]

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
