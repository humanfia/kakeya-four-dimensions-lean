-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WindowColumns.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.CaseAObjects
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.GridCounts
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowCells
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.AbstractCaseA
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WindowDensity

/-!
# From cell density to column density in a window tube

For a window tube `T` (x0672's `windowLines`, `windowPins`, `windowPin`, axis `tubeAxis T`,
columns of width `ρ / 2` where `ρ = palScale h`):

* `windowLines_eq_filter`, `windowPin_iff`, `mem_windowPins_iff`, `tubeCells_eq_windowPins`
  identify x0672's window objects with the class/cell objects of `Columns`;
* `line_cells_le_cols`: the pins of one line meet at most `121` times as many `ρ`-cells as
  columns (two pins of a line in one column are `3 ρ + 108 δ ≤ 4 ρ`-close);
* `tube_cols_le_cells`: any pin set meets at most `11` times as many columns as `ρ`-cells;
* `window_column_density_of_cells`: a (line, cell) density `dc` of `T` gives the (column, line)
  density `dc / 1331` in exactly the form of `caseA_window_contradiction`'s `hdens`.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open scoped BigOperators

attribute [local instance 10] Classical.propDecidable

section Objects

variable {S : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2} {tb : ℕ → E2 × E2 → E2 × E2}
  {a h : ℕ}

theorem windowLines_eq_filter (T : E2 × E2) :
    windowLines S cls tb a h T =
      (S.image (fun q => tb a (cls q))).filter (fun j => tb h j = T) := by
  ext j
  simp only [windowLines, windowLabels, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨q, ⟨hq, hqT⟩, rfl⟩; exact ⟨⟨q, hq, rfl⟩, hqT⟩
  · rintro ⟨⟨q, hq, rfl⟩, hqT⟩; exact ⟨q, ⟨hq, hqT⟩, rfl⟩

theorem tb_eq_of_mem_windowLines {T j : E2 × E2} (hj : j ∈ windowLines S cls tb a h T) :
    tb h j = T := by
  rw [windowLines_eq_filter] at hj; exact (Finset.mem_filter.mp hj).2

theorem windowPin_iff {T j : E2 × E2} (hj : j ∈ windowLines S cls tb a h T) {x : E2} :
    windowPin S cls tb a h T j x ↔ x ∈ pinsOf S (fun q => tb a (cls q)) j := by
  have hjT := tb_eq_of_mem_windowLines hj
  constructor
  · rintro ⟨q, hq, rfl, hqj⟩
    exact mem_pinsOf.mpr ⟨q.2, by simpa using (mem_windowLabels.mp hq).1, hqj⟩
  · intro hx
    obtain ⟨e, hxe, hej⟩ := mem_pinsOf.mp hx
    refine ⟨(x, e), mem_windowLabels.mpr ⟨hxe, ?_⟩, rfl, hej⟩
    have hej' : tb a (cls (x, e)) = j := hej
    rw [hej', hjT]

theorem mem_windowPins_iff {T : E2 × E2} {x : E2} :
    x ∈ windowPins S cls tb a h T ↔
      ∃ j ∈ windowLines S cls tb a h T, x ∈ pinsOf S (fun q => tb a (cls q)) j := by
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨tb a (cls q), Finset.mem_image_of_mem _ hq, mem_pinsOf.mpr ⟨q.2, ?_, rfl⟩⟩
    simpa using (mem_windowLabels.mp hq).1
  · rintro ⟨j, hj, hx⟩
    obtain ⟨e, hxe, hej⟩ := mem_pinsOf.mp hx
    have hjT := tb_eq_of_mem_windowLines hj
    have hej' : tb a (cls (x, e)) = j := hej
    exact Finset.mem_image.mpr ⟨(x, e), mem_windowLabels.mpr ⟨hxe, by rw [hej', hjT]⟩, rfl⟩

theorem pins_subset_image_fst {j : E2 × E2} :
    pinsOf S (fun q => tb a (cls q)) j ⊆ S.image Prod.fst := by
  intro x hx
  obtain ⟨e, hxe, -⟩ := mem_pinsOf.mp hx
  exact Finset.mem_image.mpr ⟨(x, e), hxe, rfl⟩

theorem tubeCells_eq_windowPins (ρ : ℝ) (T : E2 × E2) :
    Columns.tubeCells S (fun q => tb a (cls q)) (S.image Prod.fst) (cellOf ρ)
      (S.image (fun q => tb a (cls q))) (tb h) T =
      (windowPins S cls tb a h T).image (cellOf ρ) := by
  ext c
  simp only [Columns.tubeCells, Columns.cellsHit, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_inter]
  constructor
  · rintro ⟨j, hjJ, x, ⟨hxj, -⟩, rfl⟩
    have hj : j ∈ windowLines S cls tb a h T := by rw [windowLines_eq_filter]; exact hjJ
    exact ⟨x, mem_windowPins_iff.mpr ⟨j, hj, hxj⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hxj⟩ := mem_windowPins_iff.mp hx
    refine ⟨j, ?_, x, ⟨hxj, Finset.mem_image.mp (pins_subset_image_fst hxj)⟩, rfl⟩
    rw [← windowLines_eq_filter]; exact hj

end Objects

/-- Any pin set meets at most `11` times as many columns of width `ρ / 2` as `ρ`-cells. -/
theorem tube_cols_le_cells {ρ : ℝ} (hρ : 0 < ρ) {v : E2} (hv : ‖v‖ = 1) (U : Finset E2) :
    ((U.image (tubeCol v (ρ / 2))).card : ℝ) ≤ 11 * (U.image (cellOf ρ)).card := by
  classical
  have hsub : U.image (tubeCol v (ρ / 2)) ⊆ (U.image (cellOf ρ)).biUnion
      (fun c => (U.filter (fun x => cellOf ρ x = c)).image (tubeCol v (ρ / 2))) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨cellOf ρ x, Finset.mem_image_of_mem _ hx,
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩
  have hgroup : ∀ c ∈ U.image (cellOf ρ),
      (((U.filter (fun x => cellOf ρ x = c)).image (tubeCol v (ρ / 2))).card : ℝ) ≤ 11 := by
    intro c hc
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hc
    have himg : (U.filter (fun x => cellOf ρ x = cellOf ρ x₀)).image (tubeCol v (ρ / 2)) =
        ((U.filter (fun x => cellOf ρ x = cellOf ρ x₀)).image (fun x => inner ℝ x v)).image
          (roundZero (ρ / 2)) := by
      rw [Finset.image_image]; rfl
    rw [himg]
    have hA : ∀ t ∈ (U.filter (fun x => cellOf ρ x = cellOf ρ x₀)).image (fun x => inner ℝ x v),
        |t - inner ℝ x₀ v| ≤ 2 * ρ := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      have hd := dist_le_of_cellOf_eq hρ (Finset.mem_filter.mp hx).2
      rw [← inner_sub_left]
      calc |inner ℝ (x - x₀) v| ≤ ‖x - x₀‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ 2 * ρ := by rw [hv, mul_one, ← dist_eq_norm]; exact hd
    have h := roundZero_image_card_le (by positivity : (0 : ℝ) < ρ / 2) (by positivity) _ hA
    have e : 2 * (2 * ρ + ρ / 2) / (ρ / 2) + 1 = 11 := by field_simp; ring
    linarith
  calc ((U.image (tubeCol v (ρ / 2))).card : ℝ)
      ≤ (((U.image (cellOf ρ)).biUnion
          (fun c => (U.filter (fun x => cellOf ρ x = c)).image (tubeCol v (ρ / 2)))).card : ℝ) :=
        by exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ c ∈ U.image (cellOf ρ),
          (((U.filter (fun x => cellOf ρ x = c)).image (tubeCol v (ρ / 2))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ U.image (cellOf ρ), (11 : ℝ) := Finset.sum_le_sum hgroup
    _ = 11 * (U.image (cellOf ρ)).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

section Transfer

variable {r s ε₀ ε κ : ℝ} {n : ℕ} {P : Finset E2} {D S J₀ : Finset (E2 × E2)}
  {cls : E2 × E2 → E2 × E2} {J₁ : ℕ → Finset (E2 × E2)} {tb : ℕ → E2 × E2 → E2 × E2}

/-- The pins of one window line meet at most `121` times as many `ρ`-cells as columns. -/
theorem line_cells_le_cols (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb) {a h : ℕ}
    (ha : a ≤ n) (hh : h ≤ n) (hrδ : r ≤ palScale r n a) (hρ : palScale r n h ≤ 1 / 2)
    (h108 : 108 * palScale r n a ≤ palScale r n h) {T j : E2 × E2}
    (hj : j ∈ windowLines S cls tb a h T) :
    (((pinsOf S (fun q => tb a (cls q)) j ∩ S.image Prod.fst).image
        (cellOf (palScale r n h))).card : ℝ) ≤
      121 * (((pinsOf S (fun q => tb a (cls q)) j ∩ S.image Prod.fst).image
        (tubeCol (tubeAxis T) (palScale r n h / 2))).card : ℝ) := by
  classical
  obtain ⟨hgeo, -, hwidth, -⟩ := window_geometry hC ha hh hrδ T
  set ρ := palScale r n h with hρdef
  have hρpos : 0 < ρ := palScale_pos hC.fail.r_pos h
  set Pj := pinsOf S (fun q => tb a (cls q)) j ∩ S.image Prod.fst with hPj
  set col := tubeCol (tubeAxis T) (ρ / 2) with hcol
  have hjgeo := hgeo j hj
  -- the tube label is a line of `J₀`
  have hjJ : j ∈ J₀ := by
    rw [windowLines_eq_filter] at hj
    exact hC.window_line_mem ha (Finset.mem_filter.mp hj).1
  have hT2 : ‖T.2‖ = 1 := by
    have := (hC.line_norms (hC.tubes_sub h (hC.tube_mem h hh j hjJ))).1
    rwa [tb_eq_of_mem_windowLines hj] at this
  have hv : ‖tubeAxis T‖ = 1 := tubeAxis_norm hT2
  have htr : 1 / 2 ≤ |inner ℝ j.2 (perp (tubeAxis T))| :=
    transverse_of_close hT2 hρ hjgeo.2.2.2
  have hpw : ∀ x ∈ Pj, |inner ℝ (x - j.1) j.2| ≤ 27 * palScale r n a := by
    intro x hx
    have hxj := (Finset.mem_inter.mp hx).1
    exact hwidth j hj x (mem_windowPins_iff.mpr ⟨j, hj, hxj⟩) ((windowPin_iff hj).mpr hxj)
  have hsub : Pj.image (cellOf ρ) ⊆ (Pj.image col).biUnion
      (fun c => (Pj.filter (fun x => col x = c)).image (cellOf ρ)) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_biUnion.mpr ⟨col x, Finset.mem_image_of_mem _ hx,
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx, rfl⟩)⟩
  have hgroup : ∀ c ∈ Pj.image col,
      (((Pj.filter (fun x => col x = c)).image (cellOf ρ)).card : ℝ) ≤ 121 := by
    intro c hc
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hc
    set L := 6 * (ρ / 2) + 4 * (27 * palScale r n a) with hL
    have hL0 : 0 ≤ L := by have := palScale_pos hC.fail.r_pos (n := n) a; positivity
    have hclose : ∀ x ∈ Pj.filter (fun x => col x = col x₀), dist x x₀ ≤ L := by
      intro x hx
      obtain ⟨hxP, hxc⟩ := Finset.mem_filter.mp hx
      exact dist_le_of_same_tubeCol' hv (by positivity) hjgeo.1 htr (hpw x hxP) (hpw x₀ hx₀) hxc
    have h1 := cellOf_image_card_le hρpos hL0 x₀ _ hclose
    have hL4 : L + ρ ≤ 5 * ρ := by rw [hL]; linarith
    have h2 : 2 * (L + ρ) / ρ + 1 ≤ 11 := by
      rw [div_add_one hρpos.ne', div_le_iff₀ hρpos]; linarith
    have h3 : 0 ≤ 2 * (L + ρ) / ρ + 1 := by positivity
    have h4 : (2 * (L + ρ) / ρ + 1) ^ 2 ≤ 121 := by nlinarith
    linarith
  calc ((Pj.image (cellOf ρ)).card : ℝ)
      ≤ (((Pj.image col).biUnion
          (fun c => (Pj.filter (fun x => col x = c)).image (cellOf ρ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ c ∈ Pj.image col, (((Pj.filter (fun x => col x = c)).image (cellOf ρ)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ Pj.image col, (121 : ℝ) := Finset.sum_le_sum hgroup
    _ = 121 * (Pj.image col).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Column density of a window tube from its cell density**, in the form of the `hdens`
hypothesis of `caseA_window_contradiction`. -/
theorem window_column_density_of_cells (hC : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    {a h : ℕ} (ha : a ≤ n) (hh : h ≤ n) (hrδ : r ≤ palScale r n a)
    (hρ : palScale r n h ≤ 1 / 2) (h108 : 108 * palScale r n a ≤ palScale r n h)
    {T : E2 × E2} {dc : ℝ} (hdc : 0 ≤ dc)
    (hcell : dc * ((((S.image (fun q => tb a (cls q))).filter (fun j => tb h j = T)).card : ℝ) *
        (Columns.tubeCells S (fun q => tb a (cls q)) (S.image Prod.fst)
          (cellOf (palScale r n h)) (S.image (fun q => tb a (cls q))) (tb h) T).card) ≤
      ∑ j ∈ (S.image (fun q => tb a (cls q))).filter (fun j => tb h j = T),
        ((Columns.cellsHit S (fun q => tb a (cls q)) (S.image Prod.fst)
          (cellOf (palScale r n h)) j).card : ℝ)) :
    dc / 1331 * (((windowPins S cls tb a h T).image
        (tubeCol (tubeAxis T) (palScale r n h / 2))).card : ℝ) *
        (windowLines S cls tb a h T).card ≤
      ((((windowPins S cls tb a h T).image (tubeCol (tubeAxis T) (palScale r n h / 2))) ×ˢ
        (windowLines S cls tb a h T)).filter (fun p : ℝ × (E2 × E2) =>
          ∃ x ∈ windowPins S cls tb a h T, windowPin S cls tb a h T p.2 x ∧
            tubeCol (tubeAxis T) (palScale r n h / 2) x = p.1)).card := by
  classical
  set ρ := palScale r n h with hρdef
  have hρpos : 0 < ρ := palScale_pos hC.fail.r_pos h
  set col := tubeCol (tubeAxis T) (ρ / 2) with hcol
  set W := windowPins S cls tb a h T with hW
  set L := windowLines S cls tb a h T with hLdef
  have hL : L = (S.image (fun q => tb a (cls q))).filter (fun j => tb h j = T) :=
    windowLines_eq_filter T
  have htc := tubeCells_eq_windowPins (S := S) (cls := cls) (tb := tb) (a := a) (h := h) ρ T
  rw [← hL, htc] at hcell
  -- the right side, line by line
  have hrow : ∀ j ∈ L, ((W.image col).filter (fun c => ∃ x ∈ W,
      windowPin S cls tb a h T j x ∧ col x = c)) =
      (pinsOf S (fun q => tb a (cls q)) j ∩ S.image Prod.fst).image col := by
    intro j hj
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_inter]
    constructor
    · rintro ⟨-, x, hxW, hxj, rfl⟩
      have hxp := (windowPin_iff hj).mp hxj
      exact ⟨x, ⟨hxp, Finset.mem_image.mp (pins_subset_image_fst hxp)⟩, rfl⟩
    · rintro ⟨x, ⟨hxp, -⟩, rfl⟩
      have hxW : x ∈ W := mem_windowPins_iff.mpr ⟨j, hj, hxp⟩
      exact ⟨⟨x, hxW, rfl⟩, x, hxW, (windowPin_iff hj).mpr hxp, rfl⟩
  have hRHS : ((((W.image col) ×ˢ L).filter (fun p : ℝ × (E2 × E2) =>
      ∃ x ∈ W, windowPin S cls tb a h T p.2 x ∧ col x = p.1)).card : ℝ) =
      ∑ j ∈ L, (((pinsOf S (fun q => tb a (cls q)) j ∩ S.image Prod.fst).image col).card : ℝ) := by
    rw [Finset.card_filter, Finset.sum_product_right]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [← hrow j hj, Finset.card_filter]
    push_cast
    rfl
  rw [hRHS]
  -- each line: cells ≤ 121 columns
  have hlines : ∑ j ∈ L, ((Columns.cellsHit S (fun q => tb a (cls q)) (S.image Prod.fst)
      (cellOf ρ) j).card : ℝ) ≤ 121 * ∑ j ∈ L,
        (((pinsOf S (fun q => tb a (cls q)) j ∩ S.image Prod.fst).image col).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => line_cells_le_cols hC ha hh hrδ hρ h108 hj)
  -- the tube: columns ≤ 11 cells
  have hT2 : ‖(tubeAxis T)‖ = 1 ∨ L = ∅ := by
    by_cases hLe : L = ∅
    · exact Or.inr hLe
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hLe
      have hjJ : j ∈ J₀ := by
        rw [hL] at hj
        exact hC.window_line_mem ha (Finset.mem_filter.mp hj).1
      have h2 := (hC.line_norms (hC.tubes_sub h (hC.tube_mem h hh j hjJ))).1
      have hjW : j ∈ windowLines S cls tb a h T := hj
      rw [tb_eq_of_mem_windowLines hjW] at h2
      exact Or.inl (tubeAxis_norm h2)
  rcases hT2 with hv | hLe
  · have hcols := tube_cols_le_cells hρpos hv W
    have hLc : (0 : ℝ) ≤ L.card := Nat.cast_nonneg _
    calc dc / 1331 * ((W.image col).card : ℝ) * L.card
        ≤ dc / 1331 * (11 * (W.image (cellOf ρ)).card) * L.card := by
          gcongr
      _ = (1 / 121) * (dc * ((L.card : ℝ) * (W.image (cellOf ρ)).card)) := by ring
      _ ≤ (1 / 121) * ∑ j ∈ L, ((Columns.cellsHit S (fun q => tb a (cls q)) (S.image Prod.fst)
            (cellOf ρ) j).card : ℝ) := by gcongr
      _ ≤ (1 / 121) * (121 * ∑ j ∈ L,
            (((pinsOf S (fun q => tb a (cls q)) j ∩ S.image Prod.fst).image col).card : ℝ)) := by
          gcongr
      _ = _ := by ring
  · rw [hLe]; simp

/-- **A dense window tube in columns**, from the premise counts and the window conditions of
`CaseALeaf`: the `hT`/`hdens` input of `caseA_window_contradiction` with
`dens = B^-(3 dn + 9 e) / 8 / 1331`. -/
theorem HighConfig.dense_window_columns
    (H : HighConfig r s ε₀ ε κ n P D S J₀ cls J₁ tb)
    (hr1 : r < 1) (hn : 0 < n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 ≤ ε)
    {h a : ℕ} (hha : h ≤ a) (han : a ≤ n) (hRsmall : palScale r n a ≤ 1 / 8)
    {ℓ ν e : ℝ} (hℓ1 : ℓ ≤ 1) (hfar : r ^ (-κ + ℓ * (1 - s)) ≤ 1 / 2) (he : 0 ≤ e)
    {p₀ : E2} (hp₀ : p₀ ∈ S.image Prod.fst)
    (hsecond :
      (∑ t ∈ (S.image (fun q => tb a (cls q))).image (tb h),
        ((Columns.tubeCells S (fun q => tb a (cls q)) (S.image Prod.fst)
          (cellOf (palScale r n h)) (S.image (fun q => tb a (cls q))) (tb h) t).card : ℝ) ^ 2)
        ≤ 3 * r ^ (-(4 * ε + ν)) * (cellCount (S.image Prod.fst) (palScale r n h) : ℝ) ^ 2)
    (hWcoef : 8586240 * r ^ (-4 * ε) ≤ palBase r n ^ e)
    (hEcoef : 3 * r ^ (-(4 * ε + ν)) ≤ palBase r n ^ e)
    (hJcoef : (67080 : ℝ) ^ (2 : ℕ) * 5200 * r ^ (-(12 * ε + ε₀ + ℓ * s)) ≤ palBase r n ^ e)
    (hIcoef : 72 * r ^ (-2 * ε) ≤ palBase r n ^ e)
    (hUcoef : 4829760000000 * (palBase r n) ^ (2 : ℕ) * r ^ (-4 * ε) ≤ palBase r n ^ e)
    (hpalette : ((Finset.Icc h a).card : ℝ) ≤ palBase r n ^ e)
    {dn : ℝ}
    (hright : ∀ i : ℕ, h ≤ i → i ≤ a →
      ptProfile r n S h - s * h ≤ ptProfile r n S i - s * i)
    (hunif : ∀ t : ℕ, t ≤ n → |bushProfile r n S p₀ t - s * t| ≤ dn)
    (hhn : h ≤ n) (hrδ : r ≤ palScale r n a) (hρ : palScale r n h ≤ 1 / 2)
    (h108 : 108 * palScale r n a ≤ palScale r n h) :
    ∃ T ∈ S.image (fun q => tb h (tb a (cls q))),
      palBase r n ^ (-(3 * dn + 9 * e)) / 8 / 1331 *
          (((windowPins S cls tb a h T).image
            (tubeCol (tubeAxis T) (palScale r n h / 2))).card : ℝ) *
          (windowLines S cls tb a h T).card ≤
        ((((windowPins S cls tb a h T).image (tubeCol (tubeAxis T) (palScale r n h / 2))) ×ˢ
          (windowLines S cls tb a h T)).filter (fun p : ℝ × (E2 × E2) =>
            ∃ x ∈ windowPins S cls tb a h T, windowPin S cls tb a h T p.2 x ∧
              tubeCol (tubeAxis T) (palScale r n h / 2) x = p.1)).card := by
  obtain ⟨t, ht, hdense⟩ := H.dense_window_cells hr1 hn hs0 hs1 hε hha han hRsmall hℓ1 hfar he
    hp₀ hsecond hWcoef hEcoef hJcoef hIcoef hUcoef hpalette hright hunif
  have hB0 : 0 < palBase r n := palBase_pos H.fail.r_pos
  refine ⟨t, ?_, window_column_density_of_cells H han hhn hrδ hρ h108
    (by positivity) hdense⟩
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_image_of_mem _ hq

end Transfer

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

-- Workspace source: o214/x0665, commit fb70ebc, WangZahlLot/Obl/wz_furstenberg_katz_tao_high/High/WindowColumns.lean
