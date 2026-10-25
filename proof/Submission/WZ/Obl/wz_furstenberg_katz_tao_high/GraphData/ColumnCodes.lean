-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.ColumnCodes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/ColumnCodes.lean (82de8bd).
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.TubeTransfer
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.ColumnCount

/-!
# Columns and height codes of a coarse tube

For the axis `v` of a coarse tube, a point `x` gets the column `tubeCol v w x`, its first chart
coordinate rounded toward zero to a multiple of `w` (so `|tubeCol| ≤ 4` for `‖x‖ ≤ 4`), and the
height code `tubeCode v cT aT lam μ w x = rounded μ ((pointChart v x).2 / lam) - (aT + cT col)/lam`,
within `μ` of its centred rescaled height.

`column_codes_card`: with `lam = 4 Δs` and `μ = ι / (2 Δs)`, if every pin has at least `M` labels of
`J` through it (pin relation of width `ι`, transverse normals, chart slopes at most `Δs`) and
`4 Δs w ≤ 2 ι`, each column carries at most `8 #J / M` codes: x0572's column height count
(TubeCoordinates.ColumnCount), the codes of a column being a translate of its rounded heights.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

attribute [local instance] Classical.propDecidable

/-- Round toward zero to a multiple of `w`. -/
noncomputable def roundZero (w t : ℝ) : ℝ := if 0 ≤ t then w * ⌊t / w⌋ else w * ⌈t / w⌉

theorem roundZero_close {w : ℝ} (hw : 0 < w) (t : ℝ) : |roundZero w t - t| ≤ w := by
  unfold roundZero
  split_ifs with ht
  · have h1 := Int.floor_le (t / w)
    have h2 := Int.lt_floor_add_one (t / w)
    have e1 : w * ⌊t / w⌋ ≤ t := by
      have := mul_le_mul_of_nonneg_left h1 hw.le
      rwa [mul_div_cancel₀ t hw.ne'] at this
    have e2 : t < w * ⌊t / w⌋ + w := by
      have := mul_lt_mul_of_pos_left h2 hw
      rw [mul_add, mul_one, mul_div_cancel₀ t hw.ne'] at this
      linarith
    rw [abs_le]; constructor <;> linarith
  · have h1 := Int.le_ceil (t / w)
    have h2 := Int.ceil_lt_add_one (t / w)
    have e1 : t ≤ w * ⌈t / w⌉ := by
      have := mul_le_mul_of_nonneg_left h1 hw.le
      rwa [mul_div_cancel₀ t hw.ne'] at this
    have e2 : w * ⌈t / w⌉ < t + w := by
      have := mul_lt_mul_of_pos_left h2 hw
      rw [mul_add, mul_one, mul_div_cancel₀ t hw.ne'] at this
      linarith
    rw [abs_le]; constructor <;> linarith

theorem abs_roundZero_le {w : ℝ} (hw : 0 < w) (t : ℝ) : |roundZero w t| ≤ |t| := by
  unfold roundZero
  split_ifs with ht
  · have h1 := Int.floor_le (t / w)
    have e1 : w * ⌊t / w⌋ ≤ t := by
      have := mul_le_mul_of_nonneg_left h1 hw.le
      rwa [mul_div_cancel₀ t hw.ne'] at this
    have h0 : (0 : ℝ) ≤ ⌊t / w⌋ := by exact_mod_cast Int.floor_nonneg.mpr (div_nonneg ht hw.le)
    have e0 : 0 ≤ w * ⌊t / w⌋ := mul_nonneg hw.le h0
    rw [abs_of_nonneg e0, abs_of_nonneg ht]; exact e1
  · push Not at ht
    have h1 := Int.le_ceil (t / w)
    have e1 : t ≤ w * ⌈t / w⌉ := by
      have := mul_le_mul_of_nonneg_left h1 hw.le
      rwa [mul_div_cancel₀ t hw.ne'] at this
    have h0 : (⌈t / w⌉ : ℝ) ≤ 0 := by
      exact_mod_cast Int.ceil_le.mpr (by push_cast; exact (div_neg_of_neg_of_pos ht hw).le)
    have e0 : w * ⌈t / w⌉ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw.le h0
    rw [abs_of_nonpos e0, abs_of_neg ht]; linarith

/-- The column of a point. -/
noncomputable def tubeCol (v : Plane) (w : ℝ) (x : Plane) : ℝ := roundZero w (pointChart v x).1

/-- The height code of a point. -/
noncomputable def tubeCode (v : Plane) (cT aT lam μ w : ℝ) (x : Plane) : ℝ :=
  rounded μ ((pointChart v x).2 / lam) - (aT + cT * tubeCol v w x) / lam

theorem tubeCol_close (v : Plane) {w : ℝ} (hw : 0 < w) (x : Plane) :
    |tubeCol v w x - (pointChart v x).1| ≤ w := roundZero_close hw _

theorem abs_tubeCol_le {v : Plane} (hv : ‖v‖ = 1) {w : ℝ} (hw : 0 < w) {x : Plane}
    (hx : ‖x‖ ≤ 4) : |tubeCol v w x| ≤ 4 := by
  refine (abs_roundZero_le hw _).trans ?_
  calc |(pointChart v x).1| = |inner ℝ x v| := rfl
    _ ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
    _ ≤ 4 := by rw [hv, mul_one]; exact hx

theorem tubeCode_close (v : Plane) {cT aT lam μ w : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
    (x : Plane) :
    |tubeCode v cT aT lam μ w x - ((pointChart v x).2 - (aT + cT * tubeCol v w x)) / lam| ≤ μ := by
  have h := rounded_error hμ ((pointChart v x).2 / lam)
  have e : tubeCode v cT aT lam μ w x - ((pointChart v x).2 - (aT + cT * tubeCol v w x)) / lam =
      rounded μ ((pointChart v x).2 / lam) - (pointChart v x).2 / lam := by
    unfold tubeCode; field_simp; ring
  rw [e, abs_le]; constructor <;> linarith [h.1, h.2]

/-- **Codes per column.** -/
theorem column_codes_card {v : Plane} (hv : ‖v‖ = 1) {cT aT ι Δs w M : ℝ} (hι : 0 < ι)
    (hΔs : 0 < Δs) (hw : 0 < w) (hM : 0 < M) (hscale : 4 * Δs * w ≤ 2 * ι)
    (J : Finset (Plane × Plane)) (U : Finset Plane) (pin : Plane × Plane → Plane → Prop)
    (hJ : ∀ j ∈ J, 1 / 2 ≤ |inner ℝ j.2 (perp v)| ∧ |(lineChart v j).1| ≤ Δs)
    (hpin : ∀ j ∈ J, ∀ x ∈ U, pin j x → |inner ℝ (x - j.1) j.2| ≤ ι)
    (hdeg : ∀ x ∈ U, M ≤ ((J.filter (fun j => pin j x)).card : ℝ))
    (hinjL : Set.InjOn (lineChart v) ↑J) (y : ℝ) :
    M * (((U.filter (fun x => tubeCol v w x = y)).image
      (tubeCode v cT aT (4 * Δs) (ι / (2 * Δs)) w)).card : ℝ) ≤ 8 * J.card := by
  set V := U.filter (fun x => tubeCol v w x = y) with hV
  set P := V.image (pointChart v) with hP
  set L := J.image (lineChart v) with hL
  have hLcard : L.card = J.card := Finset.card_image_of_injOn hinjL
  have h4Δ : 0 < 4 * Δs := by positivity
  have hcount := column_height_card_at_width P L (r := 2 * ι) (Δ := 4 * Δs) (w := w) (c := y)
    (M := M) (by positivity) h4Δ hscale
    (by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      have hxcol := (Finset.mem_filter.mp hx).2
      have := tubeCol_close v hw x
      rw [hxcol] at this
      rw [abs_sub_comm]; exact this)
    (by
      intro l hl
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
      have := (hJ j hj).2
      linarith [abs_nonneg ((lineChart v j).1)])
    (by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      have hxU := (Finset.mem_filter.mp hx).1
      have hsub : (J.filter (fun j => pin j x)).image (lineChart v) ⊆
          L.filter (fun l => |(pointChart v x).2 - height l (pointChart v x).1| ≤ 2 * ι) := by
        intro l hl
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
        obtain ⟨hjJ, hpj⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hjJ, ?_⟩
        have hinc := chart_incidence (p := j.1) (e := j.2) (q := x) hv
          (by norm_num : (0 : ℝ) < 1 / 2) (hJ j hjJ).1 (hpin j hjJ x hxU hpj)
        have hpair : (j.1, j.2) = j := rfl
        rw [hpair] at hinc
        have e : ι / (1 / 2) = 2 * ι := by ring
        rwa [e] at hinc
      have hinj2 : Set.InjOn (lineChart v) ↑(J.filter (fun j => pin j x)) :=
        hinjL.mono (fun j hj => (Finset.mem_filter.mp hj).1)
      calc M ≤ ((J.filter (fun j => pin j x)).card : ℝ) := hdeg x hxU
        _ = (((J.filter (fun j => pin j x)).image (lineChart v)).card : ℝ) := by
            rw [Finset.card_image_of_injOn hinj2]
        _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub)
  -- the codes of the column are a translate of its rounded heights
  have hcodes : V.image (tubeCode v cT aT (4 * Δs) (ι / (2 * Δs)) w) =
      (P.image (fun p => rounded (2 * ι / (4 * Δs)) (p.2 / (4 * Δs)))).image
        (fun z => z - (aT + cT * y) / (4 * Δs)) := by
    ext c
    simp only [Finset.mem_image, hP]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxcol := (Finset.mem_filter.mp hx).2
      refine ⟨rounded (2 * ι / (4 * Δs)) ((pointChart v x).2 / (4 * Δs)),
        ⟨pointChart v x, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
      unfold tubeCode
      rw [hxcol]
      have e : ι / (2 * Δs) = 2 * ι / (4 * Δs) := by field_simp; ring
      rw [e]
    · rintro ⟨z, ⟨p, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      have hxcol := (Finset.mem_filter.mp hx).2
      refine ⟨x, hx, ?_⟩
      unfold tubeCode
      rw [hxcol]
      have e : ι / (2 * Δs) = 2 * ι / (4 * Δs) := by field_simp; ring
      rw [e]
  rw [hcodes]
  have hle : (((P.image (fun p => rounded (2 * ι / (4 * Δs)) (p.2 / (4 * Δs)))).image
      (fun z => z - (aT + cT * y) / (4 * Δs))).card : ℝ) ≤
      ((P.image (fun p => rounded (2 * ι / (4 * Δs)) (p.2 / (4 * Δs)))).card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  have e2 : 2 * ι / (4 * Δs) = 2 * ι / (4 * Δs) := rfl
  calc M * (((P.image (fun p => rounded (2 * ι / (4 * Δs)) (p.2 / (4 * Δs)))).image
        (fun z => z - (aT + cT * y) / (4 * Δs))).card : ℝ)
      ≤ M * ((P.image (fun p => rounded (2 * ι / (4 * Δs)) (p.2 / (4 * Δs)))).card : ℝ) :=
        mul_le_mul_of_nonneg_left hle hM.le
    _ ≤ 8 * L.card := hcount
    _ = 8 * J.card := by rw [hLcard]

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

attribute [local instance] Classical.propDecidable

/-- The tube tolerance of the rounded columns and codes. -/
noncomputable def tubeTol (ι Δs w : ℝ) : ℝ := (2 * ι + Δs * w) / (4 * Δs) + ι / (2 * Δs)

/-- **Case A for one coarse tube, with rounded columns and codes.**  Only pin degrees `M` are
needed for the code count: each column carries at most `F = 8 #J / M` codes, and
`F² ≤ K₀ #J` becomes `64 #J ≤ K₀ M²`. -/
theorem coarse_tube_rounded_false {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ ζ δ₀ : ℝ, 0 < ζ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ (v : Plane) (cT aT r ι Δs w M q d K₀ : ℝ), ‖v‖ = 1 → 0 < r → 0 < ι → 0 < Δs → 0 < w →
      0 < M → 0 < q → q ≤ 1 → 0 < d → d ≤ 1 → 1 ≤ K₀ → 4 * Δs * w ≤ 2 * ι →
      tubeTol ι Δs w ≤ δ₀ →
      ∀ (J : Finset (Plane × Plane)) (U : Finset Plane) (pin : Plane × Plane → Plane → Prop),
      J.Nonempty → U.Nonempty →
      (8 * (J.card : ℝ) / M ≤ (tubeTol ι Δs w) ^ (-(1 - e))) →
      (4 * tubeKD K₀ q b β d
          (⌈(18 * tubeTol ι Δs w / (q * (r / (10 * (4 * Δs)))) + 2) ^ 2⌉₊ : ℝ) *
          (2 * (1 + 8 / q) ^ 2) ^ β) * 2 ^ (1 + b) ≤ (tubeTol ι Δs w) ^ (-ζ) →
      4 ≤ (tubeTol ι Δs w) ^ (-(ζ / 2)) →
      (∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)| ∧
        |(lineChart v j).1| ≤ Δs) →
      (∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep r j j') →
      (∀ j ∈ J, ∀ x ∈ U, pin j x → |inner ℝ (x - j.1) j.2| ≤ ι) →
      (∀ x ∈ U, ‖x‖ ≤ 4) →
      (∀ x ∈ U, M ≤ ((J.filter (fun j => pin j x)).card : ℝ)) →
      (∀ j ∈ J, ∀ y ∈ U.image (tubeCol v w),
        |lineHeight (tubeLine v cT aT (4 * Δs) j) y| ≤ 7 / 2) →
      d * ((U.image (tubeCol v w)).card : ℝ) * J.card ≤
        ((((U.image (tubeCol v w)) ×ˢ J).filter
          (fun p : ℝ × (Plane × Plane) => ∃ x ∈ U, pin p.2 x ∧ tubeCol v w x = p.1)).card : ℝ) →
      (∀ y ∈ U.image (tubeCol v w), (((U.image (tubeCol v w)).filter
        (fun y' => |y - y'| < q)).card : ℝ) ≤ d ^ 2 / 16 * (U.image (tubeCol v w)).card) →
      (∀ z ρ : ℝ, tubeTol ι Δs w ≤ ρ →
        (((U.image (tubeCol v w)).filter (fun y => |y - z| ≤ ρ)).card : ℝ) ≤
          K₀ * ρ ^ β * (U.image (tubeCol v w)).card) →
      (∀ c a ρ : ℝ, tubeTol ι Δs w ≤ ρ →
        ((J.filter (fun j => |(tubeLine v cT aT (4 * Δs) j).1 - c| ≤ ρ ∧
          |(tubeLine v cT aT (4 * Δs) j).2 - a| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ (1 + b) * J.card) →
      64 * (J.card : ℝ) ≤ K₀ * M ^ 2 → False := by
  obtain ⟨ζ, δ₀, hζ, hδ₀, hδ₀2, hfalse⟩ := coarse_tube_false he hb hβ
  refine ⟨ζ, δ₀, hζ, hδ₀, hδ₀2, ?_⟩
  intro v cT aT r ι Δs w M q d K₀ hv hr hι hΔs hw hM hq hq1 hd hd1 hK₀ hscale hδδ₀ J U pin
    hJne hUne hFe hloss h4 hJ hJsep hpin hU4 hdeg hheight hdens hspread hIfr hLfr hquad
  have hlam : 0 < 4 * Δs := by positivity
  have hμ : 0 < ι / (2 * Δs) := by positivity
  have hδpos : 0 < tubeTol ι Δs w := by unfold tubeTol; positivity
  have htol : (2 * ι + Δs * w) / (4 * Δs) + ι / (2 * Δs) = tubeTol ι Δs w := rfl
  -- injectivity of the chart on `J`
  have hinjL : Set.InjOn (lineChart v) ↑J := by
    intro j hj j' hj' heq
    by_contra hne
    obtain ⟨he1, -, hn1, -⟩ := hJ j hj
    obtain ⟨he2, hp2, hn2, -⟩ := hJ j' hj'
    have h := lineChart_separated hv he1 he2 hp2 hn1 hn2 (hJsep j hj j' hj' hne)
    rw [heq, dist_self] at h
    linarith
  -- the code bound
  set F := 8 * (J.card : ℝ) / M with hFdef
  have hJpos : (0 : ℝ) < J.card := by exact_mod_cast hJne.card_pos
  have hF1 : 1 ≤ F := by
    obtain ⟨x, hx⟩ := hUne
    have hMJ : M ≤ J.card := (hdeg x hx).trans (by exact_mod_cast Finset.card_filter_le _ _)
    rw [hFdef, le_div_iff₀ hM]; linarith
  have hYc : ∀ y ∈ U.image (tubeCol v w), ((((U.filter (fun x => tubeCol v w x = y)).image
      (tubeCode v cT aT (4 * Δs) (ι / (2 * Δs)) w)).card : ℝ)) ≤ F := by
    intro y _
    have h := column_codes_card hv (cT := cT) (aT := aT) hι hΔs hw hM hscale J U pin
      (fun j hj => ⟨(hJ j hj).2.2.1, (hJ j hj).2.2.2⟩) hpin hdeg hinjL y
    rw [hFdef, le_div_iff₀ hM]
    linarith
  have hquadF : F ^ 2 ≤ K₀ * J.card := by
    rw [hFdef, div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  rw [← htol] at hδδ₀ hFe hloss h4 hIfr hLfr
  exact hfalse v cT aT (4 * Δs) r ι w Δs (ι / (2 * Δs)) q d F K₀ hv hlam hr hι.le hw.le hμ.le hq
    hq1 hd hd1 hK₀ hF1 (by rw [htol]; exact hδpos) hδδ₀ hFe hloss h4 J U pin (tubeCol v w)
    (tubeCode v cT aT (4 * Δs) (ι / (2 * Δs)) w) hJne hUne hJ hJsep hpin
    (fun x hx => ⟨tubeCol_close v hw x, abs_tubeCol_le hv hw (hU4 x hx)⟩)
    (fun x _ => tubeCode_close v hlam hμ x) hheight hYc hdens hspread hIfr hLfr hquadF

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
