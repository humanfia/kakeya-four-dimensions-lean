-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData.TubeTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o214/x0665 WangZahlLot/Obl/wz_furstenberg_katz_tao_high/GraphData/TubeTransfer.lean (82de8bd).
import Mathlib
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.BridgeThin
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates.NormalChart

/-!
# From a coarse tube in the plane to tube coordinates

Fix a unit vector `v` (the axis of a coarse tube), a central line `(c_T, a_T)` of the chart of `v`
and a vertical scale `λ > 0`.  A label `j = (p, e)` goes to the centred, rescaled chart line

  `tubeLine v c_T a_T λ j = ((cot e - c_T) / λ, (a_j - a_T) / λ)`,  `(cot e, a_j) = lineChart v j`.

A point `q` goes to the column `col q` (within `w` of its first chart coordinate) and to a height
code `hc q` (within `μ` of its centred rescaled height).

* `tubeLine_meets`: a pin `q` of `j` (`|⟨q - p, e⟩| ≤ ι`) gives, in tube coordinates, a height of
  `tubeLine j` at the column of `q` within `(2 ι + Δs w)/λ + μ` of the column's height codes
  (`Δs` bounds the chart slopes).
* `tubeLine_separated`: `StripSep r`-separated labels with normals transverse to `v` give tube
  lines at sup-distance at least `r / (10 λ)`.
* `lineHeight_tubeLine`: the height of a tube line is the centred rescaled chart height.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

/-- The centred, rescaled chart line of a label. -/
noncomputable def tubeLine (v : Plane) (cT aT lam : ℝ) (j : Plane × Plane) : ℝ × ℝ :=
  (((lineChart v j).1 - cT) / lam, ((lineChart v j).2 - aT) / lam)

theorem lineHeight_tubeLine (v : Plane) {cT aT lam : ℝ} (hlam : lam ≠ 0) (j : Plane × Plane)
    (x : ℝ) :
    lineHeight (tubeLine v cT aT lam j) x = (height (lineChart v j) x - (aT + cT * x)) / lam := by
  simp only [lineHeight, tubeLine, height]
  field_simp
  ring

/-- **Incidences become column meetings.** -/
theorem tubeLine_meets {v : Plane} (hv : ‖v‖ = 1) {cT aT lam ι w Δs μ : ℝ} (hlam : 0 < lam)
    (hw : 0 ≤ w) {j : Plane × Plane} (hjn : 1 / 2 ≤ |inner ℝ j.2 (perp v)|)
    (hslope : |(lineChart v j).1| ≤ Δs) {q : Plane} (hinc : |inner ℝ (q - j.1) j.2| ≤ ι)
    (col : Plane → ℝ) (hcol : |col q - (pointChart v q).1| ≤ w)
    (hc : Plane → ℝ) (hhc : |hc q - ((pointChart v q).2 - (aT + cT * col q)) / lam| ≤ μ) :
    |lineHeight (tubeLine v cT aT lam j) (col q) - hc q| ≤ (2 * ι + Δs * w) / lam + μ := by
  have hinc' := chart_incidence (p := j.1) (e := j.2) (q := q) hv (by norm_num : (0 : ℝ) < 1 / 2)
    hjn hinc
  have hpair : (j.1, j.2) = j := rfl
  rw [hpair] at hinc'
  have hι2 : ι / (1 / 2) = 2 * ι := by ring
  rw [hι2] at hinc'
  -- move from the point's abscissa to its column
  have hshift : |height (lineChart v j) (col q) - height (lineChart v j) (pointChart v q).1| ≤
      Δs * w := by
    simp only [height]
    have : (lineChart v j).1 * col q + (lineChart v j).2 -
        ((lineChart v j).1 * (pointChart v q).1 + (lineChart v j).2) =
        (lineChart v j).1 * (col q - (pointChart v q).1) := by ring
    rw [this, abs_mul]
    exact mul_le_mul hslope hcol (abs_nonneg _) (le_trans (abs_nonneg _) hslope)
  have hdiff : |height (lineChart v j) (col q) - (pointChart v q).2| ≤ 2 * ι + Δs * w := by
    calc |height (lineChart v j) (col q) - (pointChart v q).2|
        ≤ |height (lineChart v j) (col q) - height (lineChart v j) (pointChart v q).1| +
            |height (lineChart v j) (pointChart v q).1 - (pointChart v q).2| := abs_sub_le _ _ _
      _ ≤ Δs * w + 2 * ι := by
          rw [abs_sub_comm (height (lineChart v j) (pointChart v q).1)]
          linarith
      _ = 2 * ι + Δs * w := by ring
  rw [lineHeight_tubeLine v hlam.ne' j (col q)]
  have e : (height (lineChart v j) (col q) - (aT + cT * col q)) / lam - hc q =
      (height (lineChart v j) (col q) - (pointChart v q).2) / lam +
        (((pointChart v q).2 - (aT + cT * col q)) / lam - hc q) := by ring
  rw [e]
  calc |(height (lineChart v j) (col q) - (pointChart v q).2) / lam +
        (((pointChart v q).2 - (aT + cT * col q)) / lam - hc q)|
      ≤ |(height (lineChart v j) (col q) - (pointChart v q).2) / lam| +
          |((pointChart v q).2 - (aT + cT * col q)) / lam - hc q| := abs_add_le _ _
    _ ≤ (2 * ι + Δs * w) / lam + μ := by
        rw [abs_div, abs_of_pos hlam]
        have h2 : |((pointChart v q).2 - (aT + cT * col q)) / lam - hc q| ≤ μ := by
          rw [abs_sub_comm]; exact hhc
        exact add_le_add (div_le_div_of_nonneg_right hdiff hlam.le) h2

/-- **Separated labels give separated tube lines.** -/
theorem tubeLine_separated {v : Plane} (hv : ‖v‖ = 1) {cT aT lam r : ℝ} (hlam : 0 < lam)
    {l l' : Plane × Plane} (he : ‖l.2‖ = 1) (he' : ‖l'.2‖ = 1) (hp' : ‖l'.1‖ ≤ 4)
    (hw : 1 / 2 ≤ |inner ℝ l.2 (perp v)|) (hw' : 1 / 2 ≤ |inner ℝ l'.2 (perp v)|)
    (hsep : StripSep r l l') :
    r / (10 * lam) ≤ dist (tubeLine v cT aT lam l) (tubeLine v cT aT lam l') := by
  have h := rescaled_lineChart_separated hlam hv he he' hp' hw hw' hsep
  have e : dist (tubeLine v cT aT lam l) (tubeLine v cT aT lam l') =
      dist (rescale lam (lineChart v l)) (rescale lam (lineChart v l')) := by
    simp only [tubeLine, rescale, Prod.dist_eq, Real.dist_eq]
    congr 1
    · congr 1; field_simp; ring
    · congr 1; field_simp; ring
  rw [e]; exact h

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates

attribute [local instance] Classical.propDecidable

/-- **Case A for one coarse tube of the plane.**  For positive `e, b, β` there are `ζ, δ₀` such
that the following data cannot exist at a tube tolerance `δ = (2 ι + Δs w)/λ + μ ≤ δ₀`: separated
labels `J` with transverse normals and chart slopes at most `Δs`, pins `U` with a pin relation of
width `ι`, columns `col` and height codes `hc`, such that columns and labels are related with
density `d` through pins, the columns are spread and Frostman, the tube lines are Frostman, the
columns carry at most `F` height codes with `F² ≤ K₀ #J`, and the numerics of
`dense_columns_thin_false` hold with `σ = r / (10 λ)`. -/
theorem coarse_tube_false {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ ζ δ₀ : ℝ, 0 < ζ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ (v : Plane) (cT aT lam r ι w Δs μ q d F K₀ : ℝ), ‖v‖ = 1 → 0 < lam → 0 < r → 0 ≤ ι →
      0 ≤ w → 0 ≤ μ → 0 < q → q ≤ 1 → 0 < d → d ≤ 1 → 1 ≤ K₀ → 1 ≤ F →
      0 < (2 * ι + Δs * w) / lam + μ → (2 * ι + Δs * w) / lam + μ ≤ δ₀ →
      F ≤ ((2 * ι + Δs * w) / lam + μ) ^ (-(1 - e)) →
      (4 * tubeKD K₀ q b β d
          (⌈(18 * ((2 * ι + Δs * w) / lam + μ) / (q * (r / (10 * lam))) + 2) ^ 2⌉₊ : ℝ) *
          (2 * (1 + 8 / q) ^ 2) ^ β) * 2 ^ (1 + b) ≤ ((2 * ι + Δs * w) / lam + μ) ^ (-ζ) →
      4 ≤ ((2 * ι + Δs * w) / lam + μ) ^ (-(ζ / 2)) →
      ∀ (J : Finset (Plane × Plane)) (U : Finset Plane) (pin : Plane × Plane → Plane → Prop)
        (col hc : Plane → ℝ),
      J.Nonempty → U.Nonempty →
      (∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)| ∧
        |(lineChart v j).1| ≤ Δs) →
      (∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep r j j') →
      (∀ j ∈ J, ∀ x ∈ U, pin j x → |inner ℝ (x - j.1) j.2| ≤ ι) →
      (∀ x ∈ U, |col x - (pointChart v x).1| ≤ w ∧ |col x| ≤ 4) →
      (∀ x ∈ U, |hc x - ((pointChart v x).2 - (aT + cT * col x)) / lam| ≤ μ) →
      (∀ j ∈ J, ∀ y ∈ U.image col, |lineHeight (tubeLine v cT aT lam j) y| ≤ 7 / 2) →
      (∀ y ∈ U.image col, (((U.filter (fun x => col x = y)).image hc).card : ℝ) ≤ F) →
      d * ((U.image col).card : ℝ) * J.card ≤
        ((((U.image col) ×ˢ J).filter
          (fun p : ℝ × (Plane × Plane) => ∃ x ∈ U, pin p.2 x ∧ col x = p.1)).card : ℝ) →
      (∀ y ∈ U.image col, (((U.image col).filter (fun y' => |y - y'| < q)).card : ℝ) ≤
        d ^ 2 / 16 * (U.image col).card) →
      (∀ z ρ : ℝ, (2 * ι + Δs * w) / lam + μ ≤ ρ →
        (((U.image col).filter (fun y => |y - z| ≤ ρ)).card : ℝ) ≤
          K₀ * ρ ^ β * (U.image col).card) →
      (∀ c a ρ : ℝ, (2 * ι + Δs * w) / lam + μ ≤ ρ →
        ((J.filter (fun j => |(tubeLine v cT aT lam j).1 - c| ≤ ρ ∧
          |(tubeLine v cT aT lam j).2 - a| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ (1 + b) * J.card) →
      F ^ 2 ≤ K₀ * J.card → False := by
  obtain ⟨ζ, δ₀, hζ, hδ₀, hδ₀2, hfalse⟩ := dense_columns_thin_false he hb hβ
  refine ⟨ζ, δ₀, hζ, hδ₀, hδ₀2, ?_⟩
  intro v cT aT lam r ι w Δs μ q d F K₀ hv hlam hr hι hw hμ hq hq1 hd hd1 hK₀ hF hδpos hδδ₀ hFe
    hloss h4 J U pin col hc hJne hUne hJ hJsep hpin hcol hhc hheight hYc hdens hspread hIfr hLfr hquad
  set δ := (2 * ι + Δs * w) / lam + μ with hδ
  set I := U.image col with hI
  set Yc : ℝ → Finset ℝ := fun y => (U.filter (fun x => col x = y)).image hc with hYcdef
  set T := tubeLine v cT aT lam with hT
  have hσ : 0 < r / (10 * lam) := by positivity
  -- tube lines are separated, hence the map is injective
  have hsepT : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → r / (10 * lam) ≤ dist (T j) (T j') := by
    intro j hj j' hj' hjj'
    obtain ⟨he1, -, hn1, -⟩ := hJ j hj
    obtain ⟨he2, hp2, hn2, -⟩ := hJ j' hj'
    exact tubeLine_separated hv hlam he1 he2 hp2 hn1 hn2 (hJsep j hj j' hj' hjj')
  have hinj : Set.InjOn T (↑J : Set (Plane × Plane)) := by
    intro j hj j' hj' heq
    by_contra hne
    have := hsepT j hj j' hj' hne
    rw [heq, dist_self] at this
    linarith
  set L := J.image T with hL
  have hLcard : L.card = J.card := Finset.card_image_of_injOn hinj
  have hIne : I.Nonempty := hUne.image _
  refine hfalse δ (r / (10 * lam)) q d F K₀ hδpos hδδ₀ hσ hq hq1 hd hd1 hK₀ hF hFe hloss h4
    L I Yc (hJne.image _) hIne (fun y hy => ?_) ?_ ?_ hYc ?_ hspread hIfr ?_ ?_
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (hcol x hx).2
  · intro l hl y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
    exact hheight j hj y hy
  · intro l hl l' hl' hll'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hl'
    have hjj' : j ≠ j' := fun h => hll' (by rw [h])
    exact hsepT j hj j' hj' hjj'
  · -- density transfers through the injective map
    rw [hLcard]
    refine hdens.trans ?_
    have hsub : ((I ×ˢ J).filter (fun p : ℝ × (Plane × Plane) =>
        ∃ x ∈ U, pin p.2 x ∧ col x = p.1)).image (fun p => (p.1, T p.2)) ⊆
        (I ×ˢ L).filter (fun p => Meets Yc δ p.1 p.2) := by
      intro p hp
      obtain ⟨⟨y, j⟩, hyj, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hyjprod, x, hx, hpinx, hcolx⟩ := Finset.mem_filter.mp hyj
      obtain ⟨hy, hj⟩ := Finset.mem_product.mp hyjprod
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, Finset.mem_image_of_mem _ hj⟩, ?_⟩
      obtain ⟨-, -, hn, hsl⟩ := hJ j hj
      have hm := tubeLine_meets hv hlam hw hn hsl (hpin j hj x hx hpinx) col (hcol x hx).1 hc
        (hhc x hx)
      refine ⟨hc x, ?_, ?_⟩
      · simp only [hYcdef]
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hcolx⟩, rfl⟩
      · simp only at hcolx ⊢
        rw [← hcolx]
        exact hm
    have hinj2 : Set.InjOn (fun p : ℝ × (Plane × Plane) => (p.1, T p.2))
        ↑((I ×ˢ J).filter (fun p : ℝ × (Plane × Plane) => ∃ x ∈ U, pin p.2 x ∧ col x = p.1)) := by
      intro p hp p' hp' heq
      simp only [Prod.mk.injEq] at heq
      have hpJ := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
      have hp'J := (Finset.mem_product.mp (Finset.mem_filter.mp hp').1).2
      exact Prod.ext heq.1 (hinj hpJ hp'J heq.2)
    rw [← Finset.card_image_of_injOn hinj2]
    exact_mod_cast Finset.card_le_card hsub
  · intro c a ρ hρ
    have hsubL : L.filter (fun l => |l.1 - c| ≤ ρ ∧ |l.2 - a| ≤ ρ) ⊆
        (J.filter (fun j => |(T j).1 - c| ≤ ρ ∧ |(T j).2 - a| ≤ ρ)).image T := by
      intro l hl
      obtain ⟨hlL, hlc⟩ := Finset.mem_filter.mp hl
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hlL
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hlc⟩, rfl⟩
    calc ((L.filter (fun l => |l.1 - c| ≤ ρ ∧ |l.2 - a| ≤ ρ)).card : ℝ)
        ≤ (((J.filter (fun j => |(T j).1 - c| ≤ ρ ∧ |(T j).2 - a| ≤ ρ)).image T).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubL
      _ ≤ ((J.filter (fun j => |(T j).1 - c| ≤ ρ ∧ |(T j).2 - a| ≤ ρ)).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ ≤ K₀ * ρ ^ (1 + b) * J.card := hLfr c a ρ hρ
      _ = K₀ * ρ ^ (1 + b) * L.card := by rw [hLcard]
  · rw [hLcard]; exact hquad

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
