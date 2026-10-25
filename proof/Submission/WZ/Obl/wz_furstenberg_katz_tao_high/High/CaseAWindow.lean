-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.CaseAWindow.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/CaseAWindow.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.TubeChart
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.GraphData.TubeTwoEnds

/-!
# Case A at one coarse tube, in the frame of the tube

`RoundedTubeFalse e b β ζ δ₀` is the conclusion of x0665's `coarse_tube_rounded_false` (ported
in `O214.GraphData`) for fixed `ζ, δ₀`; `exists_roundedTubeFalse` provides them.

`caseA_window_false` instantiates it in the frame of a coarse tube `T` (`v = tubeAxis T`,
`(cT, aT) = lineChart v T`, slope bound `Δs = 16 ρ`, vertical scale `4 Δs`, pin width
`ι = 27 δ`, column width `w = ι / (2 Δs)`) and derives the chart hypotheses from the closeness
of the lines to `T` (`near_tube_chart`): every line `j` has a unit normal, `‖j.1‖ ≤ 4`, offset
`|⟨j.1 - T.1, j.2⟩| ≤ 17 ρ` and normal within `ρ` of `±T.2`. The counting hypotheses (pin
degree, density, column and line Frostman, the quadratic bound) stay explicit.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.TubeCoordinates
open WangZahlLot.Obl.wz_furstenberg_katz_tao_high.GraphData
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

attribute [local instance] Classical.propDecidable

/-- The conclusion of `coarse_tube_rounded_false` for fixed `ζ, δ₀`. -/
def RoundedTubeFalse (e b β ζ δ₀ : ℝ) : Prop :=
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
      64 * (J.card : ℝ) ≤ K₀ * M ^ 2 → False

theorem exists_roundedTubeFalse {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ ζ δ₀ : ℝ, 0 < ζ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ RoundedTubeFalse e b β ζ δ₀ :=
  coarse_tube_rounded_false he hb hβ

/-- The tube tolerance in the frame of a tube of width `ρ` with lines of width `δ`. -/
theorem tubeTol_frame {ρ δ : ℝ} (hρ : 0 < ρ) :
    tubeTol (27 * δ) (16 * ρ) (27 * δ / (2 * (16 * ρ))) = 243 * δ / (128 * ρ) := by
  unfold tubeTol
  field_simp
  ring

/-- **Case A at one coarse tube, in its frame.** The chart hypotheses of
`coarse_tube_rounded_false` follow from the closeness of the lines to the tube `T`; the
tolerance is `243 δ / (128 ρ)`. -/
theorem caseA_window_false {e b β ζ δ₀ : ℝ} (hRT : RoundedTubeFalse e b β ζ δ₀)
    {T : Plane × Plane} (hT2 : ‖T.2‖ = 1) (hT4 : ‖T.1‖ ≤ 4)
    {ρ δ M q d K₀ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hρ1 : ρ ≤ 1 / 2)
    (hM : 0 < M) (hq : 0 < q) (hq1 : q ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1) (hK₀ : 1 ≤ K₀)
    (htol : 243 * δ / (128 * ρ) ≤ δ₀)
    (J : Finset (Plane × Plane)) (U : Finset Plane) (pin : Plane × Plane → Plane → Prop)
    (hJne : J.Nonempty) (hUne : U.Nonempty)
    (hF : 8 * (J.card : ℝ) / M ≤ (243 * δ / (128 * ρ)) ^ (-(1 - e)))
    (hloss : (4 * tubeKD K₀ q b β d
          (⌈(18 * (243 * δ / (128 * ρ)) / (q * (δ / (10 * (4 * (16 * ρ))))) + 2) ^ 2⌉₊ : ℝ) *
          (2 * (1 + 8 / q) ^ 2) ^ β) * 2 ^ (1 + b) ≤ (243 * δ / (128 * ρ)) ^ (-ζ))
    (h4 : 4 ≤ (243 * δ / (128 * ρ)) ^ (-(ζ / 2)))
    (hJgeo : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ |inner ℝ (j.1 - T.1) j.2| ≤ 17 * ρ ∧
      (dist j.2 T.2 ≤ ρ ∨ dist j.2 (-T.2) ≤ ρ))
    (hJsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep δ j j')
    (hpin : ∀ j ∈ J, ∀ x ∈ U, pin j x → |inner ℝ (x - j.1) j.2| ≤ 27 * δ)
    (hU4 : ∀ x ∈ U, ‖x‖ ≤ 4)
    (hdeg : ∀ x ∈ U, M ≤ ((J.filter (fun j => pin j x)).card : ℝ))
    (hdens : d * ((U.image (tubeCol (tubeAxis T) (27 * δ / (2 * (16 * ρ))))).card : ℝ) *
        J.card ≤
      ((((U.image (tubeCol (tubeAxis T) (27 * δ / (2 * (16 * ρ))))) ×ˢ J).filter
        (fun p : ℝ × (Plane × Plane) => ∃ x ∈ U, pin p.2 x ∧
          tubeCol (tubeAxis T) (27 * δ / (2 * (16 * ρ))) x = p.1)).card : ℝ))
    (hspread : ∀ y ∈ U.image (tubeCol (tubeAxis T) (27 * δ / (2 * (16 * ρ)))),
      (((U.image (tubeCol (tubeAxis T) (27 * δ / (2 * (16 * ρ))))).filter
        (fun y' => |y - y'| < q)).card : ℝ) ≤
      d ^ 2 / 16 * (U.image (tubeCol (tubeAxis T) (27 * δ / (2 * (16 * ρ))))).card)
    (hcolfr : ∀ z ρ' : ℝ, 243 * δ / (128 * ρ) ≤ ρ' →
      (((U.image (tubeCol (tubeAxis T) (27 * δ / (2 * (16 * ρ))))).filter
        (fun y => |y - z| ≤ ρ')).card : ℝ) ≤
      K₀ * ρ' ^ β * (U.image (tubeCol (tubeAxis T) (27 * δ / (2 * (16 * ρ))))).card)
    (hlinefr : ∀ c a ρ' : ℝ, 243 * δ / (128 * ρ) ≤ ρ' →
      ((J.filter (fun j =>
        |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
          (4 * (16 * ρ)) j).1 - c| ≤ ρ' ∧
        |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
          (4 * (16 * ρ)) j).2 - a| ≤ ρ')).card : ℝ) ≤ K₀ * ρ' ^ (1 + b) * J.card)
    (hquad : 64 * (J.card : ℝ) ≤ K₀ * M ^ 2) : False := by
  set v := tubeAxis T with hv
  have hv1 : ‖v‖ = 1 := tubeAxis_norm hT2
  have hΔs : 0 < 16 * ρ := by positivity
  have hι : 0 < 27 * δ := by positivity
  have hw : 0 < 27 * δ / (2 * (16 * ρ)) := by positivity
  have hscale : 4 * (16 * ρ) * (27 * δ / (2 * (16 * ρ))) ≤ 2 * (27 * δ) := by
    have : 4 * (16 * ρ) * (27 * δ / (2 * (16 * ρ))) = 2 * (27 * δ) := by field_simp; ring
    rw [this]
  have htt := tubeTol_frame (δ := δ) hρ
  have hθ : ρ ≤ 1 / 2 := hρ1
  have hlam : 0 < 4 * (16 * ρ) := by positivity
  -- the chart facts of the lines
  have hJ : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)| ∧
      |(lineChart v j).1| ≤ 16 * ρ := by
    intro j hj
    obtain ⟨h1, h2, h3, h4'⟩ := hJgeo j hj
    obtain ⟨hc1, hc2, -⟩ := near_tube_chart (lam := 4 * (16 * ρ)) hT2 hT4 h1 hθ hlam h3 h4'
    exact ⟨h1, h2, hc1, hc2.trans (by linarith)⟩
  have hheight : ∀ j ∈ J, ∀ y ∈ U.image (tubeCol v (27 * δ / (2 * (16 * ρ)))),
      |lineHeight (tubeLine v (lineChart v T).1 (lineChart v T).2 (4 * (16 * ρ)) j) y| ≤
        7 / 2 := by
    intro j hj y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨h1, -, h3, h4'⟩ := hJgeo j hj
    obtain ⟨-, -, hc3⟩ := near_tube_chart (lam := 4 * (16 * ρ)) hT2 hT4 h1 hθ hlam h3 h4'
    have hy4 : |tubeCol v (27 * δ / (2 * (16 * ρ))) x| ≤ 4 := abs_tubeCol_le hv1 hw (hU4 x hx)
    refine (hc3 _ hy4).trans ?_
    rw [div_le_iff₀ hlam]
    nlinarith
  rw [← htt] at htol hF hloss h4 hcolfr hlinefr
  exact hRT v (lineChart v T).1 (lineChart v T).2 δ (27 * δ) (16 * ρ)
    (27 * δ / (2 * (16 * ρ))) M q d K₀ hv1 hδ hι hΔs hw hM hq hq1 hd hd1 hK₀ hscale htol
    J U pin hJne hUne hF hloss h4 hJ hJsep hpin hU4 hdeg hheight hdens hspread hcolfr hlinefr
    hquad

/-- The conclusion of `tube_two_ends_false` for fixed `η, δ₀`. -/
def TwoEndsFalse (e b β η δ₀ : ℝ) : Prop :=
    ∀ (v : Plane) (cT aT r ι Δs w M d K₀ A : ℝ), ‖v‖ = 1 → 0 < r → 0 < ι → 0 < Δs → 0 < w →
      0 < M → 1 ≤ K₀ → 0 ≤ A → 4 * Δs * w ≤ 2 * ι → ι ≤ K₀ * r →
      tubeTol ι Δs w ≤ δ₀ →
      K₀ ≤ (tubeTol ι Δs w) ^ (-η) → A ≤ (tubeTol ι Δs w) ^ (-η) →
      (tubeTol ι Δs w) ^ η ≤ d → d ≤ 1 →
      ∀ (J : Finset (Plane × Plane)) (U : Finset Plane) (pin : Plane × Plane → Plane → Prop),
      J.Nonempty → U.Nonempty →
      (8 * (J.card : ℝ) / M ≤ (tubeTol ι Δs w) ^ (-(1 - e))) →
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
      (∀ j ∈ J, ∀ z ρ : ℝ, tubeTol ι Δs w ≤ ρ →
        (((U.image (tubeCol v w)).filter (fun y => (∃ x ∈ U, pin j x ∧ tubeCol v w x = y) ∧
          |y - z| ≤ ρ)).card : ℝ) ≤
          A * ρ ^ β * (((U.image (tubeCol v w)).filter
            (fun y => ∃ x ∈ U, pin j x ∧ tubeCol v w x = y)).card : ℝ)) →
      (∀ c a ρ : ℝ, tubeTol ι Δs w ≤ ρ →
        ((J.filter (fun j => |(tubeLine v cT aT (4 * Δs) j).1 - c| ≤ ρ ∧
          |(tubeLine v cT aT (4 * Δs) j).2 - a| ≤ ρ)).card : ℝ) ≤ K₀ * ρ ^ (1 + b) * J.card) →
      64 * (J.card : ℝ) ≤ K₀ * M ^ 2 → False

theorem exists_twoEndsFalse {e b β : ℝ} (he : 0 < e) (hb : 0 < b) (hβ : 0 < β) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧ TwoEndsFalse e b β η δ₀ :=
  tube_two_ends_false he hb hβ

/-- The tube tolerance with columns of width `ρ / 2`. -/
theorem tubeTol_half {ρ δ : ℝ} (hρ : 0 < ρ) :
    tubeTol (27 * δ) (16 * ρ) (ρ / 2) = (108 * δ + 8 * ρ ^ 2) / (64 * ρ) := by
  unfold tubeTol
  field_simp
  ring

/-- **Case A at one coarse tube from two-ended classes, in the frame of the tube**, with columns
of width `w` (`64 ρ w ≤ 54 δ`, for instance `w = ρ / 2` when `ρ² ≤ δ`). The chart hypotheses of
`tube_two_ends_false` follow from the closeness of the lines to `T`; the tolerance is
`tubeTol (27 δ) (16 ρ) w`. -/
theorem caseA_window_two_ends_false {e b β η δ₀ : ℝ} (hTE : TwoEndsFalse e b β η δ₀)
    {T : Plane × Plane} (hT2 : ‖T.2‖ = 1) (hT4 : ‖T.1‖ ≤ 4)
    {ρ δ w M d K₀ A : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hρ1 : ρ ≤ 1 / 2) (hw : 0 < w)
    (hscale : 4 * (16 * ρ) * w ≤ 2 * (27 * δ))
    (hM : 0 < M) (hK₀ : 27 ≤ K₀) (hA : 0 ≤ A)
    (htol : tubeTol (27 * δ) (16 * ρ) w ≤ δ₀)
    (hK₀η : K₀ ≤ (tubeTol (27 * δ) (16 * ρ) w) ^ (-η))
    (hAη : A ≤ (tubeTol (27 * δ) (16 * ρ) w) ^ (-η))
    (hdη : (tubeTol (27 * δ) (16 * ρ) w) ^ η ≤ d) (hd1 : d ≤ 1)
    (J : Finset (Plane × Plane)) (U : Finset Plane) (pin : Plane × Plane → Plane → Prop)
    (hJne : J.Nonempty) (hUne : U.Nonempty)
    (hF : 8 * (J.card : ℝ) / M ≤ (tubeTol (27 * δ) (16 * ρ) w) ^ (-(1 - e)))
    (hJgeo : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ |inner ℝ (j.1 - T.1) j.2| ≤ 17 * ρ ∧
      (dist j.2 T.2 ≤ ρ ∨ dist j.2 (-T.2) ≤ ρ))
    (hJsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → StripSep δ j j')
    (hpin : ∀ j ∈ J, ∀ x ∈ U, pin j x → |inner ℝ (x - j.1) j.2| ≤ 27 * δ)
    (hU4 : ∀ x ∈ U, ‖x‖ ≤ 4)
    (hdeg : ∀ x ∈ U, M ≤ ((J.filter (fun j => pin j x)).card : ℝ))
    (hdens : d * ((U.image (tubeCol (tubeAxis T) w)).card : ℝ) * J.card ≤
      ((((U.image (tubeCol (tubeAxis T) w)) ×ˢ J).filter
        (fun p : ℝ × (Plane × Plane) => ∃ x ∈ U, pin p.2 x ∧
          tubeCol (tubeAxis T) w x = p.1)).card : ℝ))
    (htwo : ∀ j ∈ J, ∀ z ρ' : ℝ, tubeTol (27 * δ) (16 * ρ) w ≤ ρ' →
      (((U.image (tubeCol (tubeAxis T) w)).filter (fun y =>
        (∃ x ∈ U, pin j x ∧ tubeCol (tubeAxis T) w x = y) ∧ |y - z| ≤ ρ')).card : ℝ) ≤
        A * ρ' ^ β * (((U.image (tubeCol (tubeAxis T) w)).filter
          (fun y => ∃ x ∈ U, pin j x ∧ tubeCol (tubeAxis T) w x = y)).card : ℝ))
    (hlinefr : ∀ c a ρ' : ℝ, tubeTol (27 * δ) (16 * ρ) w ≤ ρ' →
      ((J.filter (fun j =>
        |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
          (4 * (16 * ρ)) j).1 - c| ≤ ρ' ∧
        |(tubeLine (tubeAxis T) (lineChart (tubeAxis T) T).1 (lineChart (tubeAxis T) T).2
          (4 * (16 * ρ)) j).2 - a| ≤ ρ')).card : ℝ) ≤ K₀ * ρ' ^ (1 + b) * J.card)
    (hquad : 64 * (J.card : ℝ) ≤ K₀ * M ^ 2) : False := by
  set v := tubeAxis T with hv
  have hv1 : ‖v‖ = 1 := tubeAxis_norm hT2
  have hΔs : 0 < 16 * ρ := by positivity
  have hι : 0 < 27 * δ := by positivity
  have hιK : 27 * δ ≤ K₀ * δ := mul_le_mul_of_nonneg_right hK₀ hδ.le
  have hlam : 0 < 4 * (16 * ρ) := by positivity
  have hJ : ∀ j ∈ J, ‖j.2‖ = 1 ∧ ‖j.1‖ ≤ 4 ∧ 1 / 2 ≤ |inner ℝ j.2 (perp v)| ∧
      |(lineChart v j).1| ≤ 16 * ρ := by
    intro j hj
    obtain ⟨h1, h2, h3, h4'⟩ := hJgeo j hj
    obtain ⟨hc1, hc2, -⟩ := near_tube_chart (lam := 4 * (16 * ρ)) hT2 hT4 h1 hρ1 hlam h3 h4'
    exact ⟨h1, h2, hc1, hc2.trans (by linarith)⟩
  have hheight : ∀ j ∈ J, ∀ y ∈ U.image (tubeCol v w),
      |lineHeight (tubeLine v (lineChart v T).1 (lineChart v T).2 (4 * (16 * ρ)) j) y| ≤
        7 / 2 := by
    intro j hj y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨h1, -, h3, h4'⟩ := hJgeo j hj
    obtain ⟨-, -, hc3⟩ := near_tube_chart (lam := 4 * (16 * ρ)) hT2 hT4 h1 hρ1 hlam h3 h4'
    have hy4 : |tubeCol v w x| ≤ 4 := abs_tubeCol_le hv1 hw (hU4 x hx)
    refine (hc3 _ hy4).trans ?_
    rw [div_le_iff₀ hlam]
    nlinarith
  exact hTE v (lineChart v T).1 (lineChart v T).2 δ (27 * δ) (16 * ρ) w M d K₀ A hv1 hδ hι hΔs
    hw hM (by linarith) hA hscale hιK htol hK₀η hAη hdη hd1 J U pin hJne hUne hF hJ hJsep hpin
    hU4 hdeg hheight hdens htwo hlinefr hquad

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
