-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.WideStripSecondMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Rich-count proof adapted from workspace o157/x0675 High/WideIncidence.lean.
-- Ported from internal o141, session x0563's WideIncidence.lean (branch x0563); namespace renamed.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.WideStripPacking
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.StripSecondMoment

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_osw_single_scale_heavy_pairs

attribute [local instance] Classical.propDecidable

/-- The rich-strip estimate remains valid when the strip width exceeds the
label separation; the extra cost is quadratic in their ratio. -/
theorem wide_rich_strip_count {r w C l : ℝ} (hr : 0 < r) (hrw : r ≤ w) (hw2 : w ≤ 1 / 2)
    (hC : 0 ≤ C) (hl : 0 ≤ l) (Y : Finset E2) (hYne : Y.Nonempty)
    (hY4 : ∀ y ∈ Y, ‖y‖ ≤ 4)
    (hFr : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((Y.filter (fun z => z ∈ Metric.closedBall x ρ)).card : ℝ) ≤ C * ρ * Y.card)
    (J : Finset (E2 × E2)) (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    (hrich : ∀ j ∈ J, l * Y.card ≤
      ((Y.filter (fun y => |inner ℝ (y - j.1) j.2| < w)).card : ℝ)) :
    l ^ 2 * J.card ≤
      32000 * (64 * w / r + 2) * (36 * w / r + 2) * C * (1 + Real.log (1 / w)) := by
  have hw : 0 < w := hr.trans_le hrw
  obtain ⟨F, hFJ, hFsep, hlarge⟩ := strip_coarse_subfamily hr hw hw2 J hJ hsep
  have hcount := rich_strip_count_finset hw (by linarith) hC hl Y hYne hY4
    (fun x ρ hρ => hFr x ρ (hrw.trans hρ)) F (fun j hj => hJ j (hFJ hj))
    hFsep (fun j hj => hrich j (hFJ hj))
  calc
    l ^ 2 * J.card ≤ l ^ 2 * (2 * (64 * w / r + 2) * (36 * w / r + 2) * F.card) :=
      mul_le_mul_of_nonneg_left hlarge (sq_nonneg l)
    _ = (2 * (64 * w / r + 2) * (36 * w / r + 2)) * (l ^ 2 * F.card) := by ring
    _ ≤ (2 * (64 * w / r + 2) * (36 * w / r + 2)) *
        (16000 * C * (1 + Real.log (1 / w))) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

/-- A second moment for separated tube labels whose incidence strips are
wider than the separation scale. This accommodates maximal coarse-tube
assignments without changing their classes or choosing a coordinate grid. -/
theorem wide_strip_second_moment {r w C : ℝ} (hr : 0 < r) (hrw : r ≤ w)
    (hw2 : w ≤ 1 / 2) (hC : 0 ≤ C)
    (Y : Finset E2) (hYne : Y.Nonempty) (hY4 : ∀ y ∈ Y, ‖y‖ ≤ 4)
    (hFr : ∀ x ρ, r ≤ ρ →
      ((Y.filter (fun z => z ∈ Metric.closedBall x ρ)).card : ℝ) ≤ C * ρ * Y.card)
    (J : Finset (E2 × E2)) (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    (K : ℕ) (hK : (Y.card : ℝ) ≤ (2 : ℝ) ^ K)
    (d : E2 × E2 → ℕ)
    (hd : ∀ j ∈ J, d j ≤
      (Y.filter (fun y => |inner ℝ (y - j.1) j.2| < w)).card) :
    (∑ j ∈ J, (d j : ℝ) ^ 2) ≤
      64000 * (64 * w / r + 2) * (36 * w / r + 2) *
        C * (1 + Real.log (1 / w)) * (2 * K + 1) * (Y.card : ℝ) ^ 2 := by
  classical
  have hY : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hYne.card_pos
  let B : ℝ := 32000 * (64 * w / r + 2) * (36 * w / r + 2) *
    C * (1 + Real.log (1 / w))
  have hh := second_moment_of_weak_quadratic J d K (B * (Y.card : ℝ) ^ 2)
    (fun j hj => (Nat.cast_le.mpr ((hd j hj).trans (Finset.card_filter_le _ _))).trans hK)
    (by
      intro a ha S hSJ hrich
      have hcount := wide_rich_strip_count hr hrw hw2 hC (div_nonneg ha.le hY.le)
        Y hYne hY4 hFr S (fun j hj => hJ j (hSJ hj)) (hsep.mono hSJ)
        (fun j hj => by
          have hc : a ≤ ((Y.filter (fun y => |inner ℝ (y - j.1) j.2| < w)).card : ℝ) :=
            (hrich j hj).trans (Nat.cast_le.mpr (hd j (hSJ hj)))
          simpa only [div_mul_cancel₀ _ hY.ne'] using hc)
      have hmul := mul_le_mul_of_nonneg_right hcount (sq_nonneg (Y.card : ℝ))
      have hid : (a / (Y.card : ℝ)) ^ 2 * (S.card : ℝ) * (Y.card : ℝ) ^ 2 =
          a ^ 2 * S.card := by field_simp
      rwa [hid] at hmul)
  convert hh using 1 <;> dsimp only [B] <;> ring

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
