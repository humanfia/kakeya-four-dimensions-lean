-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.WideIncidence.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o222/x0722 High/WideIncidence.lean (c61cafd).
-- Adapted from local obligation o157, branch x0675, commit 5a2c82ba2c9f.
-- Source: High/WideIncidence.lean. Shared half definitions imported from accepted o213.
-- Ported from internal o141, session x0563's WideIncidence.lean (branch x0563); namespace renamed.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.WideStripPacking
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.StripIncidence

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

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

/-- Quadratic incidence bound for strips of width `w` with labels separated at
the possibly finer scale `r`. -/
theorem wide_strip_incidence_bound {r w C m : ℝ} (hr : 0 < r) (hrw : r ≤ w)
    (hw2 : w ≤ 1 / 2) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (Y : Finset E2) (hYne : Y.Nonempty) (hY4 : ∀ y ∈ Y, ‖y‖ ≤ 4)
    (hFr : ∀ (x : E2) (ρ : ℝ), r ≤ ρ →
      ((Y.filter (fun z => z ∈ Metric.closedBall x ρ)).card : ℝ) ≤ C * ρ * Y.card)
    (J : Finset (E2 × E2)) (hJ : ∀ j ∈ J, ‖j.1‖ ≤ 4 ∧ ‖j.2‖ = 1)
    (hsep : (J : Set (E2 × E2)).Pairwise (StripSep r))
    (K : ℕ) (hK : (Y.card : ℝ) ≤ (2 : ℝ) ^ K)
    (hinc : m * Y.card ≤ ∑ j ∈ J,
      ((Y.filter (fun y => |inner ℝ (y - j.1) j.2| < w)).card : ℝ)) :
    m ^ 2 ≤ 128000 * (64 * w / r + 2) * (36 * w / r + 2) *
      C * (1 + Real.log (1 / w)) * (K + 1) ^ 2 * J.card := by
  classical
  have hY : (0 : ℝ) < Y.card := Nat.cast_pos.mpr hYne.card_pos
  let n : E2 × E2 → ℕ := fun j =>
    (Y.filter (fun y => |inner ℝ (y - j.1) j.2| < w)).card
  let B : ℝ := 32000 * (64 * w / r + 2) * (36 * w / r + 2) *
    C * (1 + Real.log (1 / w))
  have hb := weak_quadratic_sum J n K (B * (Y.card : ℝ) ^ 2)
    (fun j hj => (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hK) (by
      intro a ha S hSJ hrich
      have hcount := wide_rich_strip_count hr hrw hw2 hC (div_nonneg ha.le hY.le)
        Y hYne hY4 hFr S (fun j hj => hJ j (hSJ hj)) (hsep.mono hSJ)
        (fun j hj => by simpa [div_mul_cancel₀ _ hY.ne', n] using hrich j hj)
      have hmul := mul_le_mul_of_nonneg_right hcount (sq_nonneg (Y.card : ℝ))
      have hid : (a / (Y.card : ℝ)) ^ 2 * (S.card : ℝ) * (Y.card : ℝ) ^ 2 =
          a ^ 2 * S.card := by field_simp
      rwa [hid] at hmul)
  have hsq := (pow_le_pow_left₀ (mul_nonneg hm hY.le) hinc 2).trans hb
  dsimp only [B] at hsq
  have hh : m ^ 2 * (Y.card : ℝ) ^ 2 ≤
      (128000 * (64 * w / r + 2) * (36 * w / r + 2) *
        C * (1 + Real.log (1 / w)) * (K + 1) ^ 2 * J.card) * (Y.card : ℝ) ^ 2 := by
    convert hsq using 1 <;> ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hY)).mp hh

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
