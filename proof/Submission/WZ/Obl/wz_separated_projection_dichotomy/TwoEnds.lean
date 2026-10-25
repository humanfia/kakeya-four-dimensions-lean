-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.TwoEnds.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set

attribute [local instance] Classical.propDecidable

/-- Approximate maximization of mass divided by a power of the scale. The
index can parametrize lines, balls, or any other family of localization sets.
The factor two avoids any compactness assumption on that family. -/
theorem exists_weighted_localization {X I : Type*} (E : Finset X)
    (U : I → ℝ → Set X) (i₀ : I) {δ ζ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hζ : 0 ≤ ζ)
    (hcover : ∀ x ∈ E, x ∈ U i₀ 1) :
    ∃ (i : I) (w : ℝ) (E' : Finset X), δ ≤ w ∧ w ≤ 1 ∧
      (∀ x, x ∈ E' ↔ x ∈ E ∧ x ∈ U i w) ∧
      w ^ ζ * (E.card : ℝ) / 2 ≤ (E'.card : ℝ) ∧
      ∀ (j : I) (r : ℝ), δ ≤ r → r ≤ 1 →
        ((E'.filter (fun x => x ∈ U j r)).card : ℝ) ≤
          2 * (r / w) ^ ζ * (E'.card : ℝ) := by
  classical
  by_cases hE : E = ∅
  · subst E
    exact ⟨i₀, 1, ∅, hδ1, le_rfl, by simp, by simp, by simp⟩
  have hEpos : (0 : ℝ) < E.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hE)
  let mass (i : I) (w : ℝ) : ℝ := (E.filter (fun x => x ∈ U i w)).card
  let B : Set ℝ := {v | ∃ (i : I) (w : ℝ), δ ≤ w ∧ w ≤ 1 ∧ v = mass i w / w ^ ζ}
  have hbase : mass i₀ 1 = (E.card : ℝ) := by
    dsimp [mass]
    rw [Finset.filter_true_of_mem hcover]
  have hmem : (E.card : ℝ) ∈ B := by
    exact ⟨i₀, 1, hδ1, le_rfl, by simp [hbase]⟩
  have hB : BddAbove B := by
    refine ⟨(E.card : ℝ) / δ ^ ζ, ?_⟩
    rintro v ⟨i, w, hδw, hw1, rfl⟩
    have hw : 0 < w := hδ.trans_le hδw
    have hm : mass i w ≤ (E.card : ℝ) := by
      dsimp [mass]
      exact_mod_cast Finset.card_filter_le E (fun x => x ∈ U i w)
    calc mass i w / w ^ ζ ≤ (E.card : ℝ) / w ^ ζ :=
        div_le_div_of_nonneg_right hm (Real.rpow_nonneg hw.le _)
      _ ≤ (E.card : ℝ) / δ ^ ζ := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
        exact Real.rpow_le_rpow hδ.le hδw hζ
  have hsup : (E.card : ℝ) ≤ sSup B := le_csSup hB hmem
  have hsuppos : 0 < sSup B := hEpos.trans_le hsup
  obtain ⟨v, ⟨i, w, hδw, hw1, rfl⟩, hv⟩ :=
    exists_lt_of_lt_csSup (s := B) ⟨(E.card : ℝ), hmem⟩
      (by linarith : sSup B / 2 < sSup B)
  have hw : 0 < w := hδ.trans_le hδw
  have hwp : 0 < w ^ ζ := Real.rpow_pos_of_pos hw _
  have hscore : sSup B ≤ 2 * (mass i w / w ^ ζ) := by linarith
  let E' := E.filter (fun x => x ∈ U i w)
  have hmass : mass i w = (E'.card : ℝ) := rfl
  refine ⟨i, w, E', hδw, hw1, fun x => Finset.mem_filter, ?_, ?_⟩
  · have h := hsup.trans hscore
    rw [hmass] at h
    rw [← mul_div_assoc] at h
    have h' := (le_div_iff₀ hwp).mp h
    nlinarith
  · intro j r hδr hr1
    have hr : 0 < r := hδ.trans_le hδr
    have hrp : 0 < r ^ ζ := Real.rpow_pos_of_pos hr _
    have hj : mass j r / r ^ ζ ≤ sSup B :=
      le_csSup hB ⟨j, r, hδr, hr1, rfl⟩
    have hj' := (div_le_iff₀ hrp).mp (hj.trans hscore)
    have hinter : ((E'.filter (fun x => x ∈ U j r)).card : ℝ) ≤ mass j r := by
      dsimp [mass]
      exact_mod_cast Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
    calc ((E'.filter (fun x => x ∈ U j r)).card : ℝ) ≤ mass j r := hinter
      _ ≤ (2 * (mass i w / w ^ ζ)) * r ^ ζ := hj'
      _ = 2 * (r / w) ^ ζ * (E'.card : ℝ) := by
        rw [Real.div_rpow hr.le hw.le, hmass]
        ring

end WangZahlLot.Obl.wz_separated_projection_dichotomy
