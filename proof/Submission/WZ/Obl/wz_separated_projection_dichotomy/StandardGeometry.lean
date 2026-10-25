-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.StandardGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.SeparatedCore

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric

theorem StandardTripleGeometry.separated_small_sets {S T U : Finset Plane}
    (h : StandardTripleGeometry S T U) :
    (∀ a ∈ S, 1 / 2 ≤ ‖a‖ ∧ ∀ a' ∈ S, dist a a' ≤ 1 / 10) ∧
    (∀ b ∈ T, ∀ b' ∈ T, dist b b' ≤ 1 / 10) ∧
    (∀ b ∈ U, ∀ b' ∈ U, dist b b' ≤ 1 / 10) ∧
    (∀ b ∈ T, ∀ b' ∈ U, 1 / 2 ≤ dist b b') := by
  obtain ⟨a, c, ha, hc, hS, hT, hU⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    constructor
    · have ht := dist_triangle a x 0
      rw [dist_zero_right, dist_zero_right, dist_comm a x, ha] at ht
      linarith [hS x hx]
    · intro y hy
      have ht := dist_triangle x a y
      rw [dist_comm a y] at ht
      linarith [hS x hx, hS y hy]
  · intro x hx y hy
    have ht := dist_triangle x 0 y
    rw [dist_comm 0 y] at ht
    linarith [hT x hx, hT y hy]
  · intro x hx y hy
    have ht := dist_triangle x c y
    rw [dist_comm c y] at ht
    linarith [hU x hx, hU y hy]
  · intro x hx y hy
    have ht := dist_triangle c y x
    have ht' := dist_triangle c x 0
    rw [dist_zero_right, hc] at ht'
    rw [dist_comm c y, dist_comm y x] at ht
    linarith [hT x hx, hU y hy]

end WangZahlLot.Obl.wz_separated_projection_dichotomy
