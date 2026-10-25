-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.SmallComparison.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.FixedComparison
import Submission.WZ.Obl.wz_essentially_distinct_tube_count

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open MeasureTheory
open WangZahlLot.Obl.wz_normalized_projection_iteration (Slope)

/-- The normalized cinematic estimate, expressed through the local moment interface. -/
def CinematicEstimate : Prop :=
  ∀ e : ℝ, 0 < e → ∃ ηC : ℝ, 0 < ηC ∧ ∃ dC : ℝ, 0 < dC ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ dC → τ ≤ 1 / 100 → ∀ f : ℝ → ℝ,
      Slope f → |f 0| ≤ 1 → CinematicMomentAt τ ηC e f

/-- The cinematic estimate supplies every sufficiently small comparison exponent. -/
theorem small_comparison_of_cinematic (hC : CinematicEstimate) {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) : ComparisonAt ε := by
  intro κ hκ
  let η := min (ε ^ 3 / 100000) (κ / 100)
  let s := 1 - 4 * ε ^ 2
  let e := ε / 100
  let vloss := ε ^ 3 / 100
  let t := ε ^ 3 / 1000
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η ≤ ε ^ 3 / 100000 := min_le_left _ _
  have hηκ : η ≤ κ / 100 := min_le_right _ _
  have hε2 : 0 < ε ^ 2 := by positivity
  have hε3 : 0 < ε ^ 3 := by positivity
  have hε2ε : ε ^ 2 ≤ ε / 100 := by nlinarith
  have hε2small : ε ^ 2 ≤ 1 / 10000 := by nlinarith
  have hε3le : ε ^ 3 ≤ ε ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (show 0 ≤ 1 - ε by linarith)]
  have hε4le : ε ^ 4 ≤ ε ^ 2 / 10000 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (show 0 ≤ 1 / 10000 - ε ^ 2 by linarith)]
  have hs : 0 ≤ s := by dsimp [s]; nlinarith
  have hs1 : s ≤ 1 := by dsimp [s]; nlinarith
  have he : 0 < e := by dsimp [e]; positivity
  have hvLoss : 0 < vloss := by dsimp [vloss]; positivity
  have hroot : 0 < (1 - ε ^ 2) * (2 - s) - η - (1 + ε ^ 2) := by
    dsimp [s]
    nlinarith
  have hres : η < ε ^ 2 := by nlinarith
  have hlight : 0 < ε ^ 3 / 4 - 3 * vloss - 3 * t := by
    dsimp [vloss, t]
    nlinarith
  have hremove : 3 * η < t := by dsimp [t]; nlinarith
  have hretain : 3 * η < κ := by nlinarith
  have hexp : ε / 2 ≤ 3 * s - 3 + ε - 2 * e := by dsimp [s, e]; nlinarith
  obtain ⟨ηC, hηC, dC, hdC, hC'⟩ := hC e he
  obtain ⟨P, hP, hpack⟩ := WangZahlLot.wz_essentially_distinct_tube_count
  obtain ⟨q, hq, d, hd, hbudget⟩ := exists_comparison_budget hε hη hvLoss hP hηC hdC
    hroot hres hlight hremove hretain
  refine ⟨η, hη, d, hd, ?_⟩
  intro δ hδ hδd hδsmall n x v Y hH htrans hF f hf hf0
  exact comparison_from_budget hδ hε hvLoss hq hs hs1 hexp (hbudget δ hδ hδd)
    x v Y hH htrans hF
    (hpack δ hδ hδsmall n x v hH.2.1 hH.2.2.1 hH.2.2.2.1) hf hf0
    (fun τ hτ hτC hτsmall => hC' τ hτ hτC hτsmall f hf hf0)

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
