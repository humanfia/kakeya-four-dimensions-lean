-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.CountComparison.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Basic
import Submission.WZ.Obl.wz_rescaled_fibre_alternatives.ConvexEnlargement

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_rescaled_fibre_alternatives
  (ConvexCount convexExpansionLoss convexExpansionLoss_pos convex_enlargement)

/-- Convex counts pass to replacement bodies when each old body lies in a fixed
dilation of its replacement about a point of the replacement. -/
theorem convex_count_of_expansions {r s A C L R : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hL : 0 ≤ L) (hscale : s ^ 2 ≤ A * r ^ 2)
    {n : ℕ} (P : Fin n → Prop) (U V : Fin n → Set Space) (p : Fin n → Space)
    (hopen : ∀ i, P i → IsOpen (U i)) (hbound : ∀ i, P i → U i ⊆ ball 0 R)
    (hp : ∀ i, P i → p i ∈ U i)
    (hexpand : ∀ i, P i → V i ⊆ AffineMap.homothety (p i) C '' U i)
    (hK : ConvexCount r L P V) :
    ConvexCount s (A * L * convexExpansionLoss C) P U := by
  classical
  intro W hW
  let I : Set (Fin n) := {i | P i ∧ U i ⊆ W}
  rcases I.eq_empty_or_nonempty with hI | ⟨i₀, hi₀⟩
  · change ENNReal.ofReal ((I.ncard : ℝ) * s ^ 2) ≤ _
    simp [hI]
  let W₀ := interior W ∩ ball (0 : Space) R
  have hUi : ∀ i ∈ I, U i ⊆ W₀ := by
    intro i hi
    exact subset_inter ((hopen i hi.1).subset_interior_iff.mpr hi.2) (hbound i hi.1)
  have hW₀ : Convex ℝ W₀ := hW.interior.inter (convex_ball _ _)
  have hW₀o : IsOpen W₀ := isOpen_interior.inter isOpen_ball
  have hW₀b : Bornology.IsBounded W₀ := isBounded_ball.subset inter_subset_right
  have hW₀ne : W₀.Nonempty := ⟨p i₀, hUi i₀ hi₀ (hp i₀ hi₀.1)⟩
  obtain ⟨W', hW', hexp, hvol⟩ := convex_enlargement hW₀ hW₀o hW₀b hW₀ne hC
  have hcount : I.ncard ≤ {i | P i ∧ V i ⊆ W'}.ncard := by
    apply Set.ncard_mono
    intro i hi
    refine ⟨hi.1, (hexpand i hi.1).trans ?_⟩
    exact (image_mono (hUi i hi)).trans (hexp (p i) (hUi i hi (hp i hi.1)))
  have hWsub : W₀ ⊆ W := inter_subset_left.trans interior_subset
  have hcountscale : (I.ncard : ℝ) * s ^ 2 ≤ A * ((I.ncard : ℝ) * r ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg I.ncard)]
  change ENNReal.ofReal ((I.ncard : ℝ) * s ^ 2) ≤ _
  calc
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal ((I.ncard : ℝ) * r ^ 2) := by
      rw [← ENNReal.ofReal_mul hA]
      exact ENNReal.ofReal_le_ofReal hcountscale
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal (({i | P i ∧ V i ⊆ W'}.ncard : ℝ) * r ^ 2) := by
      gcongr
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal L * volume W') := mul_le_mul' le_rfl (hK W' hW')
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal L *
        (ENNReal.ofReal (convexExpansionLoss C) * volume W₀)) := by gcongr
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal L *
        (ENNReal.ofReal (convexExpansionLoss C) * volume W)) := by
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (measure_mono hWsub)))
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hA,
        ← ENNReal.ofReal_mul (mul_nonneg hA hL)]

end WangZahlLot.Obl.wz_multiscale_finite_tower
