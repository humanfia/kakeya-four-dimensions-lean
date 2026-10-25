-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.LocalStability.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/LocalStability.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.LocalCoefficient
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.StableSelection

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open MeasureTheory

noncomputable section

/-- Power-scale weighted stability for local convex counts of bodies with a
common volume lower bound. The weights can be their shading volumes. -/
theorem stable_local_family_power {ν : ℝ} (hν : 0 < ν) :
    ∃ (p : ℕ) (d : ℝ), 0 < p ∧ 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      δ ≤ 1 / 2 ∧
      ∀ (κ : Type) [DecidableEq κ] (S : Finset κ)
        (U : κ → Set V) (vol : ℝ) (near : κ → κ → Prop)
        (weight : κ → ℝ) (A : ℝ),
      0 ≤ vol → (∀ i ∈ S, O vol ≤ μ (U i)) → 0 < A →
      (∀ i ∈ S, 0 ≤ weight i ∧ weight i ≤ A) →
      0 < ∑ i ∈ S, weight i →
      δ ^ 2 * A * S.card ≤ (∑ i ∈ S, weight i) / 2 →
      (S.card : ℝ) ≤ δ ^ (-(6 : ℝ)) →
      ∃ Q : Finset κ, Q ⊆ S ∧ Q.Nonempty ∧
        δ ^ (ν + ν / 20) * (∑ i ∈ S, weight i) ≤ ∑ i ∈ Q, weight i ∧
        (∀ i ∈ Q, ∀ j ∈ Q, weight i ≤ δ ^ (-(ν / 20)) * weight j) ∧
        (∀ R ⊆ Q, (Q.card : ℝ) ≤ 2 * R.card →
          localCoefficient U vol near Q ≤ 2 ^ p * localCoefficient U vol near R) := by
  obtain ⟨p, d, hp, hd, hparams⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.stable_selection_parameters
      hν (C := 1) (by norm_num)
  refine ⟨p, d, hp, hd, ?_⟩
  intro δ hδ hδd
  obtain ⟨hhalf, _, hsmall, hgrid, hnorm, _⟩ := hparams δ hδ hδd
  refine ⟨hhalf, ?_⟩
  intro κ _ S U vol near weight A hvol hU hA hweight hmass htail hcard
  have hδ1 : δ ≤ 1 := by linarith
  have hcoef : ∀ R ⊆ S, R.Nonempty →
      1 ≤ localCoefficient U vol near R ∧
      localCoefficient U vol near R ≤ δ ^ (-(6 : ℝ)) := by
    intro R hRS _
    refine ⟨one_le_localCoefficient U vol near R, ?_⟩
    apply (localCoefficient_le_card U near R hvol (fun i hi => hU i (hRS hi))).trans
    apply max_le
    · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by norm_num)
    · exact (Nat.cast_le.mpr (Finset.card_le_card hRS)).trans hcard
  obtain ⟨Q, hQS, hQne, hkeep, hbal, hstable⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.weighted_stable_subfamily
      S weight (localCoefficient U vol near) hA (sq_pos_of_pos hδ)
      (by nlinarith) (by
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith))
      (fun i hi => (hweight i hi).2) hmass htail (2 * p) p hp hgrid
      (Real.rpow_nonneg hδ.le _) hcoef hsmall
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hkeep
  have hQmass : 0 ≤ ∑ i ∈ Q, weight i :=
    Finset.sum_nonneg fun i hi => (hweight i (hQS hi)).1
  refine ⟨Q, hQS, hQne, ?_, hbal, hstable⟩
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hδ (ν / 20))).mp
  calc
    _ = δ ^ (ν + ν / 20) * (δ ^ (ν / 20) * ∑ i ∈ S, weight i) := by ring
    _ ≤ δ ^ (ν + ν / 20) *
        (2 * δ ^ (-(ν / 20)) * (2 * p + 1 : ℝ) * ∑ i ∈ Q, weight i) :=
      mul_le_mul_of_nonneg_left hkeep (Real.rpow_nonneg hδ.le _)
    _ = (δ ^ (ν + ν / 20) * (2 * δ ^ (-(ν / 20)) * (2 * p + 1 : ℝ))) *
        ∑ i ∈ Q, weight i := by ring
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hnorm hQmass

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
