-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ClusterEnclosure.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ClusterEnclosure.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.BoxEnclosure
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedBlocks
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainCoefficient

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (frozen_prism_norm frozen_prism_convex frozen_prism_ends ball_subset_frozen_prism boxAxis_norm)

noncomputable section

/-- Local grain blocks have volume-controlled prism enclosures with a common
long dimension. No hypothesis that a grain is a round tube is needed. -/
theorem grain_block_enclosure {L : ℕ} {a ρ c : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c) (hac : a ≤ ρ * c)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V)
    (Q : Finset (Fin L)) (hQ : Q.Nonempty) (j : Fin L)
    (hnear : ∀ i ∈ Q, grainNear a ρ c z e j i)
    {W : Set V} (hW : Convex ℝ W) (hfin : μ W ≠ ⊤)
    (hcover : ∀ i ∈ Q, P a (ρ * c) c (z i) (e i) ⊆ W) :
    ∃ (A B : ℝ) (i : Fin L) (E : V ≃ₗᵢ[ℝ] V),
      i ∈ Q ∧ 0 < A ∧ A ≤ B ∧ B ≤ 10 * c ∧
      (∀ k ∈ Q, P a (ρ * c) c (z k) (e k) ⊆ P A B (10 * c) (z i) E) ∧
      A * B * (10 * c) ≤ 34560 * (μ W).toReal := by
  have hrc : ρ * c ≤ c := mul_le_of_le_one_left hc.le hρ1
  have hadiv : a / ρ ≤ c := (div_le_iff₀ hρ).mpr (by simpa [mul_comm] using hac)
  have haa : a ≤ a / ρ := (le_div_iff₀ hρ).mpr (by nlinarith)
  let Z := P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j)
  let W' := W ∩ Z
  have hUZ (k : Fin L) (hk : k ∈ Q) : P a (ρ * c) c (z k) (e k) ⊆ Z := by
    apply Subset.trans ?_ (hnear k hk)
    intro p hp
    exact ⟨hp.1.trans (by linarith), hp.2.1.trans (by linarith), hp.2.2⟩
  have hUW (k : Fin L) (hk : k ∈ Q) : P a (ρ * c) c (z k) (e k) ⊆ W' :=
    subset_inter (hcover k hk) (hUZ k hk)
  obtain ⟨i, hi⟩ := hQ
  have hcenter : z i ∈ W' := hUW i hi (by simp only [P, sub_self, map_zero,
    PiLp.zero_apply, abs_zero, mem_ofPred_eq]; exact ⟨by positivity, by positivity, by positivity⟩)
  have hZnorm (p : V) (hp : p ∈ Z) : ‖p - z j‖ ≤ 2 * c := by
    apply frozen_prism_norm (by positivity) (by rw [mul_div_assoc]; linarith)
      le_rfl (z j) (e j) hp
  have hbound : W' ⊆ ball (z i) (5 * c) := by
    intro p hp
    have hh := norm_sub_le (p - z j) (z i - z j)
    rw [sub_sub_sub_cancel_right] at hh
    change ‖p - z i‖ < 5 * c
    linarith [hZnorm p hp.2, hZnorm (z i) hcenter.2]
  have hlong : ∃ p ∈ W', ∃ q ∈ W', c ≤ dist p q := by
    have he := frozen_prism_ends ha.le (mul_pos hρ hc).le hc.le (z i) (e i)
    refine ⟨_, hUW i hi he.1, _, hUW i hi he.2, ?_⟩
    rw [dist_eq_norm, show z i + (c / 2) •
      WangZahlLot.Obl.wz_clustered_cover_volume_gain.boxAxis (e i) 2 -
      (z i - (c / 2) • WangZahlLot.Obl.wz_clustered_cover_volume_gain.boxAxis (e i) 2) =
      c • WangZahlLot.Obl.wz_clustered_cover_volume_gain.boxAxis (e i) 2 by module,
      norm_smul, Real.norm_eq_abs, abs_of_pos hc, boxAxis_norm, mul_one]
  obtain ⟨A, B, E, hA, hAB, hB, hbox, hvol⟩ := convex_enclosure_fixed_length
    (hW.inter (frozen_prism_convex _ _ _ _ _))
    (ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)) (half_pos ha)
    (by positivity : 0 < 5 * c) hc
    ((ball_subset_frozen_prism hac hrc (z i) (e i)).trans (hUW i hi)) hbound hlong
  have hlength : 2 * (5 * c) = 10 * c := by ring
  rw [hlength] at hB hbox hvol
  refine ⟨A, B, i, E, hi, hA, hAB, hB, fun k hk => (hUW k hk).trans hbox, ?_⟩
  have hcoeff : 6912 * (5 * c) / c = (34560 : ℝ) := by field_simp; ring
  rw [hcoeff] at hvol
  exact hvol.trans (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hfin (measure_mono inter_subset_left)) (by norm_num))

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
