-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ContainedCrossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ContainedCrossing.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0626 5604560, ContainedCrossing.lean.
This is workspace collaboration code; existing local and accepted dependencies are imported. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.GrainCrossing
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.EndTrimming
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BoxCover

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric
open WangZahlLot.Obl.wz_coarse_tube_grains.RIS
  (tube_two_point_error abs_rotated_coord_le)

/-- Two separated points of a fine tube in a slab control its direction,
even when their separation is measured in a different frame. -/
theorem separated_tube_slab_direction {δ a c : ℝ} {x v p q z : V}
    (e : V ≃ₗᵢ[ℝ] V) (i : Fin 3)
    (hδ : 0 < δ) (hδa : δ ≤ a) (hδc : 4 * δ ≤ c) (hv : ‖v‖ = 1)
    (hp : p ∈ T δ x v) (hq : q ∈ T δ x v) (hsep : c ≤ dist p q)
    (hpa : |e (p - z) i| ≤ a / 2) (hqa : |e (q - z) i| ≤ a / 2) :
    |e v i| ≤ 6 * a / c := by
  have hc : 0 < c := by linarith
  obtain ⟨s, _, herr⟩ := tube_two_point_error hp hq
  have hnorm : ‖s • v‖ = |s| := by rw [norm_smul, Real.norm_eq_abs, hv, mul_one]
  have hs : c / 2 ≤ |s| := by
    have hh := norm_le_norm_add_norm_sub (s • v) (p - q)
    rw [norm_sub_rev (s • v), hnorm] at hh
    rw [dist_eq_norm] at hsep
    linarith
  have herror : |e (p - q) i - s * e v i| < 2 * δ := by
    have hh := (abs_rotated_coord_le e ((p - q) - s • v) i).trans_lt herr
    simpa only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using hh
  have hdiff : |e (p - q) i| ≤ a := by
    rw [show p - q = (p - z) - (q - z) by abel, map_sub]
    change |e (p - z) i - e (q - z) i| ≤ a
    exact (abs_sub _ _).trans (by linarith)
  have hmul : |s| * |e v i| ≤ 3 * a := by
    rw [← abs_mul]
    have hh := abs_sub (e (p - q) i) (e (p - q) i - s * e v i)
    rw [sub_sub_cancel] at hh
    linarith
  apply (le_div_iff₀ hc).mpr
  nlinarith [mul_le_mul_of_nonneg_right hs (abs_nonneg (e v i))]

/-- A fine tube crossing an old grain has small transverse components in
any containing prism, with the old length `c` in the denominator. -/
theorem crossing_contained_prism_direction {δ a b c A B ℓ : ℝ}
    {x v z z' : V} (e g : V ≃ₗᵢ[ℝ] V)
    (hδ : 0 < δ) (hδA : δ ≤ A) (hAB : A ≤ B)
    (hδc : 4 * δ ≤ c) (hv : ‖v‖ = 1)
    (hsub : P a b c z e ⊆ P A B ℓ z' g)
    (hcross : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P a b c z e, e (p - z) 2 = t) :
    |g v 0| ≤ 6 * A / c ∧ |g v 1| ≤ 6 * B / c := by
  obtain ⟨p, hp, hpc⟩ := hcross (c / 2) (by simp)
  obtain ⟨q, hq, hqc⟩ := hcross (-c / 2) (by simp)
  have hsep : c ≤ dist p q := by
    have he : e (p - q) 2 = c := by
      rw [show p - q = (p - z) - (q - z) by abel, map_sub]
      change e (p - z) 2 - e (q - z) 2 = c
      rw [hpc, hqc]
      ring
    have hh := abs_rotated_coord_le e (p - q) 2
    rw [he, abs_of_nonneg (by linarith : 0 ≤ c)] at hh
    exact hh
  exact ⟨separated_tube_slab_direction g 0 hδ hδA hδc hv hp.1 hq.1 hsep
      (hsub hp.2).1 (hsub hq.2).1,
    separated_tube_slab_direction g 1 hδ (hδA.trans hAB) hδc hv hp.1 hq.1 hsep
      (hsub hp.2).2.1 (hsub hq.2).2.1⟩

/-- A small transverse bound in an orthogonal frame leaves a definite
long component. -/
theorem long_component_of_transverse {A B c : ℝ} {v : V}
    (g : V ≃ₗᵢ[ℝ] V) (hc : 0 < c) (hAB : A ≤ B) (hBc : 24 * B ≤ c)
    (hv : ‖v‖ = 1) (h0 : |g v 0| ≤ 6 * A / c) (h1 : |g v 1| ≤ 6 * B / c) :
    1 / 2 ≤ |g v 2| := by
  have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.norm_le_coord_sum (g v)
  rw [g.norm_map, hv] at hh
  have hsmall : 6 * A / c + 6 * B / c ≤ (1 / 2 : ℝ) := by
    rw [← add_div, div_le_iff₀ hc]
    linarith
  linarith

/-- Crossing a retained old grain inside a narrow container gives exact
crossing of a wider prism of the SAME prescribed length, whenever the
retained point lies in its core and avoids the fine-tube ends. -/
theorem wider_prism_crossing_of_contained_grain {δ a b c A B ℓ : ℝ}
    {x v z z' z'' q : V} (e g : V ≃ₗᵢ[ℝ] V)
    (hδ : 0 < δ) (hδA : δ ≤ A) (hAB : A ≤ B)
    (hδc : 16 * δ ≤ c) (hBc : 128 * B ≤ c) (hv : ‖v‖ = 1)
    (hsub : P a b c z e ⊆ P A B ℓ z' g)
    (hcross : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P a b c z e, e (p - z) 2 = t)
    (hq : q ∈ (T δ x v \ WangZahlLot.Obl.wz_coarse_tube_grains.RIS.tubeEnds δ c x v) ∩
      P (16 * A) (16 * B) (c / 8) z'' g) :
    (∀ p ∈ T δ x v ∩ frontier (P (128 * A) (128 * B) c z'' g),
      |g (p - z'') 2| = c / 2) ∧
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ x v ∩ P (128 * A) (128 * B) c z'' g, g (p - z'') 2 = t := by
  have hc : 0 < c := by linarith
  have hA : 0 < A := hδ.trans_le hδA
  have hB : 0 < B := hA.trans_le hAB
  obtain ⟨h0, h1⟩ := crossing_contained_prism_direction e g hδ hδA hAB
    (by linarith) hv hsub hcross
  apply WangZahlLot.Obl.wz_coarse_tube_grains.RIS.Interfaces.prism_crossing_of_core_point
    (q := q) g hδ (by linarith) (by linarith) hδc
    (long_component_of_transverse g hc hAB (by linarith) hv h0 h1) ?_ ?_ ?_
  · have H := (le_div_iff₀ hc).mp h0
    nlinarith
  · have H := (le_div_iff₀ hc).mp h1
    nlinarith
  · change q ∈ (T δ x v \ WangZahlLot.Obl.wz_coarse_tube_grains.RIS.tubeEnds δ c x v) ∩
      P ((128 * A) / 8) ((128 * B) / 8) (c / 8) z'' g
    simpa only [show (128 * A) / 8 = 16 * A by ring,
      show (128 * B) / 8 = 16 * B by ring] using hq

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
