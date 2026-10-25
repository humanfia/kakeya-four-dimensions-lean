-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.CappedPrismWidth.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/CappedPrismWidth.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Core
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BallDensity
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

/-!
# Dense prisms under an all-radius density cap are thin

Ported, with its namespace and import adjusted, from session x0551's
`WangZahlLot/Obl/wz_move_three_wide_grains_core/CappedPrismWidth.lean`
(o169 repository, commit 9d63190, workspace code, not accepted). Used for the
thin-or-gain alternative of pulled-back label boxes (WZ Lemma 8.3, Step 13).
-/

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (ball_density_mass_in_box frozen_prism_box frozen_prism_compact frozenBasis)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (orthogonalBox volume_orthogonalBox)

/-- A local ambient density cap bounds the density of every contained prism,
at any positive radius that fits its short side. -/
theorem dense_prism_ball_bound {a b c r D lam : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (hr : 0 < r) (hra : r ≤ a / 2)
    (hlam : 0 ≤ lam) (z : V) (e : V ≃ₗᵢ[ℝ] V) (H Γ : Set V)
    (hHP : H ⊆ P a b c z e) (hHΓ : H ⊆ Γ)
    (hden : O (D * (a * b * c)) ≤ μ H)
    (hcap : ∀ p ∈ H, μ (Γ ∩ ball p r) ≤ O (lam * r ^ 3)) :
    D ≤ 512 * lam := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hTB : TotallyBounded H := (frozen_prism_compact ha.le hab hbc z e).totallyBounded.subset hHP
  have hbox : H ⊆ orthogonalBox ![a / 2, b / 2, c / 2] z (frozenBasis e) := by
    simpa only [← frozen_prism_box] using hHP
  have HH := ball_density_mass_in_box hr hTB hHΓ ![a / 2, b / 2, c / 2]
    z (frozenBasis e) hbox hcap
  have hsub : orthogonalBox (fun j => (![a / 2, b / 2, c / 2] : Fin 3 → ℝ) j + r)
      z (frozenBasis e) ⊆ orthogonalBox ![a, b, c] z (frozenBasis e) := by
    intro p hp j
    have hj := hp j
    fin_cases j <;> norm_num at hj ⊢ <;> linarith
  have hupper : μ H ≤ O (512 * lam * (a * b * c)) := by
    apply HH.trans ((mul_le_mul' le_rfl (measure_mono hsub)).trans_eq ?_)
    rw [volume_orthogonalBox]
    · rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 64 * lam)]
      congr 1
      norm_num [Fin.prod_univ_three]
      ring
    · intro j
      fin_cases j <;> simp <;> positivity
  have hscalar := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 512 * lam * (a * b * c))).mp
    (hden.trans hupper)
  exact (mul_le_mul_iff_left₀ (show 0 < a * b * c by positivity)).mp hscalar

/-- Uniformly below a cutoff, an ambient all-radius density cap prevents an
individually dense prism from having a large short side. This applies before
assembling any exact grain-cover predicate. -/
theorem capped_dense_prism_short {s t h jump : ℝ} (hs : 0 < s)
    (hbudget : t + h < jump * s) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d₀ →
      ∀ (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) (H Γ : Set V),
      0 < a → a ≤ b → b ≤ c → c ≤ 1 → H ⊆ P a b c z e → H ⊆ Γ →
      O (δ ^ h * (a * b * c)) ≤ μ H →
      (∀ p ∈ Γ, ∀ r : ℝ, 0 < r → r ≤ 1 →
        μ (Γ ∩ ball p r) ≤ O (δ ^ (-t) * (δ / r) ^ s * r ^ 3)) →
      a < δ ^ (1 - jump) := by
  have hp : 0 < jump * s - t - h := by linarith
  obtain ⟨d, hd, Hd⟩ := WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
    hp (by positivity : 0 < 1 / (1024 * (2 : ℝ) ^ s))
  refine ⟨min d 1, lt_min hd one_pos, min_le_right _ _, ?_⟩
  intro δ hδ hδd a b c z e H Γ ha hab hbc hc1 hHP hHΓ hden hcap
  by_contra hfail
  have hlarge : δ ^ (1 - jump) ≤ a := le_of_not_gt hfail
  have Hbound := dense_prism_ball_bound ha hab hbc
    (by positivity : 0 < a / 2) le_rfl
    (by positivity : 0 ≤ δ ^ (-t) * (δ / (a / 2)) ^ s) z e H Γ hHP hHΓ hden
    (fun p hp => hcap p (hHΓ hp) (a / 2) (by positivity) (by linarith))
  have hratio : δ / a ≤ δ ^ jump := by
    calc
      δ / a ≤ δ / δ ^ (1 - jump) := div_le_div_of_nonneg_left hδ.le (Real.rpow_pos_of_pos hδ _) hlarge
      _ = δ ^ jump := by
        calc
          _ = δ ^ (1 : ℝ) / δ ^ (1 - jump) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_sub hδ]; congr 1; ring
  have hscale : (δ / (a / 2)) ^ s ≤ (2 : ℝ) ^ s * δ ^ (jump * s) := by
    calc
      _ = (2 : ℝ) ^ s * (δ / a) ^ s := by rw [show δ / (a / 2) = 2 * (δ / a) by ring, Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ (2 : ℝ) ^ s * (δ ^ jump) ^ s := by gcongr
      _ = _ := by rw [← Real.rpow_mul hδ.le]
  have hsimpl : δ ^ h ≤ (512 * (2 : ℝ) ^ s) * δ ^ (jump * s - t) := by
    calc
      _ ≤ 512 * (δ ^ (-t) * (δ / (a / 2)) ^ s) := Hbound
      _ ≤ 512 * (δ ^ (-t) * ((2 : ℝ) ^ s * δ ^ (jump * s))) := by gcongr
      _ = _ := by rw [Real.rpow_sub hδ, Real.rpow_neg hδ.le]; ring
  have Hsmall := Hd δ hδ (hδd.trans (min_le_left _ _))
  have hcst : (512 * (2 : ℝ) ^ s) * δ ^ (jump * s - t - h) ≤ 1 / 2 := by
    have HH := (le_div_iff₀ (by positivity : 0 < 1024 * (2 : ℝ) ^ s)).mp Hsmall
    nlinarith only [HH]
  have hfactor : δ ^ (jump * s - t) = δ ^ (jump * s - t - h) * δ ^ h := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  rw [hfactor] at hsimpl
  have HH := mul_le_mul_of_nonneg_right hcst (Real.rpow_pos_of_pos hδ h).le
  have Hpos := Real.rpow_pos_of_pos hδ h
  nlinarith only [hsimpl, HH, Hpos]

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
