-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/ConcentratedDensity.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.ConcentratedProperties

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory Metric
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
  (frozen_prism_volume)

noncomputable section

namespace ConcentratedGrainData

variable {ω ζ δ ε b ρ c : ℝ} {p n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}

/-- Retention and balance turn the aggregate grain density into a uniform
lower density on every selected grain. -/
theorem selected_density (D : ConcentratedGrainData ω ζ δ ε b ρ c p n x v Y)
    (hδ : 0 < δ) : ∀ j ∈ D.Q,
    O (δ ^ (21 * ε / 40)) * μ (P D.a (ρ * c) c (D.z j) (D.e j)) ≤ μ (D.Hg j) := by
  classical
  obtain ⟨ha, hρ, -, hc, -⟩ := D.dimensions hδ
  obtain ⟨hfin, hweight, hmass⟩ := grain_real_weights hδ D.grains
  have hQfin : (∑ j ∈ D.Q, μ (D.Hg j)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => hfin j)
  have hkeep := ENNReal.toReal_mono hQfin D.retained
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hδ.le _),
    ENNReal.toReal_sum (fun j _ => hfin j), ENNReal.toReal_sum (fun j _ => hfin j)] at hkeep
  intro j hj
  have hL : (0 : ℝ) < D.L := Nat.cast_pos.mpr j.pos
  have hcard : (D.Q.card : ℝ) ≤ D.L := by
    have hh : D.Q.card ≤ D.L := by simpa only [Fintype.card_fin] using Finset.card_le_univ D.Q
    exact_mod_cast hh
  have hsum := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.comparable_mass_of_card_retention
    D.Q {j} (fun i => (μ (D.Hg i)).toReal) (Finset.singleton_nonempty j)
    (Finset.singleton_subset_iff.mpr hj)
    (Real.rpow_nonneg hδ.le (-(ε / 80))) (Nat.cast_nonneg D.L)
    (fun _ _ => ENNReal.toReal_nonneg) D.balanced (by simpa using hcard)
  simp only [Finset.sum_singleton] at hsum
  have hlo : δ ^ (ε / 4 + ε / 80) *
      (δ ^ (ε / 4) * D.L * (D.a * (ρ * c) * c)) ≤
      δ ^ (-(ε / 80)) * D.L * (μ (D.Hg j)).toReal :=
    (mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hδ.le _)).trans (hkeep.trans hsum)
  have hexp : δ ^ (ε / 4 + ε / 80) * δ ^ (ε / 4) =
      δ ^ (-(ε / 80)) * δ ^ (21 * ε / 40) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    ring
  have hlo' : (δ ^ (-(ε / 80)) * D.L) *
      (δ ^ (21 * ε / 40) * (D.a * (ρ * c) * c)) ≤
      (δ ^ (-(ε / 80)) * D.L) * (μ (D.Hg j)).toReal := by
    calc
      _ = (δ ^ (ε / 4 + ε / 80) * δ ^ (ε / 4)) * D.L *
          (D.a * (ρ * c) * c) := by rw [hexp]; ring
      _ ≤ _ := by nlinarith only [hlo]
  have hpoint := (mul_le_mul_iff_right₀ (mul_pos (Real.rpow_pos_of_pos hδ _) hL)).mp hlo'
  have hv : μ (P D.a (ρ * c) c (D.z j) (D.e j)) = O (D.a * (ρ * c) * c) :=
    frozen_prism_volume ha.le (mul_pos hρ hc).le hc.le _ _
  rw [hv, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
  exact (ENNReal.ofReal_le_ofReal hpoint).trans_eq (ENNReal.ofReal_toReal (hfin j))

end ConcentratedGrainData
end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
