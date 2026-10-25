-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.GrainStability.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/GrainStability.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.LocalStability
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainCoefficient
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.GrainMass

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (frozen_prism_volume)

noncomputable section

/-- Uniform stable selection of the frozen grains. The cutoff and stability
power are independent of both the fine and grain cardinalities. -/
theorem stable_grain_selection {ν : ℝ} (hν : 0 < ν) :
    ∃ (p : ℕ) (d : ℝ), 0 < p ∧ 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
      δ ≤ 1 / 2 ∧
      ∀ (h ρ a c b g : ℝ) (n N L : ℕ) (x v : Fin n → V)
        (S : Finset (Fin n)) (Z : Fin n → Set V) (y w : Fin N → V)
        (f : Fin n → Fin N) (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V)
        (Hg : Fin L → Set V) (γ : Fin L → Fin N) (m : ℝ),
      h ≤ 1 → 0 < L → (L : ℝ) ≤ δ ^ (-(6 : ℝ)) →
      GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hg γ m →
      ∃ Q : Finset (Fin L), Q.Nonempty ∧
        O (δ ^ (ν + ν / 20)) * ∑ j, μ (Hg j) ≤ ∑ j ∈ Q, μ (Hg j) ∧
        (∀ i ∈ Q, ∀ j ∈ Q,
          (μ (Hg i)).toReal ≤ δ ^ (-(ν / 20)) * (μ (Hg j)).toReal) ∧
        (∀ R ⊆ Q, (Q.card : ℝ) ≤ 2 * R.card →
          grainCoefficient a ρ c z e Q ≤ 2 ^ p * grainCoefficient a ρ c z e R) := by
  obtain ⟨p, d, hp, hd, H⟩ := stable_local_family_power hν
  refine ⟨p, d, hp, hd, ?_⟩
  intro δ hδ hδd
  obtain ⟨hhalf, Hδ⟩ := H δ hδ hδd
  refine ⟨hhalf, ?_⟩
  intro h ρ a c b g n N L x v S Z y w f z e Hg γ m hh hL hcard hG
  have ha : 0 < a := hδ.trans_le hG.1
  have hrc : 0 < ρ * c := ha.trans_le hG.2.1
  have hc : 0 < c := hrc.trans_le hG.2.2.1
  have hvol : 0 < a * (ρ * c) * c := by positivity
  obtain ⟨hfin, hweight, hmass⟩ := grain_real_weights hδ hG
  have hLreal : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hmasspos : 0 < ∑ j, (μ (Hg j)).toReal :=
    (by positivity : 0 < δ ^ h * L * (a * (ρ * c) * c)).trans_le hmass
  have hδ1 : δ ≤ 1 := by linarith
  have hδh : δ ≤ δ ^ h := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hh
  have htailfactor : 2 * δ ^ 2 ≤ δ ^ h := by nlinarith
  have htail : δ ^ 2 * (a * (ρ * c) * c) * L ≤
      (∑ j, (μ (Hg j)).toReal) / 2 := by
    have hprod := mul_le_mul_of_nonneg_right htailfactor
      (show 0 ≤ L * (a * (ρ * c) * c) by positivity)
    nlinarith
  obtain ⟨Q, _, hQ, hkeep, hbal, hstable⟩ := Hδ (Fin L) Finset.univ
    (fun j => P a (ρ * c) c (z j) (e j)) (a * (ρ * c) * c)
    (grainNear a ρ c z e) (fun j => (μ (Hg j)).toReal) (a * (ρ * c) * c)
    hvol.le (fun j _ => (frozen_prism_volume ha.le hrc.le hc.le (z j) (e j)).ge)
    hvol (fun j _ => hweight j) hmasspos (by simpa using htail) (by simpa using hcard)
  refine ⟨Q, hQ, ?_, hbal, hstable⟩
  have hall : ∑ j, (μ (Hg j)).toReal = (∑ j, μ (Hg j)).toReal :=
    (ENNReal.toReal_sum (fun j _ => hfin j)).symm
  have hsel : ∑ j ∈ Q, (μ (Hg j)).toReal = (∑ j ∈ Q, μ (Hg j)).toReal :=
    (ENNReal.toReal_sum (fun j _ => hfin j)).symm
  have hallfin : (∑ j, μ (Hg j)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun j _ => hfin j)
  have hselfin : (∑ j ∈ Q, μ (Hg j)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun j _ => hfin j)
  have hkeep' := ENNReal.ofReal_le_ofReal hkeep
  rwa [hall, hsel, ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _),
    ENNReal.ofReal_toReal hallfin, ENNReal.ofReal_toReal hselfin] at hkeep'

end
end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
