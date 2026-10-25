-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_grains_assembly.LocalCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_grains_assembly.Defs
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGeometry

/-!
# The local convex count of `H` is free

The last clause of `H` bounds, for every grain `j` and convex `W`, the number of grains
`j'` with `U j' ⊆ W` (among those near `j`) by `g μ(W) / (a (ρ c) c)`.  Since a box
`P a (ρ c) c` has volume `a (ρ c) c`, the clause holds with `g = max 1 L`.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_grains_assembly

open MeasureTheory

theorem P_eq_Box (a b c : ℝ) (z : V) (e : V ≃ₗᵢ[ℝ] V) :
    P a b c z e = WangZahlLot.Obl.wz_two_scale_flat_box_estimate.Box a b c z e := rfl

theorem volume_P {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (z : V)
    (e : V ≃ₗᵢ[ℝ] V) : μ (P a b c z e) = O (a * b * c) :=
  WangZahlLot.Obl.wz_two_scale_flat_box_estimate.box_volume ha hb hc z e

/-- The local convex-count clause of `H` with coefficient `g = max 1 L`. -/
theorem local_count_of_le {L : ℕ} {a ρ c g : ℝ} (ha : 0 ≤ a) (hρc : 0 ≤ ρ * c) (hc : 0 ≤ c)
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (hg : (L : ℝ) ≤ g) :
    ∀ j W, Convex ℝ W →
      O (q L {j' | P (a/ρ) c c (z j') (e j') ⊆ P (2*a/ρ) (2*c) (2*c) (z j) (e j) ∧
        P a (ρ*c) c (z j') (e j') ⊆ W} * (a*(ρ*c)*c)) ≤ O g * μ W := by
  intro j W hW
  set s := {j' | P (a/ρ) c c (z j') (e j') ⊆ P (2*a/ρ) (2*c) (2*c) (z j) (e j) ∧
    P a (ρ*c) c (z j') (e j') ⊆ W} with hs
  have hvol : 0 ≤ a * (ρ * c) * c := by positivity
  by_cases hne : s.Nonempty
  · obtain ⟨j', hj'⟩ := hne
    have hW' : O (a * (ρ * c) * c) ≤ μ W := by
      rw [← volume_P ha hρc hc (z j') (e j')]
      exact measure_mono hj'.2
    have hq : q L s ≤ L := by
      show (s.ncard : ℝ) ≤ L
      have h1 : s.ncard ≤ (Set.univ : Set (Fin L)).ncard := Set.ncard_le_ncard (Set.subset_univ s)
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
      exact_mod_cast h1
    have hq0 : 0 ≤ q L s := Nat.cast_nonneg _
    calc O (q L s * (a * (ρ * c) * c))
        = O (q L s) * O (a * (ρ * c) * c) := ENNReal.ofReal_mul hq0
      _ ≤ O g * μ W := by
        gcongr
        exact ENNReal.ofReal_le_ofReal (hq.trans hg)
  · have hs0 : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have : q L s = 0 := by
      show (s.ncard : ℝ) = 0
      rw [hs0, Set.ncard_empty, Nat.cast_zero]
    rw [this, zero_mul]
    show ENNReal.ofReal 0 ≤ _
    rw [ENNReal.ofReal_zero]
    exact zero_le

end WangZahlLot.Obl.wz_coarse_grains_assembly
