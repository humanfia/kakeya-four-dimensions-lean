-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.LocalCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorDyadic

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory

/-- Equal-volume finite families have an unrestricted local count coefficient.
The counting predicate may impose any additional condition on the index. -/
theorem finite_uniform_volume_count {V : Type*} [MeasurableSpace V]
    (μ : Measure V) {L : ℕ} (U : Fin L → Set V) {v : ℝ}
    (hv : 0 ≤ v) (hvol : ∀ j, ENNReal.ofReal v ≤ μ (U j))
    (R : Fin L → Prop) (W : Set V) :
    ENNReal.ofReal (({j | R j ∧ U j ⊆ W}.ncard : ℝ) * v) ≤
      ENNReal.ofReal (max 1 (L : ℝ)) * μ W := by
  classical
  by_cases h : ({j | R j ∧ U j ⊆ W} : Set (Fin L)).Nonempty
  · obtain ⟨j, hjR, hjW⟩ := h
    have hn : ({j | R j ∧ U j ⊆ W}.ncard : ℝ) ≤ max 1 (L : ℝ) := by
      apply le_trans _ (le_max_right _ _)
      have hh := Set.ncard_le_card ({j | R j ∧ U j ⊆ W} : Set (Fin L))
      simp only [Nat.card_fin] at hh
      exact_mod_cast hh
    calc
      _ = ENNReal.ofReal ({j | R j ∧ U j ⊆ W}.ncard : ℝ) * ENNReal.ofReal v :=
        ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (max 1 (L : ℝ)) * μ W :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hn) ((hvol j).trans (measure_mono hjW))
  · have hempty : ({j | R j ∧ U j ⊆ W} : Set (Fin L)) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp only [hempty, Set.ncard_empty, Nat.cast_zero, zero_mul, ENNReal.ofReal_zero]
    exact zero_le

/-- The arbitrary positive coefficient in the initial grains state requires
only the volume of each grain, with no geometric nonconcentration input. -/
theorem initial_local_grain_count {L : ℕ} {a ρ c : ℝ}
    (ha : 0 ≤ a) (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (z : Fin L → LeanEval.Analysis.WangZahlKakeya.Space)
    (e : Fin L → LeanEval.Analysis.WangZahlKakeya.Space ≃ₗᵢ[ℝ]
      LeanEval.Analysis.WangZahlKakeya.Space) :
    ∃ g : ℝ, 0 < g ∧ ∀ j W, Convex ℝ W →
      ENNReal.ofReal
        (({j' | wz_clustered_cover_volume_gain.Parent.Factor.box (a / ρ) c c (z j') (e j') ⊆
          wz_clustered_cover_volume_gain.Parent.Factor.box (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
          wz_clustered_cover_volume_gain.Parent.Factor.box a (ρ * c) c (z j') (e j') ⊆ W}.ncard : ℝ) *
          (a * (ρ * c) * c)) ≤ ENNReal.ofReal g * volume W := by
  refine ⟨max 1 (L : ℝ), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro j W _
  apply finite_uniform_volume_count volume
    (fun j' => wz_clustered_cover_volume_gain.Parent.Factor.box a (ρ * c) c (z j') (e j'))
    (by positivity)
  intro j'
  exact (wz_clustered_cover_volume_gain.Parent.Factor.box_volume ha (mul_nonneg hρ hc) hc
    (z j') (e j')).symm.le

end WangZahlLot.Obl.wz_broad_grains_initialization
