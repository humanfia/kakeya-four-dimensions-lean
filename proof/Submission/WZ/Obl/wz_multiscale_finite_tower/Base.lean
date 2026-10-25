-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.Base.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Tower
import Submission.WZ.Obl.wz_multiscale_finite_tower.Cutoff

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The complete depth-zero alternative, including the arbitrary prescribed cutoff. -/
theorem finite_tower_base {σ ω : ℝ} (hE : Endpoint σ ω) (hσ : σ ≤ 1 / 2)
    {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
      ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ n x v Y,
      Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y →
      VolumeBound σ ω κ α d n Y ∨
      (d ≤ D ∧ ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M L : ℝ),
        Admissible d ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
        ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
        Tower false d (d ^ (-ε)) (2 * (1 - ω / 100) ^ (0 : ℕ)) (2 ^ 0) m x' v') := by
  obtain ⟨κ, hκ, η₀, hη₀, hcut⟩ := hE.away_from_zero hσ zero_lt_one hD
  refine ⟨1, zero_lt_one, κ, hκ, min ε η₀, lt_min hε hη₀, ?_⟩
  intro d hd hd100 n x v Y hA
  have hd1 : d < 1 := by linarith
  by_cases hsmall : d ≤ D
  · right
    refine ⟨hsmall, ?_⟩
    simpa only [pow_zero, mul_one] using
      initial_refinement hd hd1 hε.le (min_le_left ε η₀) hA
  · exact Or.inl (hcut d hd hd100 (le_of_not_ge hsmall) n x v Y
      (hA.mono_error hd hd1.le (min_le_right ε η₀)))

end WangZahlLot.Obl.wz_multiscale_finite_tower
