-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.StrongBase.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Strong
import Submission.WZ.Obl.wz_multiscale_finite_tower.UniformLocal

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- On a compact scale interval elementary shading density implies any fixed power bound. -/
theorem elementary_away_from_zero {σ ω α D : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 ≤ ω) (hα : 0 < α) (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ d η : ℝ, 0 < d → d ≤ 1 → D ≤ d → η ≤ 1 →
    ∀ n x v Y, Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y →
      VolumeBound σ ω κ α d n Y := by
  let κ : ℝ := (1 / 16) * (min D 1) ^ (5 + α)
  have hκ : 0 < κ := mul_pos (by norm_num) (Real.rpow_pos_of_pos (lt_min hD zero_lt_one) _)
  refine ⟨κ, hκ, ?_⟩
  intro d η hd hd1 hDd hη n x v Y hA
  have hF : FrameAdmissible d d 1 n x v Y := (hA.mono_error hd hd1 hη)
  have hv := hF.small_gap hd hd1 hd hd1 hσ hσ1 hω
    (h := 1) (loss := 5) (by simp) (by norm_num)
  have hp : (min D 1) ^ (5 + α) ≤ d ^ (5 + α) :=
    Real.rpow_le_rpow (le_min hD.le zero_le_one) ((min_le_left _ _).trans hDd) (by linarith)
  apply le_trans (ENNReal.ofReal_le_ofReal _) hv
  have he : κ * d ^ (ω - α) ≤ (1 / 16 : ℝ) * d ^ (5 : ℝ) * d ^ ω := by
    calc
      _ ≤ ((1 / 16 : ℝ) * d ^ (5 + α)) * d ^ (ω - α) := by dsimp [κ]; gcongr
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hd, mul_assoc, ← Real.rpow_add hd]
        congr 2
        ring
  dsimp [volumeFactor]
  calc
    κ * d ^ (ω - α) * (n * d ^ 2) * (n * d) ^ (-σ) ≤
        ((1 / 16 : ℝ) * d ^ (5 : ℝ) * d ^ ω) * (n * d ^ 2) * (n * d) ^ (-σ) := by gcongr
    _ = _ := by ring

/-- The strengthened depth-zero alternative, including relative slab estimates in the root. -/
theorem strong_depth_zero {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2) (hω : 0 ≤ ω)
    (ε D : ℝ) (hε : 0 < ε) (hD : 0 < D) :
    ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧
    ∀ d : ℝ, 0 < d → d ≤ 1 / 100 → ∀ n x v Y,
      Admissible d η (d ^ (-η)) (d ^ (-η)) n x v Y →
      VolumeBound σ ω κ α d n Y ∨ (d ≤ D ∧
      ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M L : ℝ),
      Admissible d ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
      ENNReal.ofReal (d ^ ε) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
      StrongTower d (d ^ (-ε)) 1 1 m x' v') := by
  obtain ⟨d₀, hd₀, hd₀D, hsmall⟩ := exists_scale_cutoff (1 / 4096) (ε / 2) D
    (by norm_num) (by positivity) hD
  obtain ⟨κ, hκ, hcompact⟩ := elementary_away_from_zero hσ hσ1 hω zero_lt_one hd₀
  let η : ℝ := min 1 (ε / 2)
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / 2 := min_le_right _ _
  refine ⟨1, zero_lt_one, κ, hκ, η, hη, ?_⟩
  intro d hd hd100 n x v Y hA
  have hd1 : d < 1 := by linarith
  rcases le_total d₀ d with hcut | hcut
  · exact Or.inl (hcompact d η hd hd1.le hcut hη1 n x v Y hA)
  · have hA' := hA.mono_error hd hd1.le (show η ≤ ε by linarith)
    refine Or.inr ⟨hcut.trans hd₀D, n, x, v, Y, d ^ (-ε), d ^ (-ε), hA', Set.Subset.rfl, ?_, ?_⟩
    · exact mul_le_of_le_one_left (by positivity)
        (ENNReal.ofReal_le_one.mpr (Real.rpow_le_one hd.le hd1.le hε.le))
    · have hC : (4096 : ℝ) ≤ d ^ (-(ε / 2)) := by
        rw [Real.rpow_neg hd.le, inv_eq_one_div]
        apply (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
        have hs := hsmall d hd hcut
        linarith
      have hL : 4096 * d ^ (-η) ≤ d ^ (-ε) := by
        calc
          4096 * d ^ (-η) ≤ d ^ (-(ε / 2)) * d ^ (-η) :=
            mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hd.le _)
          _ = d ^ (-(ε / 2) + -η) := (Real.rpow_add hd _ _).symm
          _ ≤ d ^ (-ε) := Real.rpow_le_rpow_of_exponent_ge hd hd1.le (by linarith)
      exact strong_tower_one hd hd1 le_rfl hA.1 (fun i => (hA.2.1 i).1)
        (fun i => (hA.2.1 i).2.1) hA'.2.2.2.2.1 hA.2.2.2.2.2 hL

end WangZahlLot.Obl.wz_multiscale_finite_tower
