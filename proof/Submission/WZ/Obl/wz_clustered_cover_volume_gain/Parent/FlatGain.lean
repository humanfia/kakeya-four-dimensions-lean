-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.FlatGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.Arithmetic

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

/-- The scalar alternative in Section 9 Step 2: the flat-prism gain either
already supplies the desired improvement, or the factoring prisms are almost tubes. -/
theorem flat_prism_gain_or_almost_tube {δ a b σ ω ε α t κ : ℝ} {n : ℕ}
    {V : ENNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a)
    (hω : 0 ≤ ω) (hκ : 0 ≤ κ) (hbudget : ε + α ≤ t * ω)
    (hvol : ENNReal.ofReal
      (κ * δ ^ (ω + ε) * (b / a) ^ ω * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ V) :
    ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ V ∨
      δ ^ t * b ≤ a := by
  by_cases hshape : δ ^ t * b ≤ a
  · exact Or.inr hshape
  · have hr : δ ^ (-t) ≤ b / a := by
      apply (le_div_iff₀ ha).mpr
      calc
        δ ^ (-t) * a ≤ δ ^ (-t) * (δ ^ t * b) :=
          mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hshape))
            (Real.rpow_nonneg hδ.le _)
        _ = b := by
          rw [← mul_assoc, ← Real.rpow_add hδ]
          simp
    have hp : δ ^ (ω - α) ≤ δ ^ (ω + ε) * (b / a) ^ ω := by
      calc
        _ ≤ δ ^ (ω + ε - t * ω) :=
          Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        _ = δ ^ (ω + ε) * (δ ^ (-t)) ^ ω := by
          rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Real.rpow_nonneg hδ.le _) hr hω)
          (Real.rpow_nonneg hδ.le _)
    exact Or.inl ((ENNReal.ofReal_le_ofReal (by
      calc
        _ ≤ (κ * (δ ^ (ω + ε) * (b / a) ^ ω)) * (n * δ ^ 2) *
            (n * δ) ^ (-σ) := by gcongr
        _ = _ := by ring)).trans hvol)

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
