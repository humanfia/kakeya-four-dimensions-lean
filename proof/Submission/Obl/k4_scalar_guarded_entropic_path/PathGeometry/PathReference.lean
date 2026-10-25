/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/PathReference.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ChainBudgets

/-! The probability of an actual finite scalar path is dominated by its
original world mixture with an explicit subpower density factor. This factor
is measured on each fixed exact sequence before choosing an outer diagonal. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

def normalizedWorldMixture (p : Code) (k : ℕ) : Measure (Fin (W p k) × State) :=
  (worldMixture p k univ)⁻¹ • worldMixture p k

theorem normalizedWorldMixture_isProbability {p : Code} (hp : Exact p) (k : ℕ) :
    IsProbabilityMeasure (normalizedWorldMixture p k) := by
  have hm : 0 < worldMixture p k univ := by
    have hK : 0 < K p k := lt_of_lt_of_le zero_lt_one (hp.1.2.2.1.1 k)
    exact (ENNReal.ofReal_pos.mpr (inv_pos.mpr hK)).trans_le (worldMixture_mass_lower hp k)
  rw [isProbabilityMeasure_iff, normalizedWorldMixture, Measure.smul_apply]
  exact ENNReal.inv_mul_cancel hm.ne' ((worldMixture_mass_le_one hp k).trans_lt (by simp)).ne

namespace RefinementChain

def referenceFactor {p z : Code} (chain : RefinementChain p z) (k : ℕ) : ℝ :=
  ((chain.originalLaw k univ).toReal)⁻¹

theorem originalLaw_mass_toReal_pos {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) : 0 < (chain.originalLaw k univ).toReal :=
  ENNReal.toReal_pos_iff.mpr ⟨chain.originalLaw_mass_pos hz k,
    (chain.originalLaw_mass_le_one hz k).trans_lt (by simp)⟩

theorem referenceFactor_one_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) : 1 ≤ chain.referenceFactor k := by
  apply (one_le_inv₀ (chain.originalLaw_mass_toReal_pos hz k)).mpr
  simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞)
    (chain.originalLaw_mass_le_one hz k)

theorem ofReal_referenceFactor {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) :
    ENNReal.ofReal (chain.referenceFactor k) = (chain.originalLaw k univ)⁻¹ := by
  rw [referenceFactor, ENNReal.ofReal_inv_of_pos (chain.originalLaw_mass_toReal_pos hz k),
    ENNReal.ofReal_toReal ((chain.originalLaw_mass_le_one hz k).trans_lt (by simp)).ne]

/-- The one-time normalization of the common path changes the original
reference law by a subpower factor on every fixed finite path. -/
theorem referenceFactor_subpower {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, chain.referenceFactor k ≤ N z k ^ ε := by
  filter_upwards [chain.originalLaw_mass_subpower hz ε hε] with k hk
  have hN : 0 < N z k := by linarith [hz.1.1 k]
  have hm : N z k ^ (-ε) ≤ (chain.originalLaw k univ).toReal := by
    simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg hN.le _)] using
      ENNReal.toReal_mono ((chain.originalLaw_mass_le_one hz k).trans_lt (by simp)).ne hk
  change ((chain.originalLaw k univ).toReal)⁻¹ ≤ _
  calc
    _ ≤ (N z k ^ (-ε))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hN _) hm
    _ = _ := by rw [Real.rpow_neg hN.le, inv_inv]

theorem probability_le_originalReference {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) :
    chain.probability k ≤ ENNReal.ofReal (chain.referenceFactor k) •
      worldMixture p (chain.sample k) := by
  rw [chain.ofReal_referenceFactor hz k, probability]
  exact Measure.le_iff.mpr fun s hs => by
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' le_rfl (chain.originalLaw_le k s)

/-- All original-layer path laws are images of the same normalized final
mixture. Subsequent masks can therefore be selected on one common space. -/
theorem probability_eq_map_finalMixture {p z : Code} (chain : RefinementChain p z) (k : ℕ) :
    chain.probability k = (normalizedWorldMixture z k).map (chain.pullback k) := by
  have hB₀ : ENNReal.ofReal (chain.budget k) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (chain.budget_pos k)).ne'
  have hBt : ENNReal.ofReal (chain.budget k) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [probability, chain.originalLaw_univ, originalLaw, normalizedWorldMixture,
    Measure.map_smul _ (chain.measurable_pullback k).aemeasurable, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hB₀) (Or.inl hBt)]
  calc
    _ = ((ENNReal.ofReal (chain.budget k))⁻¹ * ENNReal.ofReal (chain.budget k)) *
        (worldMixture z k univ)⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hB₀ hBt, one_mul]

end RefinementChain

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures
