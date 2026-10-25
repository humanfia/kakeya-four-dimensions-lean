/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/SelectedPaths.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.OriginalFibers
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.CommonMasks
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! Restrict the common path probability before returning to its original
worlds. Every later sparse selection remains an original incidence submeasure,
and a fixed positive fraction retains inverse-subpower original mass. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem originalLaw_mass_ofReal_inverseReference {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) :
    ENNReal.ofReal ((chain.referenceFactor k)⁻¹) = chain.originalLaw k univ := by
  rw [referenceFactor, inv_inv,
    ENNReal.ofReal_toReal ((chain.originalLaw_mass_le_one hz k).trans_lt (by simp)).ne]

def selectedLaw {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    (G : Set (Fin (W z k) × State)) : Measure (Fin (W p (chain.sample k)) × State) :=
  (chain.originalLaw k univ) •
    ((normalizedWorldMixture z k).restrict G).map (chain.pullback k)

theorem selectedLaw_le_originalLaw {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) (G : Set (Fin (W z k) × State)) :
    chain.selectedLaw k G ≤ chain.originalLaw k := by
  have hmap := Measure.map_mono
    (show (normalizedWorldMixture z k).restrict G ≤ normalizedWorldMixture z k from
      Measure.restrict_le_self) (chain.measurable_pullback k)
  calc
    _ ≤ (chain.originalLaw k univ) •
        (normalizedWorldMixture z k).map (chain.pullback k) := by
      apply Measure.le_iff.mpr
      intro S _
      simp only [selectedLaw, Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl (hmap S)
    _ = (chain.originalLaw k univ) • chain.probability k := by
      rw [chain.probability_eq_map_finalMixture k]
    _ = _ := by
      rw [probability, smul_smul,
        ENNReal.mul_inv_cancel (chain.originalLaw_mass_pos hz k).ne'
          ((chain.originalLaw_mass_le_one hz k).trans_lt (by simp)).ne, one_smul]

theorem selectedLaw_le_originalReference {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) (G : Set (Fin (W z k) × State)) :
    chain.selectedLaw k G ≤ worldMixture p (chain.sample k) :=
  (chain.selectedLaw_le_originalLaw hz k G).trans (chain.originalLaw_le k)

theorem selectedLaw_univ {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    (G : Set (Fin (W z k) × State)) :
    chain.selectedLaw k G univ =
      chain.originalLaw k univ * normalizedWorldMixture z k G := by
  rw [selectedLaw, Measure.smul_apply,
    Measure.map_apply (chain.measurable_pullback k) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ]
  rfl

def selectedWorldLaw {p z : Code} (chain : RefinementChain p z) (k : ℕ)
    (G : Set (Fin (W z k) × State)) (g : Fin (W p (chain.sample k))) : Measure State :=
  originalFibers p (chain.sample k) (chain.selectedLaw k G) g

theorem selectedWorldLaw_le {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) (G : Set (Fin (W z k) × State))
    (g : Fin (W p (chain.sample k))) :
    chain.selectedWorldLaw k G g ≤ mu p (chain.sample k) g :=
  originalFibers_le (chain.selectedLaw_le_originalReference hz k G) g

theorem selectedWorldLaw_mass {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) (G : Set (Fin (W z k) × State)) :
    ∑ g, ENNReal.ofReal (ω p (chain.sample k) g) * chain.selectedWorldLaw k G g univ =
      chain.originalLaw k univ * normalizedWorldMixture z k G :=
  (originalFibers_mass (chain.selectedLaw_le_originalReference hz k G)).trans
    (chain.selectedLaw_univ k G)

theorem selectedWorldLaw_mass_lower {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (k : ℕ) (G : Set (Fin (W z k) × State))
    (hG : ENNReal.ofReal (1 / 2 : ℝ) ≤ normalizedWorldMixture z k G) :
    ENNReal.ofReal ((chain.referenceFactor k * 2)⁻¹) ≤
      ∑ g, ENNReal.ofReal (ω p (chain.sample k) g) * chain.selectedWorldLaw k G g univ := by
  rw [chain.selectedWorldLaw_mass hz k G]
  have hR : 0 ≤ chain.referenceFactor k := zero_le_one.trans (chain.referenceFactor_one_le hz k)
  calc
    _ = ENNReal.ofReal ((chain.referenceFactor k)⁻¹) * ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [mul_inv, ENNReal.ofReal_mul (inv_nonneg.mpr hR)]
      norm_num
    _ = chain.originalLaw k univ * ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [chain.originalLaw_mass_ofReal_inverseReference hz k]
    _ ≤ _ := mul_le_mul' le_rfl hG

theorem retainedFactor_subpower {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, chain.referenceFactor k * 2 ≤ N z k ^ ε := by
  have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => (by linarith [hz.1.1 k])) hz.1.2.1 (chain.referenceFactor_one_le hz)
    (chain.referenceFactor_subpower hz) 1 (a := 0) (b := ε) hε (A := 2) (by norm_num)
  filter_upwards [h] with k hk
  simpa only [pow_one, Real.rpow_zero, mul_one, one_mul, mul_comm] using hk.le

/-- Sparse restrictions made on one common probability return to original
worlds with unchanged priors/weights and inverse-subpower aggregate mass. -/
theorem selectedWorldLaw_mass_subpower {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (G : (k : ℕ) → Set (Fin (W z k) × State))
    (hG : ∀ᶠ k in atTop, ENNReal.ofReal (1 / 2 : ℝ) ≤ normalizedWorldMixture z k (G k))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ENNReal.ofReal (N z k ^ (-ε)) ≤
      ∑ g, ENNReal.ofReal (ω p (chain.sample k) g) * chain.selectedWorldLaw k (G k) g univ := by
  filter_upwards [hG, chain.retainedFactor_subpower hz ε hε] with k hk hR
  have hN : 0 ≤ N z k := by linarith [hz.1.1 k]
  calc
    _ = ENNReal.ofReal ((N z k ^ ε)⁻¹) := by rw [Real.rpow_neg hN]
    _ ≤ ENNReal.ofReal ((chain.referenceFactor k * 2)⁻¹) :=
      ENNReal.ofReal_le_ofReal (inv_anti₀ (by linarith [chain.referenceFactor_one_le hz k]) hR)
    _ ≤ _ := chain.selectedWorldLaw_mass_lower hz k (G k) hk

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathMeasures.RefinementChain
