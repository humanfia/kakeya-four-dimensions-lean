/-
Adapted from this LOT tree, o118, session x0400, commit bd322ee595fd,
Submission/Obl/k4_extremal_profile_setup/NativeDepth.lean.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.ProblemFields
import Submission.Obl.k4_native_grid_profile_extension.CountedRefinement
import Submission.Obl.k4_native_grid_profile_extension.Dyadic
import Submission.Obl.k4_native_grid_profile_extension.Observation

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open Set MeasureTheory
open scoped ENNReal

/-- The frozen pure observations keep the same continuous base and coarsen
only their integer hidden bin. -/
theorem obs_refinement {N r s : ℝ} (hN : 1 ≤ N) (hr : 0 ≤ r) (hrs : r ≤ s)
    (B : ℝ) (a : Incidence) :
    obs B (δ N r) a = ((obs B (δ N s) a).1,
      (obs B (δ N s) a).2 /
        (2 : ℤ) ^ (Submission.Obl.k4_native_grid_profile_extension.depthIndex N s -
          Submission.Obl.k4_native_grid_profile_extension.depthIndex N r)) := by
  apply Prod.ext
  · rfl
  · exact Submission.Obl.k4_native_grid_profile_extension.floor_dyadicWidth_refinement
      hN hr hrs (B * (x a.1 a.2) 3)

/-- Arbitrary measurable versions of the native pure densities are antitone
at the actual sampled incidences. -/
theorem obs_refinement_density_le (μ : Measure Incidence) {N r s : ℝ}
    (hN : 1 ≤ N) (hr : 0 ≤ r) (hrs : r ≤ s) (B : ℝ)
    (f g : Observation → ENNReal) (hf : Measurable f) (hg : Measurable g)
    (hflaw : μ.map (obs B (δ N r)) = (volume.prod Measure.count).withDensity f)
    (hglaw : μ.map (obs B (δ N s)) = (volume.prod Measure.count).withDensity g) :
    ∀ᵐ a ∂μ, g (obs B (δ N s) a) ≤ f (obs B (δ N r) a) := by
  let q (n : ℤ) := n /
    (2 : ℤ) ^ (Submission.Obl.k4_native_grid_profile_extension.depthIndex N s -
      Submission.Obl.k4_native_grid_profile_extension.depthIndex N r)
  have heq : (fun a : Incidence => ((obs B (δ N s) a).1, q (obs B (δ N s) a).2)) =
      obs B (δ N r) := funext fun a => (obs_refinement hN hr hrs B a).symm
  have hcoarse : μ.map (fun a : Incidence => ((obs B (δ N s) a).1, q (obs B (δ N s) a).2)) =
      (volume.prod Measure.count).withDensity f := by rw [heq]; exact hflaw
  have h := Submission.Obl.k4_native_grid_profile_extension.observation_refinement_density_le
    μ volume (obs B (δ N s))
    (Submission.Obl.k4_native_grid_profile_extension.measurable_pureObservation _ _)
    q f g hf hg hcoarse hglaw
  filter_upwards [h] with a ha
  exact ha.trans_eq (congrArg f (congrFun heq a))

noncomputable def Data.incidenceMeasure (p : Data) (k : ℕ) (γ : Fin (p.W k)) :
    Measure Incidence := ((p.ν k γ).prod volume).restrict (p.E k γ)

theorem Data.Valid.density_antitone {p : Data} (hp : p.Valid) (k : ℕ)
    (γ : Fin (p.W k)) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ p.L) :
    ∀ᵐ a ∂p.incidenceMeasure k γ,
      p.g k γ s (obs (p.B k γ) (δ (p.N k) s) a) ≤
        p.g k γ r (obs (p.B k γ) (δ (p.N k) r) a) := by
  have hf := hp.2.2.2.2.2.2.2.2.2.1 k γ r hr (hrs.trans hs)
  have hg := hp.2.2.2.2.2.2.2.2.2.1 k γ s (hr.trans hrs) hs
  exact obs_refinement_density_le (p.incidenceMeasure k γ)
    (by linarith [hp.1 k]) hr hrs (p.B k γ) _ _ hf.1 hg.1 hf.2 hg.2

end Submission.Obl.k4_remainder_pure_profile_normalization
