import Submission.Obl.k4_scalar_pure_multiworld_homogenization.WorldMeasure
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.GridProfile
import Submission.Obl.k4_native_grid_profile_extension.DepthGrid

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_native_grid_profile_extension.Profiles

abbrev depthGrid (L : ℝ) : Set ℝ :=
  Submission.Obl.k4_native_grid_profile_extension.depthGrid L
abbrev clamp (L : ℝ) (q : ℚ) : ℝ :=
  Submission.Obl.k4_native_grid_profile_extension.Clamp L q

abbrev GridData (p : Problem) : Prop :=
  ∃ (M : ℝ) (a : ℕ → ℚ → ℝ), (∀ k q, |a k q| ≤ M) ∧
    ∀ (q : ℚ) (τ : ℝ), 0 < τ →
      IsPowerSmall (resolution p) (fun k => worldLaw p k
        {z | sampledDensity p (clamp (length p) q) k z <
            ENNReal.ofReal (resolution p k ^ (-a k q - τ)) ∨
          ENNReal.ofReal (resolution p k ^ (-a k q + τ)) <
            sampledDensity p (clamp (length p) q) k z})

abbrev subsequenceProblem (p : Problem) (φ : ℕ → ℕ) (F : ℝ → ℝ) : Problem :=
  selectedProblem p φ (loss p ∘ φ) (sizeBudget p) (degreeBudget p)
    (fun k => event p (φ k)) (fun k => density p (φ k)) F

theorem raw_subsequence {p : Problem} (hp : RawScalar p) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (F : ℝ → ℝ) : RawScalar (subsequenceProblem p φ F) := by
  constructor
  · refine ⟨(fun k => hp.1.1 (φ k)), hp.1.2.1.comp hφ.tendsto_atTop,
      ⟨(fun k => hp.1.2.2.1.1 (φ k)), ?_⟩, hp.1.2.2.2⟩
    intro ε hε
    exact hφ.tendsto_atTop.eventually (hp.1.2.2.1.2 ε hε)
  · intro k
    exact hp.2 (φ k)

/-- Bounded typical exponents on the countable depth grid give the entire pure
profile after one subsequence, retaining all priors, weights, and events. -/
theorem pure_profile_from_grid {p : Problem}
    (hp : RawScalar p) (hd : HasDensities p) (hgrid : GridData p) :
    ∃ (φ : ℕ → ℕ) (F : ℝ → ℝ), StrictMono φ ∧
      RawScalar (subsequenceProblem p φ F) ∧ PureProfile (subsequenceProblem p φ F) := by
  classical
  obtain ⟨M, a, ha, htypical⟩ := hgrid
  let S := depthGrid (length p)
  have hL : 0 ≤ length p := hp.1.2.2.2.2.2.1.le
  have hs : S.Countable :=
    Submission.Obl.k4_native_grid_profile_extension.depthGrid_countable _
  have hclosure : closure S = Icc 0 (length p) :=
    Submission.Obl.k4_native_grid_profile_extension.closure_depthGrid hL
  choose index hindex using fun s : S => s.property
  let aS (k : ℕ) (s : S) := a k (index s)
  obtain ⟨φ, F, hφ, hF, hshape, htyp⟩ := profile_of_countable_grid
    (resolution p) hp.1.1 hp.1.2.1 (worldLaw p) (worldLaw_inverse_subpower hp)
    (length p) hL S hs hclosure
    (Submission.Obl.k4_native_grid_profile_extension.zero_mem_depthGrid hL)
    (Submission.Obl.k4_native_grid_profile_extension.right_mem_depthGrid hL)
    (sampledDensity p) aS M (fun k s => ha k (index s))
    (by
      intro s τ hτ
      simpa only [← hindex s] using htypical (index s) τ hτ)
    (by
      intro r hr s hs hrs ε hε
      exact world_approx_mono hp hd hr.1 hrs hs.2 hε)
    (by
      intro r hr s hs hrs ε hε
      exact world_approx_tail hp hd hr.1 hrs hs.2 hε)
  refine ⟨φ, F, hφ, raw_subsequence hp hφ F, ?_⟩
  refine ⟨?_, hshape, ?_⟩
  · intro k a r hr hrL
    exact hd (φ k) a r hr hrL
  · intro r τ hr hrL hτ
    obtain ⟨c, hc, hsmall⟩ := htyp r ⟨hr, hrL⟩ τ hτ
    refine ⟨c, hc, ?_⟩
    filter_upwards [hsmall] with k hk
    simp only [Function.comp_apply] at hk
    have hm : MeasurableSet {z : WorldState p (φ k) |
        sampledDensity p r (φ k) z <
            ENNReal.ofReal (resolution p (φ k) ^ (-F r - τ)) ∨
          ENNReal.ofReal (resolution p (φ k) ^ (-F r + τ)) <
            sampledDensity p r (φ k) z} :=
      (measurableSet_lt (measurable_sampledDensity hd _ hr hrL) measurable_const).union
        (measurableSet_lt measurable_const (measurable_sampledDensity hd _ hr hrL))
    rw [worldLaw_apply p (φ k) hm] at hk
    exact hk

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
