/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/PreparationCore.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathWidthMasks
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensitySupport
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.DensityCaps
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.SelectedMaskMonotonicity

/-! Simultaneous width and original density preparation on one common
finite path probability. The returned original-world laws keep their
original priors and weights and have inverse-subpower total mass. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath

open MeasureTheory Set Filter PathMeasures
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_native_grid_profile_extension.Profiles

noncomputable section

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

def preparationCore (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (k : ℕ) :
    Set (Fin (W (path.forget.finalFamily.problem i) k) × State) :=
  path.widthCore i certs choices k ∩
    (path.measuredChain i certs).commonCore grid.exceptions k

theorem measurableSet_preparationCore (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (k : ℕ) : MeasurableSet (path.preparationCore i certs choices grid k) :=
  (path.measurableSet_widthCore i certs choices k).inter
    ((path.measuredChain i certs).measurableSet_commonCore grid.exceptions grid.measurableSet_exceptions k)

/-- Both families of deletions are charged to the SAME probability,
so their intersection still retains half the mass eventually. -/
theorem eventually_preparationCore_mass_half (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs) (grid : DensityGrid) :
    ∀ᶠ k in atTop, ENNReal.ofReal (1 / 2 : ℝ) ≤
      normalizedWorldMixture (path.forget.finalFamily.problem i) k
        (path.preparationCore i certs choices grid k) := by
  let chain := path.measuredChain i certs
  let events := path.widthEvents i certs choices
  have hz := (path.forget.finalFamily.angular i).1
  let bad := fun k => chain.sampledBadSet events k ∪ chain.badSet grid.exceptions k
  have hm (k : ℕ) : MeasurableSet (bad k) :=
    (chain.measurableSet_sampledBadSet events (path.widthEvents_measurable i certs choices) k).union
      (chain.measurableSet_badSet grid.exceptions grid.measurableSet_exceptions k)
  have hsmall : IsPowerSmall (N (path.forget.finalFamily.problem i))
      (fun k => normalizedWorldMixture _ k (bad k)) := by
    apply ((chain.sampledBadSet_powerSmall hz events
      (path.widthEvents_measurable i certs choices) (path.widthEvents_small i certs choices)).add
        hz.1.2.1 (chain.badSet_powerSmall hz grid.exceptions grid.measurableSet_exceptions
          (chain.allSuffixes_densityExceptions_powerSmall grid))).mono
    exact Eventually.of_forall fun _ => measure_union_le _ _
  obtain ⟨c, hc, hbound⟩ := hsmall
  have hhalf : ∀ᶠ k in atTop, N (path.forget.finalFamily.problem i) k ^ (-c) ≤ (1 / 2 : ℝ) :=
    ((tendsto_rpow_neg_atTop hc).comp hz.1.2.1).eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hbound, hhalf] with k hk hpow
  let := normalizedWorldMixture_isProbability hz k
  have heq : path.preparationCore i certs choices grid k = chain.pathSet k ∩ (bad k)ᶜ := by
    ext z
    simp only [preparationCore, widthCore, RefinementChain.sampledCore,
      RefinementChain.commonCore, chain, events, bad, mem_inter_iff, mem_compl_iff, mem_union]
    tauto
  have hcore : normalizedWorldMixture _ k (path.preparationCore i certs choices grid k) =
      normalizedWorldMixture _ k (bad k)ᶜ := by
    rw [heq]
    exact Measure.measure_inter_eq_of_ae (chain.pathSet_ae_normalized k)
  apply Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    (1 : ℝ≥0∞) _ _ 1 (by norm_num) (by norm_num) ?_
      (hk.trans (ENNReal.ofReal_le_ofReal hpow))
  rw [hcore, add_comm, measure_add_measure_compl (hm k)]
  simp

/-- The ORIGINAL full source laws retain inverse-subpower aggregate
mass after the joint width and density deletion. -/
theorem preparationCore_original_mass_subpower (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ENNReal.ofReal (N (path.forget.finalFamily.problem i) k ^ (-ε)) ≤
      ∑ g, ENNReal.ofReal (ω (source.problem i) ((path.measuredChain i certs).sample k) g) *
        (path.measuredChain i certs).selectedWorldLaw k
          (path.preparationCore i certs choices grid k) g univ :=
  (path.measuredChain i certs).selectedWorldLaw_mass_subpower
    (path.forget.finalFamily.angular i).1 _
    (path.eventually_preparationCore_mass_half i certs choices grid) ε hε

theorem preparationCore_subset_wide (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (k : ℕ) :
    path.preparationCore i certs choices grid k ⊆ path.widePathSet i certs choices k :=
  fun _ hz => path.widthCore_subset_wide i certs choices k hz.1

theorem preparationCore_subset_ambient (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (k : ℕ) :
    path.preparationCore i certs choices grid k ⊆ path.ambientPathSet i certs k :=
  fun _ hz => path.widthCore_subset_ambient i certs choices k hz.1

/-- Every later dominated law in every original frame inherits all tested
original density exceptions as null sets, hence all existing density caps. -/
theorem allSuffixes_preparationCore_exception_null (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (k : ℕ) :
    (path.measuredChain i certs).AllSuffixes (fun q suffix =>
      ∀ (j : Fin (grid.count q)) (g : Fin (W q (suffix.sample k))) (ρ : Measure State),
        ρ ≤ suffix.selectedWorldLaw k (path.preparationCore i certs choices grid k) g →
        ρ (pureException q (suffix.sample k) g (grid.pureDepth q j) (grid.tolerance q j)) = 0 ∧
        ρ (angularException q (suffix.sample k) g (grid.angularDepth q j) (grid.tolerance q j)) = 0) := by
  let chain := path.measuredChain i certs
  have hz := (path.forget.finalFamily.angular i).1
  have hnull := chain.allSuffixes_densityCore_exception_null hz grid k
  apply chain.allSuffixes_mono (fun q suffix hq => ?_) hnull
  intro j g ρ hρ
  have hmono := suffix.selectedWorldLaw_mono_mask k
    (show path.preparationCore i certs choices grid k ⊆ chain.commonCore grid.exceptions k from
      inter_subset_right) g
  have hdom := hρ.trans hmono
  exact ⟨le_antisymm ((hdom _).trans_eq (hq j g).1) zero_le,
    le_antisymm ((hdom _).trans_eq (hq j g).2) zero_le⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PathNodes.TrueGridPath
