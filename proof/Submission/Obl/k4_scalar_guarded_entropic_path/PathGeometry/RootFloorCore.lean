/-
Adapted from this LOT tree, obligation o093, session x0535, commit 21cac614,
Submission/Obl/k4_scalar_critical_path_terminal/RootFloorCore.lean. Original attribution is retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPacketFamilies
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.PreparationCore
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.FixedFractionMass

/-! The actual root packet floors, width masks and original density masks
hold on one fixed common core with positive probability and inverse-subpower
original mass. Its choice precedes every later residual and candidate. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPacketFamilies

open MeasureTheory Set Filter PathMeasures PathPruning PathNodes
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

theorem eventually_floorPruningLoss_small {p z : Code} (chain : RefinementChain p z)
    (hz : Exact z) (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, (m : ENNReal) *
      (ENNReal.ofReal (chain.referenceFactor k) / ENNReal.ofReal (N z k ^ ε)) ≤
        ENNReal.ofReal (1 / 4 : ℝ) := by
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => (by linarith [hz.1.1 k])) hz.1.2.1 (chain.referenceFactor_one_le hz)
    (chain.referenceFactor_subpower hz) 1 (a := -ε) (b := 0)
    (by linarith) (A := 4 * (m : ℝ)) (by positivity)
  filter_upwards [hsmall] with k hk
  have hN : 0 < N z k := by linarith [hz.1.1 k]
  have hreal : (m : ℝ) * (chain.referenceFactor k / (N z k ^ ε)) ≤ (1 / 4 : ℝ) := by
    simp only [pow_one, Real.rpow_zero] at hk
    rw [div_eq_mul_inv, ← Real.rpow_neg hN.le]
    nlinarith
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hN _),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  exact ENNReal.ofReal_le_ofReal hreal

variable {ctx : CriticalContext} {source : MaximizingFamily ctx}
  {start : ℝ} {targets : List ℝ}

def FloorCoreProperties (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (k : ℕ)
    (E : Set (Fin (W (path.forget.finalFamily.problem i) k) × State)) : Prop :=
  MeasurableSet E ∧ E ⊆ path.preparationCore i certs choices grid k ∧
    ENNReal.ofReal (1 / 4 : ℝ) ≤
      normalizedWorldMixture (path.forget.finalFamily.problem i) k E ∧
    ∀ (j : Fin targets.length) (d : (rootPacketFamily path i certs ε j).Index k),
      0 < ω (source.problem i) ((path.measuredChain i certs).sample k)
        ((rootPacketFamily path i certs ε j).world k d) →
      E ∩ (rootPacketFamily path i certs ε j).cell k d = ∅ ∨
        (ENNReal.ofReal (N (path.forget.finalFamily.problem i) k ^ ε))⁻¹ *
          ENNReal.ofReal ((rootPacketFamily path i certs ε j).duration k) *
          ν (source.problem i) ((path.measuredChain i certs).sample k)
            ((rootPacketFamily path i certs ε j).world k d)
            ((rootPacketFamily path i certs ε j).assignment k d) ≤
        (path.measuredChain i certs).selectedWorldLaw k E
          ((rootPacketFamily path i certs ε j).world k d)
          ((rootPacketFamily path i certs ε j).priorCell k d)

theorem eventually_exists_floorCore (path : TrueGridPath ctx source start targets)
    (i : ℕ) (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∃ E, FloorCoreProperties path i certs choices grid ε k E := by
  let chain := path.measuredChain i certs
  have hz := (path.forget.finalFamily.angular i).1
  filter_upwards [path.eventually_preparationCore_mass_half i certs choices grid,
    eventually_floorPruningLoss_small chain hz targets.length ε hε] with k hhalf hsmall
  obtain ⟨E, hE, hsub, hmass, hfloor⟩ := simultaneous_root_packet_floors path i certs ε k
    (chain.referenceFactor k) (N (path.forget.finalFamily.problem i) k ^ ε) le_rfl
    (normalizedWorldMixture (path.forget.finalFamily.problem i) k) le_rfl
    (path.preparationCore i certs choices grid k)
    (path.measurableSet_preparationCore i certs choices grid k)
  have hquarter : ENNReal.ofReal (1 / 4 : ℝ) ≤
      normalizedWorldMixture (path.forget.finalFamily.problem i) k E := by
    apply ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (1 / 4 : ℝ))
      ENNReal.ofReal_ne_top
    have h := hhalf.trans (hmass.trans (add_le_add le_rfl hsmall))
    calc
      ENNReal.ofReal (1 / 4 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) =
          ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
      _ ≤ _ := h
  refine ⟨E, hE, hsub, hquarter, ?_⟩
  exact hfloor

def floorCore (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (k : ℕ) :
    Set (Fin (W (path.forget.finalFamily.problem i) k) × State) := by
  classical
  exact if h : ∃ E, FloorCoreProperties path i certs choices grid ε k E
    then Classical.choose h else ∅

theorem measurableSet_floorCore (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (k : ℕ) :
    MeasurableSet (floorCore path i certs choices grid ε k) := by
  classical
  unfold floorCore
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact MeasurableSet.empty

theorem floorCore_subset_preparationCore (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (k : ℕ) :
    floorCore path i certs choices grid ε k ⊆ path.preparationCore i certs choices grid k := by
  classical
  unfold floorCore
  split_ifs with h
  · exact (Classical.choose_spec h).2.1
  · exact empty_subset _

theorem eventually_floorCore_properties (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, FloorCoreProperties path i certs choices grid ε k
      (floorCore path i certs choices grid ε k) := by
  classical
  filter_upwards [eventually_exists_floorCore path i certs choices grid ε hε] with k hk
  unfold floorCore
  rw [dite_eq_left hk]
  exact Classical.choose_spec hk

theorem floorCore_original_mass_subpower (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, ENNReal.ofReal (N (path.forget.finalFamily.problem i) k ^ (-δ)) ≤
      ∑ g, ENNReal.ofReal (ω (source.problem i) ((path.measuredChain i certs).sample k) g) *
        (path.measuredChain i certs).selectedWorldLaw k
          (floorCore path i certs choices grid ε k) g univ := by
  apply (path.measuredChain i certs).selectedWorldLaw_mass_subpower_of_fixed_fraction
    (path.forget.finalFamily.angular i).1 _ (1 / 4) (by norm_num) ?_ δ hδ
  filter_upwards [eventually_floorCore_properties path i certs choices grid ε hε] with k hk
  exact hk.2.2.1

theorem floorCore_subset_wide (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (k : ℕ) :
    floorCore path i certs choices grid ε k ⊆ path.widePathSet i certs choices k :=
  (floorCore_subset_preparationCore path i certs choices grid ε k).trans
    (path.preparationCore_subset_wide i certs choices grid k)

theorem floorCore_subset_ambient (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (k : ℕ) :
    floorCore path i certs choices grid ε k ⊆ path.ambientPathSet i certs k :=
  (floorCore_subset_preparationCore path i certs choices grid ε k).trans
    (path.preparationCore_subset_ambient i certs choices grid k)

/-- Every later dominated residual in every actual suffix retains the
original tested density caps. No candidate selects a new prior or mask. -/
theorem allSuffixes_floorCore_exception_null (path : TrueGridPath ctx source start targets) (i : ℕ)
    (certs : path.Certificates i) (choices : path.WidthChoices i certs)
    (grid : DensityGrid) (ε : ℝ) (k : ℕ) :
    (path.measuredChain i certs).AllSuffixes (fun q suffix =>
      ∀ (j : Fin (grid.count q)) (g : Fin (W q (suffix.sample k))) (ρ : Measure State),
        ρ ≤ suffix.selectedWorldLaw k (floorCore path i certs choices grid ε k) g →
        ρ (pureException q (suffix.sample k) g (grid.pureDepth q j) (grid.tolerance q j)) = 0 ∧
        ρ (angularException q (suffix.sample k) g (grid.angularDepth q j) (grid.tolerance q j)) = 0) := by
  apply (path.measuredChain i certs).allSuffixes_mono (fun q suffix hq => ?_)
    (path.allSuffixes_preparationCore_exception_null i certs choices grid k)
  intro j g ρ hρ
  exact hq j g ρ (hρ.trans (suffix.selectedWorldLaw_mono_mask k
    (floorCore_subset_preparationCore path i certs choices grid ε k) g))

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RootPacketFamilies
