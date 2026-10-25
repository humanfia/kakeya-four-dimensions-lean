/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/DepthGrid.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/DepthGrid.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.Interface
import Submission.Obl.k4_profile_density_bounds.Common

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open Set

/-- A finite grid whose left-hand points approximate every smaller depth. -/
def coarseDepthGrid (s ε : ℝ) : Finset ℝ := by
  classical
  exact (Finset.Icc (0 : ℤ) ⌊s / ε⌋).image (fun j : ℤ => (j : ℝ) * ε)

theorem coarseDepthGrid_bounds {s ε : ℝ} (_hs : 0 ≤ s) (hε : 0 < ε)
    {r : ℝ} (hr : r ∈ coarseDepthGrid s ε) : 0 ≤ r ∧ r ≤ s := by
  classical
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨hj0, hjs⟩ := Finset.mem_Icc.mp hj
  constructor
  · exact mul_nonneg (by exact_mod_cast hj0) hε.le
  · apply (le_div_iff₀ hε).1
    exact (show (j : ℝ) ≤ (⌊s / ε⌋ : ℝ) by exact_mod_cast hjs).trans (Int.floor_le _)

theorem exists_coarseDepthGrid {s ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) (hrs : r ≤ s) :
    ∃ r₀ ∈ coarseDepthGrid s ε, r₀ ≤ r ∧ r - r₀ < ε := by
  classical
  let j : ℤ := ⌊r / ε⌋
  have hj0 : 0 ≤ j := Int.floor_nonneg.mpr (div_nonneg hr hε.le)
  have hjs : j ≤ ⌊s / ε⌋ := Int.floor_mono (div_le_div_of_nonneg_right hrs hε.le)
  refine ⟨(j : ℝ) * ε, Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj0, hjs⟩, rfl⟩, ?_, ?_⟩
  · exact (le_div_iff₀ hε).1 (Int.floor_le _)
  · have h := (div_lt_iff₀ hε).1 (Int.lt_floor_add_one (r / ε))
    change r - (j : ℝ) * ε < ε
    change r < ((j : ℝ) + 1) * ε at h
    linarith

/-- Only a finite coarser pure-density grid is needed for all-depth caps:
the native observation width dominates the actual signal-bin width, while
the profile density loses at most `N^ε`. -/
theorem coarseDepthGrid_power_bounds {N s ε r τ : ℝ} (hN : 1 ≤ N)
    (hε : 0 < ε) (hr : 0 ≤ r) (hrs : r ≤ s)
    (f : ℝ → ℝ)
    (hf : ∀ a b, 0 ≤ a → a ≤ b → b ≤ s → f b - f a ≤ b - a) :
    ∃ r₀ ∈ coarseDepthGrid s ε, 0 ≤ r₀ ∧ r₀ ≤ r ∧ r - r₀ < ε ∧
      N ^ (-r) ≤ δ N r₀ ∧ N ^ (-f r₀ + τ) ≤ N ^ (-f r + τ + ε) := by
  obtain ⟨r₀, hr₀, hr₀r, hgap⟩ := exists_coarseDepthGrid hε hr hrs
  have hr₀0 := (coarseDepthGrid_bounds (hr.trans hrs) hε hr₀).1
  refine ⟨r₀, hr₀, hr₀0, hr₀r, hgap, ?_, ?_⟩
  · calc
      N ^ (-r) ≤ N ^ (-r₀) := Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hr₀r)
      _ ≤ δ N r₀ := (Submission.Obl.k4_profile_density_bounds.width_bounds
        (show 0 < N by linarith only [hN]) r₀).1
  · apply Real.rpow_le_rpow_of_exponent_le hN
    have h := hf r₀ r hr₀0 hr₀r hrs
    linarith

end Submission.Obl.k4_uncapped_native_capping.UWE
