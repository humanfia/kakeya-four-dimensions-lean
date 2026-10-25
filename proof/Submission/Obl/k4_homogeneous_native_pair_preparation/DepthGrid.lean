-- Adapted from this LOT tree, o114, session x0680, commit 8cc890dd,
-- Submission/Obl/k4_terminal_representative_atlas/Preparation/BandInterpolation.lean.
import Submission.Obl.k4_tempered_grid_selection.Exponents
import Submission.Obl.k4_quadratic_atlas_normalization.PowerBins

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open Set

/-- A fixed finite depth grid approximates every depth from below. -/
theorem exists_depth_grid {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ R : Finset ℝ, 0 ∈ R ∧ L ∈ R ∧
      (∀ r ∈ R, r ∈ Icc 0 L) ∧
      ∀ r ∈ Icc 0 L, ∃ s ∈ R, s ≤ r ∧ r ≤ s + u := by
  classical
  let n := ⌈L / u⌉₊ + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let a := L / n
  have ha : 0 ≤ a := div_nonneg hL hnR.le
  have hau : a ≤ u := by
    have hc : L / u ≤ (n : ℝ) := by
      dsimp [n]
      push_cast
      linarith [Nat.le_ceil (L / u)]
    apply (div_le_iff₀ hnR).mpr
    have := (div_le_iff₀ hu).mp hc
    linarith
  let v : ℕ → ℝ := fun j => (j : ℝ) * a
  have hv0 : v 0 = 0 := by simp [v]
  have hvn : v n = L := by dsimp [v, a]; field_simp
  let R := (Finset.range (n + 1)).image v
  have hm (j : ℕ) (hj : j ≤ n) : v j ∈ R :=
    Finset.mem_image_of_mem v (Finset.mem_range.mpr (by omega))
  refine ⟨R, hv0 ▸ hm 0 (by omega), hvn ▸ hm n le_rfl, ?_, ?_⟩
  · intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
    constructor
    · dsimp [v]; positivity
    · rw [← hvn]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjn) ha
  · intro r hr
    obtain ⟨j, hj, hjr, hrj⟩ :=
      Submission.Obl.k4_quadratic_atlas_normalization.finite_chain_interval_cover v hn
        (by simpa only [hv0] using hr.1) (by simpa only [hvn] using hr.2)
    refine ⟨v j, hm j (by have := Finset.mem_range.mp hj; omega), hjr, ?_⟩
    have he : v (j + 1) = v j + a := by simp only [v, Nat.cast_add, Nat.cast_one]; ring
    rw [he] at hrj
    linarith

end Submission.Obl.k4_homogeneous_native_pair_preparation
