/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarActiveGrid.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarActiveGrid.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridGeometry

/-! Representatives of the stored active sets in the original time grid. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set

theorem original_active_grid_representatives (U : Set ℝ) (K : Finset ℤ) (p : ℝ)
    (hcover : ∀ u ∈ U, ⌊u / p⌋ ∈ K) (hbound : ∀ u ∈ U, |u| ≤ 1) :
    ∃ (K' : Finset ℤ) (t : ℤ → ℝ), K' ⊆ K ∧
      (∀ u ∈ U, ⌊u / p⌋ ∈ K') ∧
      ∀ k ∈ K', t k ∈ U ∧ ⌊t k / p⌋ = k ∧ |t k| ≤ 1 := by
  classical
  let K' := K.filter (fun k => ∃ u ∈ U, ⌊u / p⌋ = k)
  have hchoice : ∀ k ∈ K', ∃ u ∈ U, ⌊u / p⌋ = k :=
    fun k hk => (Finset.mem_filter.mp hk).2
  let t : ℤ → ℝ := fun k => if hk : k ∈ K' then (hchoice k hk).choose else 0
  refine ⟨K', t, Finset.filter_subset _ _, ?_, ?_⟩
  · intro u hu
    exact Finset.mem_filter.mpr ⟨hcover u hu, u, hu, rfl⟩
  · intro k hk
    have hmem : t k ∈ U ∧ ⌊t k / p⌋ = k := by
      simpa only [t, dif_pos hk] using (hchoice k hk).choose_spec
    exact ⟨hmem.1, hmem.2, hbound _ hmem.1⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
