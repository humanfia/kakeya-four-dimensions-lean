/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBoxCaps.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBoxCaps.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridIndices
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Choose

/-! Rectangular caps obtained by covering with original spatial cubes. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped BigOperators

theorem original_rectangular_cap {Λ ι : Type*} [MeasurableSpace Λ] [Fintype ι]
    (ν : Measure Λ) [IsFiniteMeasure ν] (A E : Set Λ) (X : Λ → ι → ℝ)
    (a W : ι → ℝ) {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hW : ∀ i, 0 ≤ W i) (hEA : E ⊆ A)
    (hbox : ∀ l ∈ E, ∀ i, X l i ∈ Icc (a i) (a i + W i))
    (hcap : ∀ b : ι → ℝ,
      ν.real {l | l ∈ A ∧ ∀ i, X l i ∈ Icc (b i) (b i + q)} ≤ C) :
    ν.real E ≤ (∏ i, (2 * W i / q + 3)) * C := by
  classical
  have hbounded i : ∀ l ∈ E, |X l i - a i| ≤ W i := by
    intro l hl
    obtain ⟨hlo, hhi⟩ := hbox l hl i
    rw [abs_le]
    constructor <;> linarith [hW i]
  choose J hcard hcover hrep using fun i =>
    bounded_scalar_grid_indices E (fun l => X l i - a i) (hW i) hq (hbounded i)
  let K := Fintype.piFinset J
  let B : (ι → ℤ) → Set Λ := fun k =>
    {l | l ∈ A ∧ ∀ i, X l i ∈ Icc (a i + q * k i) (a i + q * k i + q)}
  have hsub : E ⊆ ⋃ k ∈ K, B k := by
    intro l hl
    let k : ι → ℤ := fun i => ⌊(X l i - a i) / q⌋
    refine mem_iUnion₂.mpr ⟨k, Fintype.mem_piFinset.mpr (fun i => hcover i l hl), hEA hl, ?_⟩
    intro i
    have h := (mesh_lower_endpoint hq (k := k i) rfl).1
    constructor <;> linarith [h.1, h.2]
  have hKcard : (K.card : ℝ) ≤ ∏ i, (2 * W i / q + 3) := by
    simp only [K, Fintype.card_piFinset, Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg (J i).card) (fun i _ => hcard i)
  calc
    ν.real E ≤ ν.real (⋃ k ∈ K, B k) := measureReal_mono hsub (measure_ne_top ν _)
    _ ≤ ∑ k ∈ K, ν.real (B k) := measureReal_biUnion_finset_le K B
    _ ≤ ∑ _k ∈ K, C := Finset.sum_le_sum (fun k _ => hcap (fun i => a i + q * k i))
    _ = (K.card : ℝ) * C := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hKcard hC

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
