/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/GridCaps.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GridLists

/-! Upper observation caps pass from a finite coarser exponent grid to
arbitrary real widths. The actual coarse cells are enumerated; no palette
doubling or occupied-cell lower bound is used. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GridCaps

open MeasureTheory Set
open scoped ENNReal

noncomputable section

def gridCell {X : Type*} {n : ℕ} (Y : X → Fin n → ℝ)
    (width : Fin n → ℝ) (c : Fin n → ℤ) : Set X :=
  {z | ∀ i, ⌊Y z i / width i⌋ = c i}

def overlapChoices {n : ℕ} (α β : Fin n → ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i) (c : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => PathNodes.overlapBins (α i) (β i) (hα i) (hβ i) (c i)

theorem overlapBins_card_le_four (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hβα : β ≤ α) (c : ℤ) :
    (PathNodes.overlapBins α β hα hβ c).card ≤ 4 := by
  have hc := PathNodes.overlapBins_card_le α β hα hβ c
  have hd : β / α ≤ 1 := (div_le_one hα).mpr hβα
  have hc' : ((PathNodes.overlapBins α β hα hβ c).card : ℝ) ≤ 4 := by
    have heq : 2 * β / α + 2 = 2 * (β / α) + 2 := by ring
    rw [heq] at hc
    linarith
  exact_mod_cast hc'

theorem overlapChoices_card {n : ℕ} (α β : Fin n → ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i) (hβα : ∀ i, β i ≤ α i)
    (c : Fin n → ℤ) : (overlapChoices α β hα hβ c).card ≤ 4 ^ n := by
  have hfour (i : Fin n) :
      (PathNodes.overlapBins (α i) (β i) (hα i) (hβ i) (c i)).card ≤ 4 :=
    overlapBins_card_le_four _ _ _ _ (hβα i) _
  rw [overlapChoices, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _i : Fin n, 4 := by gcongr with i; exact hfour i
    _ = _ := by simp

theorem gridCell_subset_overlap {X : Type*} {n : ℕ} (Y : X → Fin n → ℝ)
    (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i) (c : Fin n → ℤ) :
    gridCell Y β c ⊆ ⋃ d ∈ overlapChoices α β hα hβ c, gridCell Y α d := by
  intro z hz
  refine mem_iUnion.mpr ⟨(fun i => ⌊Y z i / α i⌋), mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · apply Fintype.mem_piFinset.mpr
    intro i
    rw [← hz i]
    exact PathNodes.floor_mem_overlapBins (α i) (β i) (hα i) (hβ i) (Y z i)
  · exact fun _ => rfl

/-- A cell on any finer real grid meets at most four old cells in each
coordinate. The same bound holds inside any additional selected event. -/
theorem gridCell_mass_le {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) (Y : X → Fin n → ℝ) (D : Set X)
    (α β : Fin n → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i)
    (hβα : ∀ i, β i ≤ α i) (C : ℝ≥0∞)
    (hcap : ∀ d, μ (D ∩ gridCell Y α d) ≤ C) (c : Fin n → ℤ) :
    μ (D ∩ gridCell Y β c) ≤ (4 : ℝ≥0∞) ^ n * C := by
  classical
  let F := overlapChoices α β hα hβ c
  have hsub : D ∩ gridCell Y β c ⊆ ⋃ d ∈ F, D ∩ gridCell Y α d := by
    intro z hz
    obtain ⟨d, hd⟩ := mem_iUnion.mp (gridCell_subset_overlap Y α β hα hβ c hz.2)
    obtain ⟨hdF, hzd⟩ := mem_iUnion.mp hd
    exact mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨hdF, hz.1, hzd⟩⟩
  calc
    _ ≤ μ (⋃ d ∈ F, D ∩ gridCell Y α d) := measure_mono hsub
    _ ≤ ∑ d ∈ F, μ (D ∩ gridCell Y α d) := measure_biUnion_finset_le F _
    _ ≤ ∑ _d ∈ F, C := Finset.sum_le_sum fun d _ => hcap d
    _ = (F.card : ℝ≥0∞) * C := by simp
    _ ≤ (4 : ℝ≥0∞) ^ n * C := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast overlapChoices_card α β hα hβ hβα c

/-- A finite coarser exponent grid with mesh eta supplies all real-width
upper caps. For the scalar base/base/hidden coordinates the loss is
64*N^((2+d)*eta), and can be absorbed by the shared path slack. -/
theorem power_grid_cap {X : Type*} [MeasurableSpace X] {n : ℕ}
    (μ : Measure X) (Y : X → Fin n → ℝ) (D : Set X) (N : ℝ) (hN : 1 ≤ N)
    (weight r₀ r : Fin n → ℝ) (η : ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hr₀ : ∀ i, r₀ i ≤ r i) (hr : ∀ i, r i ≤ r₀ i + η) (C : ℝ≥0∞)
    (hcap : ∀ d, μ (D ∩ gridCell Y (fun i => N ^ (-r₀ i)) d) ≤
      C * ENNReal.ofReal (N ^ (-(∑ i, weight i * r₀ i)))) (c : Fin n → ℤ) :
    μ (D ∩ gridCell Y (fun i => N ^ (-r i)) c) ≤
      (4 : ℝ≥0∞) ^ n * C *
        ENNReal.ofReal (N ^ (-(∑ i, weight i * r i) + η * ∑ i, weight i)) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hsum : (∑ i, weight i * r i) ≤
      (∑ i, weight i * r₀ i) + η * ∑ i, weight i := by
    calc
      _ ≤ ∑ i, (weight i * r₀ i + η * weight i) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [mul_le_mul_of_nonneg_left (hr i) (hw i)]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hpow : ENNReal.ofReal (N ^ (-(∑ i, weight i * r₀ i))) ≤
      ENNReal.ofReal (N ^ (-(∑ i, weight i * r i) + η * ∑ i, weight i)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  calc
    _ ≤ (4 : ℝ≥0∞) ^ n * (C * ENNReal.ofReal (N ^ (-(∑ i, weight i * r₀ i)))) :=
      gridCell_mass_le μ Y D _ _ (fun i => Real.rpow_pos_of_pos hNp _)
        (fun i => Real.rpow_pos_of_pos hNp _)
        (fun i => Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (hr₀ i))) _ hcap c
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul' le_rfl hpow

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.GridCaps
