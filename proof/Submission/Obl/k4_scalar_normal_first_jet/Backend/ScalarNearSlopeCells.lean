/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarNearSlopeCells.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarNearSlopeCells.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCellMass

/-! Close-slope cell counts under the original trajectory prior. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped BigOperators

/-- A cell meeting the close-slope set is wholly in the enlarged slope
interval. Its original prior floor therefore pays for its cell count. -/
theorem original_near_slope_cells {Λ ι : Type*} [MeasurableSpace Λ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure Λ) [IsFiniteMeasure ν] {A : Set Λ} (hA : MeasurableSet A)
    {code : Λ → ι} (hcode : Measurable code) (K : Finset ι) (slope : Λ → ℝ)
    {c Δ D m H : ℝ}
    (hfloor : ∀ b ∈ K, (A ∩ code ⁻¹' {b}).Nonempty → m ≤ ν.real (A ∩ code ⁻¹' {b}))
    (hspread : ∀ l ∈ A, ∀ l' ∈ A, code l = code l' → |slope l - slope l'| ≤ D)
    (hcap : ν.real {l | l ∈ A ∧ |slope l - c| ≤ Δ + D} ≤ H) :
    ∃ T : Finset ι, T ⊆ K ∧ (T.card : ℝ) * m ≤ H ∧
      ∀ l ∈ A, code l ∈ K → |slope l - c| ≤ Δ → code l ∈ T := by
  classical
  let T := K.filter (fun b => ∃ l ∈ A, code l = b ∧ |slope l - c| ≤ Δ)
  have hTK : T ⊆ K := Finset.filter_subset _ _
  let U : Set Λ := ⋃ b ∈ T, A ∩ code ⁻¹' {b}
  have hdisj : PairwiseDisjoint (T : Set ι) (fun b => A ∩ code ⁻¹' {b}) := by
    intro b _ b' _ hne
    apply disjoint_left.mpr
    intro l hl hl'
    exact hne (hl.2.symm.trans hl'.2)
  have hU : U ⊆ {l | l ∈ A ∧ |slope l - c| ≤ Δ + D} := by
    intro l hl
    obtain ⟨b, hb, hlA, hlcode⟩ := mem_iUnion₂.mp hl
    obtain ⟨l', hl'A, hl'code, hl'close⟩ := (Finset.mem_filter.mp hb).2
    refine ⟨hlA, ?_⟩
    have hd := hspread l hlA l' hl'A (hlcode.trans hl'code.symm)
    have ht := abs_sub_le (slope l) (slope l') c
    linarith
  have hcount : (T.card : ℝ) * m ≤ H := by
    calc
      _ = ∑ _b ∈ T, m := by simp
      _ ≤ ∑ b ∈ T, ν.real (A ∩ code ⁻¹' {b}) := by
        apply Finset.sum_le_sum
        intro b hb
        obtain ⟨l, hl, hcode, _⟩ := (Finset.mem_filter.mp hb).2
        exact hfloor b (hTK hb) ⟨l, hl, hcode⟩
      _ = ν.real U := (measureReal_biUnion_finset hdisj
        (fun b _ => hA.inter (hcode (MeasurableSet.singleton b)))).symm
      _ ≤ ν.real {l | l ∈ A ∧ |slope l - c| ≤ Δ + D} := measureReal_mono hU
      _ ≤ H := hcap
  refine ⟨T, hTK, hcount, ?_⟩
  intro l hl hK hclose
  exact Finset.mem_filter.mpr ⟨hK, l, hl, rfl, hclose⟩

/-- The same original prior controls the matching output mass; there is
no change of law between the cell floors and the output ceilings. -/
theorem original_near_slope_output_cap {Λ ι : Type*} [MeasurableSpace Λ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure Λ) [IsFiniteMeasure ν] {A : Set Λ} (hA : MeasurableSet A)
    {code : Λ → ι} (hcode : Measurable code) (K : Finset ι) (slope : Λ → ℝ)
    {c Δ D m H C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    (hfloor : ∀ b ∈ K, (A ∩ code ⁻¹' {b}).Nonempty → m ≤ ν.real (A ∩ code ⁻¹' {b}))
    (hspread : ∀ l ∈ A, ∀ l' ∈ A, code l = code l' → |slope l - slope l'| ≤ D)
    (hcap : ν.real {l | l ∈ A ∧ |slope l - c| ≤ Δ + D} ≤ H)
    (Z : Set Λ) (hZ : ∀ l ∈ Z, l ∈ A ∧ code l ∈ K ∧ |slope l - c| ≤ Δ)
    (hout : ∀ b ∈ K, ν.real (Z ∩ code ⁻¹' {b}) ≤ C) :
    ν.real Z ≤ H / m * C := by
  obtain ⟨T, hTK, hcount, hcover⟩ := original_near_slope_cells ν hA hcode K slope hfloor hspread hcap
  have hcard : (T.card : ℝ) ≤ H / m := (le_div_iff₀ hm).mpr hcount
  calc
    ν.real Z ≤ ∑ b ∈ T, ν.real (Z ∩ code ⁻¹' {b}) :=
      original_mass_le_sum_cells ν Z code T (Filter.Eventually.of_forall fun l hl =>
        hcover l (hZ l hl).1 (hZ l hl).2.1 (hZ l hl).2.2)
    _ ≤ ∑ _b ∈ T, C := Finset.sum_le_sum (fun b hb => hout b (hTK hb))
    _ = (T.card : ℝ) * C := by simp
    _ ≤ H / m * C := mul_le_mul_of_nonneg_right hcard hC

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
