/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCellMass.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCellMass.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-! Original mass, cell ceilings and finite collision-cell counts. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set Function
open scoped BigOperators

theorem original_mass_le_sum_cells {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (code : Ω → ι) (K : Finset ι)
    (hcover : ∀ᵐ x ∂μ, x ∈ E → code x ∈ K) :
    μ.real E ≤ ∑ b ∈ K, μ.real (E ∩ code ⁻¹' {b}) := by
  have hs : E ≤ᵐ[μ] ⋃ b ∈ K, E ∩ code ⁻¹' {b} := by
    filter_upwards [hcover] with x hx hE
    exact mem_biUnion (hx hE) ⟨hE, rfl⟩
  exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hs)).trans
    (measureReal_biUnion_finset_le K _)

theorem sum_original_code_masses {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] {E : Set Ω} (hE : MeasurableSet E)
    {code : Ω → ι} (hcode : Measurable code) (K : Finset ι)
    (hcover : ∀ x ∈ E, code x ∈ K) :
    (∑ b ∈ K, μ.real (E ∩ code ⁻¹' {b})) = μ.real E := by
  have hd : PairwiseDisjoint (K : Set ι) (fun b => E ∩ code ⁻¹' {b}) := by
    intro b _ b' _ hne
    apply disjoint_left.mpr
    intro x hx hx'
    exact hne (hx.2.symm.trans hx'.2)
  have he : (⋃ b ∈ K, E ∩ code ⁻¹' {b}) = E := by
    ext x
    constructor
    · intro hx
      obtain ⟨b, hxb⟩ := mem_iUnion.mp hx
      obtain ⟨hb, hx⟩ := mem_iUnion.mp hxb
      exact hx.1
    · intro hx
      exact mem_biUnion (hcover x hx) ⟨hx, rfl⟩
  calc
    _ = μ.real (⋃ b ∈ K, E ∩ code ⁻¹' {b}) :=
      (measureReal_biUnion_finset hd (fun b _ => hE.inter (hcode (MeasurableSet.singleton b)))).symm
    _ = μ.real E := congrArg μ.real he

/-- Finite occupied lists suffice for the exact collision formula even
when the ambient code type is infinite, as for integer floor grids. -/
theorem original_finite_code_pair_energy {Ω ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] {E : Set Ω} (hE : MeasurableSet E)
    {code : Ω → ι} (hcode : Measurable code) (K : Finset ι)
    (hcover : ∀ x ∈ E, code x ∈ K) :
    (∑ b ∈ K, μ.real (E ∩ code ⁻¹' {b}) ^ 2) =
      (μ.prod μ).real {p : Ω × Ω | p.1 ∈ E ∧ p.2 ∈ E ∧ code p.1 = code p.2} := by
  classical
  let A : ι → Set Ω := fun b => E ∩ code ⁻¹' {b}
  have hm b : MeasurableSet (A b) := hE.inter (hcode (MeasurableSet.singleton b))
  have hd : PairwiseDisjoint (K : Set ι) (fun b => A b ×ˢ A b) := by
    intro b _ b' _ hne
    apply disjoint_left.mpr
    intro p hp hp'
    exact hne (hp.1.2.symm.trans hp'.1.2)
  have he : (⋃ b ∈ K, A b ×ˢ A b) =
      {p : Ω × Ω | p.1 ∈ E ∧ p.2 ∈ E ∧ code p.1 = code p.2} := by
    ext p
    constructor
    · intro hp
      obtain ⟨b, hpb⟩ := mem_iUnion.mp hp
      obtain ⟨hb, hp⟩ := mem_iUnion.mp hpb
      exact ⟨hp.1.1, hp.2.1, hp.1.2.trans hp.2.2.symm⟩
    · rintro ⟨hp, hp', heq⟩
      exact mem_biUnion (hcover p.1 hp) ⟨⟨hp, rfl⟩, ⟨hp', heq.symm⟩⟩
  rw [← he, measureReal_biUnion_finset hd (fun b _ => (hm b).prod (hm b))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [measureReal_prod_prod, pow_two]

theorem positive_original_cells_cover_ae {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (code : Ω → ι) (K : Finset ι)
    (hcover : ∀ᵐ x ∂μ, x ∈ E → code x ∈ K) :
    ∀ᵐ x ∂μ, x ∈ E → code x ∈ K.filter (fun b => 0 < μ.real (E ∩ code ⁻¹' {b})) := by
  classical
  have hn : ∀ b ∈ K, ∀ᵐ x ∂μ,
      μ.real (E ∩ code ⁻¹' {b}) = 0 → x ∉ E ∩ code ⁻¹' {b} := by
    intro b hb
    by_cases hz : μ.real (E ∩ code ⁻¹' {b}) = 0
    · have hzero : μ (E ∩ code ⁻¹' {b}) = 0 := (measureReal_eq_zero_iff).mp hz
      have hae : ∀ᵐ x ∂μ, x ∉ E ∩ code ⁻¹' {b} := by
        rw [ae_iff]
        have he : {a : Ω | ¬(a ∉ E ∩ code ⁻¹' {b})} = E ∩ code ⁻¹' {b} := by
          ext x
          simp
        rw [he]
        exact hzero
      exact hae.mono fun x hx _ => hx
    · exact Filter.Eventually.of_forall fun x h => (hz h).elim
  have hall := (Filter.eventually_all_finset K).mpr hn
  filter_upwards [hcover, hall] with x hx hn hE
  apply Finset.mem_filter.mpr ⟨hx hE, ?_⟩
  by_contra hp
  have hz : μ.real (E ∩ code ⁻¹' {code x}) = 0 :=
    le_antisymm (not_lt.mp hp) measureReal_nonneg
  exact hn (code x) (hx hE) hz ⟨hE, rfl⟩

/-- A ceiling on every original cell converts original event mass to an
occupied-cell lower bound. Almost-everywhere coverage permits null cells
to be discarded before choosing representatives. -/
theorem original_cell_count_lower {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (code : Ω → ι) (K : Finset ι)
    (hcover : ∀ᵐ x ∂μ, x ∈ E → code x ∈ K) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ b ∈ K, μ.real (E ∩ code ⁻¹' {b}) ≤ c) :
    μ.real E / c ≤ (K.card : ℝ) := by
  apply (div_le_iff₀ hc).mpr
  calc
    μ.real E ≤ ∑ b ∈ K, μ.real (E ∩ code ⁻¹' {b}) :=
      original_mass_le_sum_cells μ E code K hcover
    _ ≤ ∑ _b ∈ K, c := Finset.sum_le_sum hcap
    _ = (K.card : ℝ) * c := by simp

/-- Positive original cells supply actual representatives and the required
dense finite tuple count at once. -/
theorem original_positive_cells {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (code : Ω → ι) (K : Finset ι)
    (hcover : ∀ᵐ x ∂μ, x ∈ E → code x ∈ K) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ b ∈ K, μ.real (E ∩ code ⁻¹' {b}) ≤ c) :
    ∃ T : Finset ι, T ⊆ K ∧ μ.real E / c ≤ (T.card : ℝ) ∧
      ∀ b ∈ T, ∃ x ∈ E, code x = b := by
  classical
  let T := K.filter (fun b => 0 < μ.real (E ∩ code ⁻¹' {b}))
  have hTK : T ⊆ K := Finset.filter_subset _ _
  refine ⟨T, hTK, original_cell_count_lower μ E code T
    (positive_original_cells_cover_ae μ E code K hcover) hc
    (fun b hb => hcap b (hTK hb)), ?_⟩
  intro b hb
  have hp := (Finset.mem_filter.mp hb).2
  obtain ⟨x, hx⟩ := nonempty_of_measureReal_ne_zero (ne_of_gt hp)
  exact ⟨x, hx.1, hx.2⟩

/-- One starting scalar bin retains the original event mass divided by
the original bin count. No prior is renormalized in this selection. -/
theorem exists_heavy_original_cell {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (code : Ω → ι) (K : Finset ι)
    (hcover : ∀ᵐ x ∂μ, x ∈ E → code x ∈ K) {δ B : ℝ}
    (hδ : 0 < δ) (hmass : δ ≤ μ.real E) (hcard : (K.card : ℝ) ≤ B) :
    ∃ b ∈ K, δ / B ≤ μ.real (E ∩ code ⁻¹' {b}) := by
  have hsum := original_mass_le_sum_cells μ E code K hcover
  have hK : K.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hsum
    linarith
  have hB : 0 < B := lt_of_lt_of_le (Nat.cast_pos.mpr hK.card_pos) hcard
  obtain ⟨b, hb, hmax⟩ := K.exists_max_image (fun b => μ.real (E ∩ code ⁻¹' {b})) hK
  refine ⟨b, hb, (div_le_iff₀ hB).mpr ?_⟩
  calc
    δ ≤ ∑ b ∈ K, μ.real (E ∩ code ⁻¹' {b}) := hmass.trans hsum
    _ ≤ ∑ _b ∈ K, μ.real (E ∩ code ⁻¹' {b}) := Finset.sum_le_sum hmax
    _ = (K.card : ℝ) * μ.real (E ∩ code ⁻¹' {b}) := by simp
    _ ≤ B * μ.real (E ∩ code ⁻¹' {b}) :=
      mul_le_mul_of_nonneg_right hcard measureReal_nonneg
    _ = μ.real (E ∩ code ⁻¹' {b}) * B := mul_comm _ _

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
