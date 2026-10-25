-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/GridMass.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/GridMass.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0352,
-- branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/GridMass.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.PhysicalSupport
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.CartesianGrids

/-!
Finite Cartesian targets retain original incidence mass. Light-cell
pruning, support density and target mass all use the same original law.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set

noncomputable section

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  [MeasurableSpace I] [MeasurableSingletonClass I]

omit [Fintype I] in
/-- The mass of an original finite code table is the sum of its ORIGINAL cell masses. -/
theorem original_code_table_mass (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → I) (hcode : Measurable code) (F : Finset I) :
    (∑ i ∈ F, μ.real {x | code x = i}) = μ.real {x | code x ∈ F} := by
  simpa only [Set.preimage, Set.mem_singleton_iff, Finset.mem_coe] using
    sum_measureReal_preimage_singleton (μ := μ) F
      (fun i _ => hcode (measurableSet_singleton i))

/-- The original finite-code light-cell budget in any finite label type. -/
theorem original_light_code_mass_le (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → I) (hcode : Measurable code) (a : ℝ) (ha : 0 ≤ a) :
    μ.real {x | μ.real {y | code y = code x} < a} ≤ (Fintype.card I : ℝ) * a := by
  let e := Fintype.equivFin I
  let finCode := e ∘ code
  have hfinCode : Measurable finCode := (measurable_of_finite e).comp hcode
  have hcell (i : I) : codeWeight μ finCode (e i) = μ.real {x | code x = i} := by
    dsimp only [codeWeight, finCode, Function.comp_apply]
    congr 1
    ext x
    exact e.injective.eq_iff
  have h := light_code_mass_le μ finCode hfinCode a ha
  simpa only [finCode, Function.comp_apply, hcell] using h

omit [Fintype I] in
/-- A selected target table inherits its original mass floor cell by cell. -/
theorem original_table_mass_floor (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → I) (hcode : Measurable code) (F : Finset I) (a : ℝ)
    (hfloor : ∀ i ∈ F, a ≤ μ.real {x | code x = i}) :
    a * (F.card : ℝ) ≤ μ.real {x | code x ∈ F} := by
  rw [← original_code_table_mass μ code hcode F]
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
    Finset.sum_le_sum (s := F) (fun i hi => hfloor i hi)

open Classical in
/-- Delete light cells using their original masses. The same cell cap U
then supplies a quantitative lower bound for the surviving cell count. -/
theorem prepare_original_grid_cells (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → I) (hcode : Measurable code) (a U : ℝ) (ha : 0 ≤ a) (hU : 0 < U)
    (hcap : ∀ i, μ.real {x | code x = i} ≤ U) :
    ∃ F : Finset I,
      (∀ i, i ∈ F ↔ a ≤ μ.real {x | code x = i}) ∧
      μ.real {x | code x ∉ F} ≤ (Fintype.card I : ℝ) * a ∧
      (μ.real univ - (Fintype.card I : ℝ) * a) / U ≤ (F.card : ℝ) ∧
      ∀ G : Finset I, G ⊆ F → a * (G.card : ℝ) ≤ μ.real {x | code x ∈ G} := by
  let F := Finset.univ.filter fun i : I => a ≤ μ.real {x | code x = i}
  have hmem (i : I) : i ∈ F ↔ a ≤ μ.real {x | code x = i} := by simp only [F, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hT : MeasurableSet {x | code x ∈ F} :=
    hcode (Set.Finite.measurableSet (Set.toFinite (F : Set I)))
  have hbad : μ.real {x | code x ∉ F} ≤ (Fintype.card I : ℝ) * a := by
    simpa only [hmem, not_le] using original_light_code_mass_le μ code hcode a ha
  have hsum := measureReal_add_measureReal_compl (μ := μ) hT
  have hmass : μ.real {x | code x ∈ F} ≤ U * (F.card : ℝ) := by
    rw [← original_code_table_mass μ code hcode F]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
      Finset.sum_le_sum (s := F) (fun i _ => hcap i)
  refine ⟨F, hmem, hbad, ?_, ?_⟩
  · apply (div_le_iff₀ hU).mpr
    change μ.real {x | code x ∈ F} + μ.real {x | code x ∉ F} = μ.real univ at hsum
    nlinarith
  · intro G hGF
    exact original_table_mass_floor μ code hcode G a (fun i hi => (hmem i).mp (hGF hi))

namespace Cartesian

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

def uniformWeight (X : Type*) [Fintype X] : X → ℝ := fun _ => 1 / Fintype.card X

def gridTableMember (F : Finset (X × Y × Z)) (x : X) (y : Y) (z : Z) : Prop :=
  (x, y, z) ∈ F

theorem sum_uniformWeight [Nonempty X] : (∑ x : X, uniformWeight X x) = 1 := by
  simp [uniformWeight, div_eq_mul_inv, Fintype.card_ne_zero]

open Classical in
/-- The uniform three-axis density is exactly the finite target count. -/
theorem uniform_triple_density (R : X → Y → Z → Prop) :
    mean (uniformWeight X) (fun x => mean (uniformWeight Y) (fun y =>
      mean (uniformWeight Z) (fun z => if R x y z then (1 : ℝ) else 0))) =
      ((Finset.univ.filter fun a : X × Y × Z => R a.1 a.2.1 a.2.2).card : ℝ) /
        ((Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z) := by
  have hsum : (∑ x, ∑ y, ∑ z, if R x y z then (1 : ℝ) else 0) =
      ((Finset.univ.filter fun a : X × Y × Z => R a.1 a.2.1 a.2.2).card : ℝ) := by
    symm
    simp only [← Finset.sum_boole, Fintype.sum_prod_type]
  simp only [mean, uniformWeight, ← Finset.mul_sum]
  rw [← hsum]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end Cartesian

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
