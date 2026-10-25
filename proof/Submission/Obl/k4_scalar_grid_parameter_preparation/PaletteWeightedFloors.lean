/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/PaletteWeightedFloors.lean -/
import Submission.Obl.k4_scalar_grid_parameter_preparation.WeightedPartitionFloors
import Submission.Obl.k4_scalar_grid_parameter_preparation.PaletteWeightedCounts

/-! Stable joint cell/palette floors with cost independent of the number of palette bins. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem simultaneous_palette_weighted_floors {Ω I P V : Type*} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) (A : Set Ω) (hA : MeasurableSet A) (hAfin : μ A ≠ ∞)
    (phys : I → Ω → P) (vel : I → Ω → V)
    (hphys : ∀ i q, MeasurableSet {p | phys i p = q})
    (hvel : ∀ i c, MeasurableSet {p | vel i p = c})
    (hfinite : ∀ i, (phys i '' A).Finite) (hvfinite : ∀ i, (vel i '' A).Finite)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (L B : ℝ) (hB : 0 < B)
    (hcount : ∀ i, ((phys i '' A).ncard : ℝ) * w i ≤ L)
    (palette : I → V → ℝ≥0∞) (hpalette : ∀ i (S : Finset V), (∑ c ∈ S, palette i c) ≤ 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ A ∧
      μ (A \ E) ≤ ENNReal.ofReal ((Fintype.card I : ℝ) * L / B) ∧
      ∀ i p, p ∈ E → ENNReal.ofReal (w i / B) * palette i (vel i p) ≤
        μ (E ∩ {p' | phys i p' = phys i p ∧ vel i p' = vel i p}) := by
  classical
  let code : I → Ω → P × V := fun i p => (phys i p,vel i p)
  have hcode (i) (q : P × V) : MeasurableSet {p | code i p = q} := by
    rcases q with ⟨q,c⟩
    have he : {p | code i p = (q,c)} = {p | phys i p = q} ∩ {p | vel i p = c} := by
      ext p
      simp only [code,Prod.mk.injEq,Set.mem_inter_iff,Set.mem_ofPred_eq]
    rw [he]
    exact (hphys i q).inter (hvel i c)
  have hjoint (i) : (code i '' A).Finite := ((hfinite i).prod (hvfinite i)).subset (by
    rintro _ ⟨p,hp,rfl⟩
    exact ⟨⟨p,hp,rfl⟩,⟨p,hp,rfl⟩⟩)
  let D : I → Finset (P × V) := fun i => (hjoint i).toFinset
  have hfst (i) : (D i).image Prod.fst = (hfinite i).toFinset := by
    ext q
    constructor
    · intro hq
      obtain ⟨pc,hpc,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨p,hp,hp'⟩ := (hjoint i).mem_toFinset.mp hpc
      exact (hfinite i).mem_toFinset.mpr ⟨p,hp,congrArg Prod.fst hp'⟩
    · intro hq
      obtain ⟨p,hp,rfl⟩ := (hfinite i).mem_toFinset.mp hq
      exact Finset.mem_image.mpr ⟨code i p,(hjoint i).mem_toFinset.mpr ⟨p,hp,rfl⟩,rfl⟩
  have hinner (i) : (∑ qc ∈ D i, ENNReal.ofReal (w i / B) * palette i qc.2) ≤
      ENNReal.ofReal (L / B) := by
    have hs := sum_pair_palette_weights_le (D i) (palette i) (hpalette i _)
    calc
      _ = ENNReal.ofReal (w i / B) * (∑ qc ∈ D i, palette i qc.2) := (Finset.mul_sum _ _ _).symm
      _ ≤ ENNReal.ofReal (w i / B) * (((D i).image Prod.fst).card : ℝ≥0∞) :=
        mul_le_mul' le_rfl hs
      _ = ENNReal.ofReal (((phys i '' A).ncard : ℝ) * w i / B) := by
        rw [hfst,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (div_nonneg (hw i) hB.le),
          ← Set.ncard_eq_toFinset_card _ (hfinite i)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hcount i) hB.le)
  obtain ⟨E,hE,hsub,hloss,hfloor⟩ := simultaneous_weighted_partition_floors μ A hA hAfin code hcode hjoint
    (fun i qc => ENNReal.ofReal (w i / B) * palette i qc.2)
  have hbudget : (∑ i : I, ∑ qc ∈ D i, ENNReal.ofReal (w i / B) * palette i qc.2) ≤
      ENNReal.ofReal ((Fintype.card I : ℝ) * L / B) := by
    calc
      _ ≤ ∑ _i : I, ENNReal.ofReal (L / B) := Finset.sum_le_sum fun i _ => hinner i
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
        rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        ring
  refine ⟨E,hE,hsub,hloss.trans hbudget,?_⟩
  intro i p hp
  simpa only [code,Prod.mk.injEq] using hfloor i p hp

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
