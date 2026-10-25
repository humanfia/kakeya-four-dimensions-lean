import Submission.Obl.k4_scalar_grid_parameter_preparation.CoefficientEntries
import Submission.Obl.k4_scalar_grid_parameter_preparation.CoefficientCellLists
import Submission.Obl.k4_plank_projected_multiplicity.DirectionPacking

/-! Enumerate the actual original coefficient bins and restore their physical-cell entry floors. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators ENNReal

theorem finite_grid_coefficient_entry_pruning {X σ : Type*} [MeasurableSpace X] [Fintype σ]
    (μ : Measure (X × ℝ)) (θ : Measure X) (a : X → Fin 5 → ℝ) (ha : Measurable a)
    (E : Set (X × ℝ)) (hE : MeasurableSet E) (h : σ → ℝ) (K A : ℝ)
    (hh : ∀ s, 0 < h s) (hh₁ : ∀ s, h s ≤ 1) (hK : 1 ≤ K) (hA : 0 < A)
    (hpoint : ∀ z ∈ E, z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |a z.1 e| ≤ K) :
    ∃ R : Set (X × ℝ), MeasurableSet R ∧ R ⊆ E ∧
      μ (E \ R) ≤ ENNReal.ofReal ((Fintype.card σ : ℝ) * (5000 * 111 ^ 3) * K / A) * θ Set.univ ∧
      ∀ (s : σ) (q : Fin 3 → ℤ) (b : Fin 5 → ℤ),
        R ∩ {z | physicalScalarGridTag (h s) (scalarPacketPosition a z) = q ∧
          scalarMixedCoefficientTag (h s) (h s) (a z.1) = b} = ∅ ∨
        ENNReal.ofReal (h s / A) * θ {l | scalarMixedCoefficientTag (h s) (h s) (a l) = b} <
          μ (R ∩ {z | physicalScalarGridTag (h s) (scalarPacketPosition a z) = q ∧
            scalarMixedCoefficientTag (h s) (h s) (a z.1) = b}) := by
  classical
  let code := fun s l => scalarMixedCoefficientTag (h s) (h s) (a l)
  let Q := fun s => code s '' (Prod.fst '' E)
  have hQ (s) : (Q s).Finite := coefficient_grid_image_finite a E (h s) K (hh s)
    (fun z hz => (hpoint z hz).2)
  let κ := fun s => ↥(Q s)
  letI (s : σ) : Fintype (κ s) := (hQ s).fintype
  let n := fun s => Fintype.card (κ s)
  let idx : (s : σ) → Fin (n s) ≃ κ s := fun s => (Fintype.equivFin (κ s)).symm
  have hrep (s : σ) (j : Fin (n s)) : ∃ z ∈ E, code s z.1 = (idx s j).val := by
    obtain ⟨l,⟨z,hz,rfl⟩,hc⟩ := (idx s j).property
    exact ⟨z,hz,hc⟩
  choose rep hrepE hrepCode using hrep
  let B := fun s (j : Fin (n s)) => {l | code s l = (idx s j).val}
  have hmcode (s) : Measurable (code s) := (measurable_scalarMixedCoefficientTag _ _).comp ha
  have hB (s) (j : Fin (n s)) : MeasurableSet (B s j) :=
    measurableSet_eq_fun (hmcode s) measurable_const
  have hdisj (s) : Pairwise fun (j j' : Fin (n s)) => Disjoint (B s j) (B s j') := by
    intro j j' hne
    apply Set.disjoint_left.mpr
    intro l hl hl'
    apply hne
    apply (idx s).injective
    exact Subtype.ext (hl.symm.trans hl')
  let b₀ := fun s j => a (rep s j).1
  have hb₀ (s) (j : Fin (n s)) (e : Fin 5) : |b₀ s j e| ≤ K :=
    (hpoint (rep s j) (hrepE s j)).2 e
  have hblock (s) (j : Fin (n s)) (l : X) (hl : l ∈ B s j) (e : Fin 5) :
      |a l e - b₀ s j e| ≤ h s := by
    have hc : code s l = code s (rep s j).1 := hl.trans (hrepCode s j).symm
    apply Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq (hh s)
    simpa only [code,b₀,scalarMixedCoefficientTag,ite_self] using congrFun hc e
  obtain ⟨R,hR,hRE,hloss,hfloor⟩ := multiscale_quadratic_coefficient_entry_pruning n μ θ a ha
    B hB hdisj b₀ h (fun _ => A) hh hh₁ hK (fun _ => hA) hb₀ hblock hE
    (fun z hz => (hpoint z hz).1)
  refine ⟨R,hR,hRE,?_,?_⟩
  · apply hloss.trans_eq
    congr 1
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card σ))]
    congr 1
    ring
  · intro s q b
    by_cases hb : b ∈ Q s
    · let j : Fin (n s) := (Fintype.equivFin (κ s)) ⟨b,hb⟩
      have hj : idx s j = ⟨b,hb⟩ := (Fintype.equivFin (κ s)).symm_apply_apply _
      have hBj : B s j = {l | code s l = b} := by simp only [B,hj]
      have heq : R ∩ coefficientPhysicalEntry a (B s j) (h s) q =
          R ∩ {z | physicalScalarGridTag (h s) (scalarPacketPosition a z) = q ∧ code s z.1 = b} := by
        rw [hBj]
        ext z
        change (z ∈ R ∧ code s z.1 = b ∧ quadraticCoordinateCode (h s) (a z.1) z.2 = q) ↔
          (z ∈ R ∧ physicalScalarGridTag (h s) (scalarPacketPosition a z) = q ∧ code s z.1 = b)
        have hp : quadraticCoordinateCode (h s) (a z.1) z.2 =
            physicalScalarGridTag (h s) (scalarPacketPosition a z) := rfl
        rw [hp]
        tauto
      have hf := hfloor s j q
      rw [heq,hBj] at hf
      exact hf
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      apply hb
      exact ⟨z.1,⟨z,hRE hz.1,rfl⟩,hz.2.2⟩

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
