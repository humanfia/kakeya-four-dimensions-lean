/-
Adapted from: here:o222 (x0774), MeshBaseDomination.lean, commit 109e510d.
-/
import Submission.Lib.K4MovingMeshBoxes.Geometry

/-! Finite-mesh domination controls the volume of mesh-enlarged sets. -/

namespace Submission.Lib.K4AffineMeshCaps

open MeasureTheory Set

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev baseMesh := @Submission.Lib.K4MovingMeshBoxes.baseMesh
abbrev interval_mesh_cover := @Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover

theorem measurable_baseMesh (delta : ℝ) : Measurable (baseMesh delta) := by
  unfold baseMesh Submission.Lib.K4MovingMeshBoxes.baseMesh
  fun_prop

def meshBox (delta : ℝ) (q : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  {z | baseMesh delta z = q}

theorem measurableSet_meshBox (delta : ℝ) (q : Fin 3 → ℤ) :
    MeasurableSet (meshBox delta q) := by
  have hm : Measurable (baseMesh delta) := measurable_baseMesh delta
  exact hm (measurableSet_singleton q)

theorem volume_meshBox {delta : ℝ} (hd : 0 < delta) (q : Fin 3 → ℤ) :
    volume (meshBox delta q) = ENNReal.ofReal (delta ^ 3) := by
  have hbox : meshBox delta q =
      univ.pi (fun i => Ico ((q i : ℝ) * delta) (((q i : ℝ) + 1) * delta)) := by
    ext z
    simp only [meshBox, baseMesh, Submission.Lib.K4MovingMeshBoxes.baseMesh,
      mem_ofPred_eq, funext_iff, mem_pi, mem_univ, forall_const]
    apply forall_congr'
    intro i
    rw [Int.floor_eq_iff, le_div_iff₀ hd, div_lt_iff₀ hd]
    rfl
  rw [hbox, Real.volume_pi_Ico]
  have hlength (i : Fin 3) : ((q i : ℝ) + 1) * delta - (q i : ℝ) * delta = delta := by ring
  simp_rw [hlength]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hd.le)]
  simp only [Fin.prod_univ_three]
  congr 1
  ring

theorem meshBox_pairwiseDisjoint (delta : ℝ) :
    Pairwise (fun q q' : Fin 3 → ℤ => Disjoint (meshBox delta q) (meshBox delta q')) := by
  intro q q' hne
  apply disjoint_left.mpr
  intro z hz hz'
  exact hne (hz.symm.trans hz')

theorem meshBox_coordinate_distance {delta : ℝ} (hd : 0 < delta)
    {q : Fin 3 → ℤ} {z w : Fin 3 → ℝ}
    (hz : z ∈ meshBox delta q) (hw : w ∈ meshBox delta q) (i : Fin 3) :
    |z i - w i| ≤ delta := by
  have hzi := Int.floor_eq_iff.mp (congrFun hz i)
  have hwi := Int.floor_eq_iff.mp (congrFun hw i)
  rw [le_div_iff₀ hd, div_lt_iff₀ hd] at hzi hwi
  rw [abs_le]
  constructor <;> nlinarith only [hzi.1, hzi.2, hwi.1, hwi.2]

def selectedMeshCell (delta : ℝ) (S : Set (Fin 3 → ℝ)) (q : Fin 3 → ℤ) :
    Set (Fin 3 → ℝ) :=
  if ∃ z ∈ S, baseMesh delta z = q then meshBox delta q else ∅

def meshSaturation (delta : ℝ) (S : Set (Fin 3 → ℝ)) : Set (Fin 3 → ℝ) :=
  ⋃ q : Fin 3 → ℤ, selectedMeshCell delta S q

theorem selectedMeshCell_subset (delta : ℝ) (S : Set (Fin 3 → ℝ)) (q : Fin 3 → ℤ) :
    selectedMeshCell delta S q ⊆ meshBox delta q := by
  unfold selectedMeshCell
  split_ifs <;> simp

theorem measurableSet_selectedMeshCell (delta : ℝ) (S : Set (Fin 3 → ℝ))
    (q : Fin 3 → ℤ) : MeasurableSet (selectedMeshCell delta S q) := by
  unfold selectedMeshCell
  split_ifs
  · exact measurableSet_meshBox delta q
  · exact MeasurableSet.empty

theorem selectedMeshCell_pairwiseDisjoint (delta : ℝ) (S : Set (Fin 3 → ℝ)) :
    Pairwise (fun q q' : Fin 3 → ℤ =>
      Disjoint (selectedMeshCell delta S q) (selectedMeshCell delta S q')) := by
  intro q q' hne
  exact (meshBox_pairwiseDisjoint delta hne).mono
    (selectedMeshCell_subset delta S q) (selectedMeshCell_subset delta S q')

theorem measurableSet_meshSaturation (delta : ℝ) (S : Set (Fin 3 → ℝ)) :
    MeasurableSet (meshSaturation delta S) :=
  MeasurableSet.iUnion (measurableSet_selectedMeshCell delta S)

theorem subset_meshSaturation (delta : ℝ) (S : Set (Fin 3 → ℝ)) :
    S ⊆ meshSaturation delta S := by
  intro z hz
  apply mem_iUnion.mpr
  refine ⟨baseMesh delta z, ?_⟩
  simp only [selectedMeshCell, if_pos (show ∃ w ∈ S, baseMesh delta w = baseMesh delta z from
    ⟨z, hz, rfl⟩)]
  rfl

theorem meshSaturation_close {delta : ℝ} (hd : 0 < delta)
    (S : Set (Fin 3 → ℝ)) {z : Fin 3 → ℝ} (hz : z ∈ meshSaturation delta S) :
    ∃ w ∈ S, ∀ i, |z i - w i| ≤ delta := by
  obtain ⟨q, hq⟩ := mem_iUnion.mp hz
  unfold selectedMeshCell at hq
  split_ifs at hq with h
  · obtain ⟨w, hw, hcode⟩ := h
    exact ⟨w, hw, fun i => meshBox_coordinate_distance hd hq hcode i⟩
  · exact hq.elim

/-- A mesh cap implies domination by the volume of the mesh saturation,
without asserting continuous domination by the volume of the original set. -/
theorem measure_le_meshSaturation_volume {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    {delta C : ℝ} (hd : 0 < delta) (hC : 0 ≤ C)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh delta (Z p) = q ∧ condition p} ≤ ENNReal.ofReal (C * delta ^ 3))
    (S : Set (Fin 3 → ℝ)) :
    μ {p | Z p ∈ S ∧ condition p} ≤ ENNReal.ofReal C * volume (meshSaturation delta S) := by
  let E (q : Fin 3 → ℤ) : Set Ω :=
    {p | Z p ∈ S ∧ condition p ∧ baseMesh delta (Z p) = q}
  have hsub : {p | Z p ∈ S ∧ condition p} ⊆ ⋃ q, E q := by
    intro p hp
    exact mem_iUnion.mpr ⟨baseMesh delta (Z p), hp.1, hp.2, rfl⟩
  have hcell (q : Fin 3 → ℤ) :
      μ (E q) ≤ ENNReal.ofReal C * volume (selectedMeshCell delta S q) := by
    by_cases hq : ∃ z ∈ S, baseMesh delta z = q
    · rw [selectedMeshCell, if_pos hq, volume_meshBox hd, ← ENNReal.ofReal_mul hC]
      apply (measure_mono (show E q ⊆ {p | baseMesh delta (Z p) = q ∧ condition p} from
        fun p hp => ⟨hp.2.2, hp.2.1⟩)).trans
      exact hcap q
    · have hE : E q = ∅ := by
        ext p
        constructor
        · intro hp
          exact (hq ⟨Z p, hp.1, hp.2.2⟩).elim
        · exact fun hp => hp.elim
      rw [hE, measure_empty]
      exact bot_le
  calc
    _ ≤ μ (⋃ q, E q) := measure_mono hsub
    _ ≤ ∑' q, μ (E q) := measure_iUnion_le _
    _ ≤ ∑' q, ENNReal.ofReal C * volume (selectedMeshCell delta S q) := ENNReal.tsum_le_tsum hcell
    _ = _ := by
      rw [ENNReal.tsum_mul_left]
      rw [meshSaturation, measure_iUnion (selectedMeshCell_pairwiseDisjoint delta S)
        (measurableSet_selectedMeshCell delta S)]

theorem ofReal_le_meshSaturation_volume {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (condition : Ω → Prop)
    {delta C eta : ℝ} (hd : 0 < delta) (hC : 0 < C)
    (hcap : ∀ q : Fin 3 → ℤ,
      μ {p | baseMesh delta (Z p) = q ∧ condition p} ≤ ENNReal.ofReal (C * delta ^ 3))
    (S : Set (Fin 3 → ℝ))
    (hmass : ENNReal.ofReal (C * eta) ≤ μ {p | Z p ∈ S ∧ condition p}) :
    ENNReal.ofReal eta ≤ volume (meshSaturation delta S) := by
  have hh := hmass.trans (measure_le_meshSaturation_volume μ Z condition hd hC.le hcap S)
  rw [ENNReal.ofReal_mul hC.le] at hh
  have hC0 : ENNReal.ofReal C ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hC)
  have hcancel := ENNReal.mul_inv_cancel hC0 ENNReal.ofReal_ne_top
  have hmul := mul_le_mul' hh (le_refl ((ENNReal.ofReal C)⁻¹))
  calc
    ENNReal.ofReal eta = (ENNReal.ofReal C * (ENNReal.ofReal C)⁻¹) * ENNReal.ofReal eta := by
      rw [hcancel, one_mul]
    _ = (ENNReal.ofReal C * ENNReal.ofReal eta) * (ENNReal.ofReal C)⁻¹ := by ac_rfl
    _ ≤ (ENNReal.ofReal C * volume (meshSaturation delta S)) * (ENNReal.ofReal C)⁻¹ := hmul
    _ = (ENNReal.ofReal C * (ENNReal.ofReal C)⁻¹) * volume (meshSaturation delta S) := by ac_rfl
    _ = volume (meshSaturation delta S) := by rw [hcancel, one_mul]

end

end Submission.Lib.K4AffineMeshCaps
