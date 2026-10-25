import Submission.Obl.k4_general_wide_layer_offset_comparison.RawMeshCoupling
import Submission.Obl.k4_general_wide_layer_offset_comparison.PairedSourceLaws
import Submission.Obl.k4_scalar_candidate_original_return.Core.MatchApply

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/MatchingMeshCoupling.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open Submission.Lib.K4OriginalStatePreparation
open scoped ENNReal

noncomputable section

/-- Smooth a two-dimensional observed base directly into the three-dimensional
matching base, adding the accepted uniform dummy coordinate in each cell. -/
def matchingMeshCoupling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 2 → ℝ) (δ : ℝ) (Q : Finset (Fin 2 → ℤ)) :
    Measure (Ω × EuclideanSpace ℝ (Fin 3)) :=
  cellCoupling
    (fun q : Q => μ.restrict {ω | meshCode2 δ (Z ω) = q.val})
    (fun q : Q => Submission.Obl.k4_scalar_candidate_original_return.MatchApply.U (meshCell2 δ q.val))

theorem matching_cell_probability {δ : ℝ} (hδ : 0 < δ) (q : Fin 2 → ℤ) :
    IsProbabilityMeasure (Submission.Obl.k4_scalar_candidate_original_return.MatchApply.U (meshCell2 δ q)) := by
  constructor
  exact Submission.Obl.k4_scalar_candidate_original_return.MatchApply.U_univ
    (measurableSet_meshCell2 δ q) (by rw [volume_meshCell2 hδ.le]; positivity)
    (by rw [volume_meshCell2 hδ.le]; finiteness)

theorem matchingMeshCoupling_fst {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂μ, meshCode2 δ (Z ω) ∈ Q) :
    (matchingMeshCoupling μ Z δ Q).map Prod.fst = μ := by
  haveI (q : Q) := matching_cell_probability hδ q.val
  rw [matchingMeshCoupling, cellCoupling_fst]
  apply partition_restrict_sum
  · intro q
    exact measurableSet_eq_fun ((measurable_meshCode2 δ).comp hZ) measurable_const
  · intro q q' hne
    exact Set.disjoint_left.mpr (fun ω hω hω' => hne (Subtype.ext (hω.symm.trans hω')))
  · filter_upwards [hcover] with ω hω
    exact ⟨⟨meshCode2 δ (Z ω), hω⟩, rfl⟩

theorem matchingMeshCoupling_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ)) :
    IsFiniteMeasure (matchingMeshCoupling μ Z δ Q) := by
  haveI (q : Q) := matching_cell_probability hδ q.val
  exact cellCoupling_finite _ _

theorem matchingMeshCoupling_support {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ)) :
    ∀ᵐ z ∂matchingMeshCoupling μ Z δ Q, ∃ q : Q,
      meshCode2 δ (Z z.1) = q.val ∧
      z.2 ∈ Submission.Obl.k4_scalar_candidate_original_return.MatchApply.box (meshCell2 δ q.val) := by
  haveI (q : Q) := matching_cell_probability hδ q.val
  apply cellCoupling_support
    (fun q : Q => μ.restrict {ω | meshCode2 δ (Z ω) = q.val})
    (fun q : Q => Submission.Obl.k4_scalar_candidate_original_return.MatchApply.U (meshCell2 δ q.val))
    (fun q : Q => {ω | meshCode2 δ (Z ω) = q.val})
    (fun q : Q => Submission.Obl.k4_scalar_candidate_original_return.MatchApply.box (meshCell2 δ q.val))
  · intro q
    exact ae_restrict_mem (measurableSet_eq_fun ((measurable_meshCode2 δ).comp hZ) measurable_const)
  · intro q
    rw [ae_iff]
    exact Submission.Obl.k4_scalar_candidate_original_return.MatchApply.U_compl_box
      (measurableSet_meshCell2 δ q.val)

theorem matchingMeshCoupling_close {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ)) :
    ∀ᵐ z ∂matchingMeshCoupling μ Z δ Q, ∀ i : Fin 2,
      |Z z.1 i - z.2 i.castSucc| ≤ δ := by
  filter_upwards [matchingMeshCoupling_support μ Z hZ hδ Q] with z hz
  obtain ⟨q, hq, hz⟩ := hz
  have hy := (Submission.Obl.k4_scalar_candidate_original_return.MatchApply.mem_box.mp hz).2
  exact meshCode2_close hδ (hq.trans ((mem_meshCell2_iff hδ q.val _).mp hy).symm)

/-- Original eventwise cell ceilings become three-dimensional index/base
ceilings. Only the fixed dummy-coordinate density factor four is incurred. -/
theorem matchingMeshCoupling_density {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ)
    {δ : ℝ} {A : ℝ≥0∞} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ))
    (E : Set Ω) (hE : MeasurableSet E)
    (hcap : ∀ q ∈ Q, μ {ω | meshCode2 δ (Z ω) = q ∧ ω ∈ E} ≤
      A * ENNReal.ofReal (δ ^ 2))
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : MeasurableSet U) :
    matchingMeshCoupling μ Z δ Q (E ×ˢ U) ≤ (4 * A) * volume U := by
  haveI (q : Q) := matching_cell_probability hδ q.val
  let V : ℝ≥0∞ := ENNReal.ofReal (1 / 4) * ENNReal.ofReal (δ ^ 2)
  have hV : V ≠ 0 := by dsimp [V]; positivity
  have hVtop : V ≠ ⊤ := by dsimp [V]; finiteness
  apply cellCoupling_density _ _ volume
    (fun q : Q => Submission.Obl.k4_scalar_candidate_original_return.MatchApply.box (meshCell2 δ q.val))
    (fun q => Submission.Obl.k4_scalar_candidate_original_return.MatchApply.box_measurable
      (measurableSet_meshCell2 δ q.val))
    (fun q q' hne => Submission.Obl.k4_scalar_candidate_original_return.MatchApply.box_disjoint
      (meshCell2_disjoint hδ (fun he => hne (Subtype.ext he))))
    V (4 * A) hV hVtop E
  · intro q
    rw [Measure.restrict_apply hE]
    calc
      _ = μ {ω | meshCode2 δ (Z ω) = q.val ∧ ω ∈ E} := by
        congr 1
        ext ω
        exact and_comm
      _ ≤ A * ENNReal.ofReal (δ ^ 2) := hcap q.val q.property
      _ = _ := by
        dsimp [V]
        have hf : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 4) = 1 := by
          rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
        calc
          _ = ((4 : ℝ≥0∞) * ENNReal.ofReal (1 / 4)) * A * ENNReal.ofReal (δ ^ 2) := by rw [hf, one_mul]
          _ = _ := by ring
  · intro q W hW
    rw [Submission.Obl.k4_scalar_candidate_original_return.MatchApply.U_apply hW]
    rw [Submission.Obl.k4_scalar_candidate_original_return.MatchApply.volume_box
      (measurableSet_meshCell2 δ q.val), volume_meshCell2 hδ.le]
  · exact hU

/-- Every original source record survives unchanged in the matching lift. -/
theorem matchingMeshCoupling_ae_original {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂μ, meshCode2 δ (Z ω) ∈ Q)
    {P : Ω → Prop} (hP : ∀ᵐ ω ∂μ, P ω) :
    ∀ᵐ z ∂matchingMeshCoupling μ Z δ Q, P z.1 := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  rw [matchingMeshCoupling_fst μ Z hZ hδ Q hcover]
  exact hP

/-- A source in the inner square remains inside the real matching half ball
when the original cells are sufficiently fine. -/
theorem matchingMeshCoupling_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂μ, meshCode2 δ (Z ω) ∈ Q)
    (hbound : ∀ᵐ ω ∂μ, ∀ i, |Z ω i| ≤ 1 / 8) :
    ∀ᵐ z ∂matchingMeshCoupling μ Z δ Q, ‖z.2‖ ≤ 1 / 2 := by
  filter_upwards [matchingMeshCoupling_ae_original μ Z hZ hδ Q hcover hbound,
    matchingMeshCoupling_close μ Z hZ hδ Q,
    matchingMeshCoupling_support μ Z hZ hδ Q] with z hb hc hs
  obtain ⟨q, hq, hs⟩ := hs
  apply Submission.Obl.k4_scalar_candidate_original_return.MatchApply.norm_le_of_mem_box
    (S := Submission.Obl.k4_scalar_candidate_original_return.MatchApply.sq (1 / 4)) Subset.rfl
  apply Submission.Obl.k4_scalar_candidate_original_return.MatchApply.mem_box.mpr
  refine ⟨(Submission.Obl.k4_scalar_candidate_original_return.MatchApply.mem_box.mp hs).1, ?_⟩
  intro i
  have ht : |z.2 i.castSucc| ≤ |z.2 i.castSucc - Z z.1 i| + |Z z.1 i| := by
    simpa only [sub_zero] using abs_sub_le (z.2 i.castSucc) (Z z.1 i) 0
  have h := ht.trans (add_le_add (by simpa only [abs_sub_comm] using hc i) (hb i))
  linarith

/-- Native prediction errors survive the literal matching lift. Only the
resolved projected polynomial is moved, and the native signal stays original. -/
theorem matchingMeshCoupling_prediction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin 2 → ℝ) (hZ : Measurable Z)
    {δ a e : ℝ} (hδ : 0 < δ) (Q : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ ω ∂μ, meshCode2 δ (Z ω) ∈ Q)
    (f : Ω → (Fin 2 → ℝ) → ℝ) (signal : Ω → ℝ)
    (hsource : ∀ᵐ ω ∂μ,
      |f ω (Z ω) - signal ω| ≤ a ∧
      ∀ y, (∀ i, |Z ω i - y i| ≤ δ) → |f ω (Z ω) - f ω y| ≤ e) :
    ∀ᵐ z ∂matchingMeshCoupling μ Z δ Q,
      |f z.1 (fun i => z.2 i.castSucc) - signal z.1| ≤ a + e := by
  filter_upwards [matchingMeshCoupling_ae_original μ Z hZ hδ Q hcover hsource,
    matchingMeshCoupling_close μ Z hZ hδ Q] with z hz hc
  have he := hz.2 (fun i => z.2 i.castSucc) hc
  calc
    _ ≤ |f z.1 (fun i => z.2 i.castSucc) - f z.1 (Z z.1)| +
        |f z.1 (Z z.1) - signal z.1| := abs_sub_le _ _ _
    _ ≤ e + a := add_le_add (by simpa only [abs_sub_comm] using he) hz.1
    _ = _ := add_comm _ _

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
