/-
Adapted from: here:o265
Original proofs by x1027.
-/
import Submission.Lib.K4StateFractionKeep

/-!
# A maximal intercept bin with one retained branch

Selecting a largest bin controls its five-bin state saturation. After choosing the heavier
Boolean branch, state-fraction pruning retains its mass and transfers every strip estimate.
All estimates use the original measure.
-/

namespace Submission.Lib.K4ParentSignalPreparation.BranchGroups

open Set MeasureTheory
open scoped NNReal ENNReal

noncomputable section

variable {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I] [Countable I]
  [MeasurableSingletonClass I]

def binGroup (E : Set Ω) (bin : Ω → ℤ) (z : ℤ) : Set Ω := E ∩ bin ⁻¹' {z}

theorem exists_maximal_bin (μ : Measure Ω) (E : Set Ω) (bin : Ω → ℤ)
    (hE : ∀ᵐ x ∂μ, x ∈ E) (S : Finset ℤ) (hS : S.Nonempty)
    (hcat : ∀ x ∈ E, bin x ∈ S) :
    ∃ z ∈ S, (∀ w : ℤ, μ (binGroup E bin w) ≤ μ (binGroup E bin z)) ∧
      μ univ ≤ S.card * μ (binGroup E bin z) := by
  classical
  obtain ⟨z, hz, hmax⟩ := S.exists_max_image (fun z => μ (binGroup E bin z)) hS
  have hmaxAll (w : ℤ) : μ (binGroup E bin w) ≤ μ (binGroup E bin z) := by
    by_cases hw : w ∈ S
    · exact hmax w hw
    · have he : binGroup E bin w = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hw (by rw [← hx.2]; exact hcat x hx.1)
      simp only [he, measure_empty]
      exact zero_le
  refine ⟨z, hz, hmaxAll, ?_⟩
  have hcover : univ ≤ᵐ[μ] ⋃ w ∈ S, binGroup E bin w := by
    filter_upwards [hE] with x hx _
    exact mem_iUnion₂.mpr ⟨bin x, hcat x hx, hx, rfl⟩
  calc
    μ univ ≤ μ (⋃ w ∈ S, binGroup E bin w) := measure_mono_ae hcover
    _ ≤ ∑ w ∈ S, μ (binGroup E bin w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ S, μ (binGroup E bin z) := Finset.sum_le_sum (fun w _ => hmaxAll w)
    _ = S.card * μ (binGroup E bin z) := by simp [nsmul_eq_mul]

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
/-- A finite state saturation of a maximal bin costs at most five times its mass. -/
theorem saturation_le_five (μ : Measure Ω) (E : Set Ω) (bin : Ω → ℤ) (state : Ω → I)
    (hE : ∀ᵐ x ∂μ, x ∈ E) (z : ℤ) (G : Set Ω) (hG : G ⊆ binGroup E bin z)
    (hclose : ∀ x ∈ E, ∀ y ∈ E, state x = state y → bin x ∈ Icc (bin y - 2) (bin y + 2))
    (hmax : ∀ w : ℤ, μ (binGroup E bin w) ≤ μ (binGroup E bin z)) :
    μ (state ⁻¹' {i | (G ∩ state ⁻¹' {i}).Nonempty}) ≤ 5 * μ (binGroup E bin z) := by
  classical
  let Z := Finset.Icc (z - 2) (z + 2)
  have hcover : state ⁻¹' {i | (G ∩ state ⁻¹' {i}).Nonempty} ≤ᵐ[μ]
      ⋃ w ∈ Z, binGroup E bin w := by
    filter_upwards [hE] with x hx hxs
    obtain ⟨y, hyG, hys⟩ := hxs
    have hy := hG hyG
    have hxy : state x = state y := hys.symm
    have hnear := hclose x hx y hy.1 hxy
    rw [hy.2] at hnear
    exact mem_iUnion₂.mpr ⟨bin x, Finset.mem_Icc.mpr hnear, hx, rfl⟩
  have hcard : Z.card = 5 := by
    dsimp [Z]
    rw [Int.card_Icc]
    have h : z + 2 + 1 - (z - 2) = (5 : ℤ) := by ring
    rw [h]
    rfl
  calc
    μ (state ⁻¹' {i | (G ∩ state ⁻¹' {i}).Nonempty}) ≤
        μ (⋃ w ∈ Z, binGroup E bin w) := measure_mono_ae hcover
    _ ≤ ∑ w ∈ Z, μ (binGroup E bin w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ Z, μ (binGroup E bin z) := Finset.sum_le_sum (fun w _ => hmax w)
    _ = 5 * μ (binGroup E bin z) := by simp [hcard, nsmul_eq_mul]

theorem exists_heavier_branch (μ : Measure Ω) (G : Set Ω) (branch : Ω → Bool) :
    ∃ β : Bool, μ G ≤ 2 * μ (G ∩ branch ⁻¹' {β}) := by
  have hcover : G ⊆ (G ∩ branch ⁻¹' {false}) ∪ (G ∩ branch ⁻¹' {true}) := by
    intro x hx
    cases h : branch x
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hsum : μ G ≤ μ (G ∩ branch ⁻¹' {false}) + μ (G ∩ branch ⁻¹' {true}) :=
    (measure_mono (μ := μ) hcover).trans (measure_union_le _ _)
  by_cases h : μ (G ∩ branch ⁻¹' {false}) ≤ μ (G ∩ branch ⁻¹' {true})
  · refine ⟨true, hsum.trans ?_⟩
    calc
      μ (G ∩ branch ⁻¹' {false}) + μ (G ∩ branch ⁻¹' {true}) ≤
          μ (G ∩ branch ⁻¹' {true}) + μ (G ∩ branch ⁻¹' {true}) := add_le_add h le_rfl
      _ = 2 * μ (G ∩ branch ⁻¹' {true}) := by ring
  · refine ⟨false, hsum.trans ?_⟩
    calc
      μ (G ∩ branch ⁻¹' {false}) + μ (G ∩ branch ⁻¹' {true}) ≤
          μ (G ∩ branch ⁻¹' {false}) + μ (G ∩ branch ⁻¹' {false}) :=
            add_le_add le_rfl (le_of_not_ge h)
      _ = 2 * μ (G ∩ branch ⁻¹' {false}) := by ring

/-- The largest bin, a heavier Boolean branch and one state-fraction cut give a measurable
one-branch source with a quantitative original mass floor and renewed ratios. -/
theorem exists_retained_branch (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) (hEm : MeasurableSet E) (hE : ∀ᵐ x ∂μ, x ∈ E)
    (bin : Ω → ℤ) (hbin : Measurable bin) (state : Ω → I) (hstate : Measurable state)
    (branch : Ω → Bool) (hbranch : Measurable branch)
    (S : Finset ℤ) (hS : S.Nonempty) (hcat : ∀ x ∈ E, bin x ∈ S)
    (hclose : ∀ x ∈ E, ∀ y ∈ E, state x = state y → bin x ∈ Icc (bin y - 2) (bin y + 2)) :
    ∃ (z : ℤ) (β : Bool) (K : Set Ω), z ∈ S ∧ MeasurableSet K ∧
      K ⊆ binGroup E bin z ∩ branch ⁻¹' {β} ∧
      μ univ ≤ (4 * S.card : ENNReal) * μ K ∧
      μ ((binGroup E bin z ∩ branch ⁻¹' {β}) \ K) ≤
        (1 / 100000000 : ENNReal) * μ (binGroup E bin z ∩ branch ⁻¹' {β}) ∧
      (∀ Q : Set Ω, MeasurableSet Q →
        (∀ i : I, μ (state ⁻¹' {i} ∩ Q) ≤
          (1 / 1000000000000 : ENNReal) * μ (state ⁻¹' {i})) →
        ∀ L : Set I, μ (K ∩ state ⁻¹' L ∩ Q) ≤
          (1 / 1000 : ENNReal) * μ (K ∩ state ⁻¹' L)) := by
  obtain ⟨z, hz, hmax, htotal⟩ := exists_maximal_bin μ E bin hE S hS hcat
  obtain ⟨β, hβ⟩ := exists_heavier_branch μ (binGroup E bin z) branch
  let G := binGroup E bin z ∩ branch ⁻¹' {β}
  have hGm : MeasurableSet G := (hEm.inter (hbin (measurableSet_singleton z))).inter
    (hbranch (measurableSet_singleton β))
  let K := Submission.Lib.K4StateFractionKeep.fractionKeep μ state G (1 / 1000000000)
  have hKm : MeasurableSet K :=
    Submission.Lib.K4StateFractionKeep.measurableSet_fractionKeep hstate hGm _
  have hKG : K ⊆ G := inter_subset_left
  have hsat : μ (state ⁻¹' {i | (G ∩ state ⁻¹' {i}).Nonempty}) ≤ 10 * μ G := by
    calc
      _ ≤ 5 * μ (binGroup E bin z) :=
        saturation_le_five μ E bin state hE z G inter_subset_left hclose hmax
      _ ≤ 5 * (2 * μ G) := mul_le_mul' le_rfl hβ
      _ = 10 * μ G := by ring
  have hdel : μ (G \ K) ≤ (1 / 100000000 : ENNReal) * μ G := by
    calc
      μ (G \ K) ≤ (1 / 1000000000 : ENNReal) *
          μ (state ⁻¹' {i | (G ∩ state ⁻¹' {i}).Nonempty}) :=
        Submission.Lib.K4StateFractionKeep.measure_diff_fractionKeep_le μ hstate G _
      _ ≤ (1 / 1000000000 : ENNReal) * (10 * μ G) := mul_le_mul' le_rfl hsat
      _ = (1 / 100000000 : ENNReal) * μ G := by
        rw [← mul_assoc]
        congr 1
        rw [← ENNReal.coe_one, ← ENNReal.coe_ofNat, ← ENNReal.coe_ofNat, ← ENNReal.coe_ofNat]
        rw [← ENNReal.coe_div (by norm_num : (1000000000 : ℝ≥0) ≠ 0),
          ← ENNReal.coe_div (by norm_num : (100000000 : ℝ≥0) ≠ 0), ← ENNReal.coe_mul]
        norm_num
  have hkeep : μ G ≤ 2 * μ K := by
    have hmass : μ G ≤ μ K + (1 / 100000000 : ENNReal) * μ G := by
      calc
        μ G = μ K + μ (G \ K) := by
          rw [← measure_inter_add_sdiff G hKm, inter_eq_right.mpr hKG]
        _ ≤ _ := add_le_add le_rfl hdel
    have hsub : (1 - (1 / 100000000 : ENNReal)) * μ G ≤ μ K := by
      rw [ENNReal.sub_mul (fun _ _ => measure_ne_top μ G), one_mul]
      exact tsub_le_iff_right.mpr hmass
    have hhalf : (1 / 2 : ENNReal) * μ G ≤ μ K := by
      have hcoef : (1 / 2 : ENNReal) ≤ 1 - 1 / 100000000 := by
        rw [← ENNReal.coe_one, ← ENNReal.coe_ofNat, ← ENNReal.coe_ofNat]
        rw [← ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0),
          ← ENNReal.coe_div (by norm_num : (100000000 : ℝ≥0) ≠ 0),
          ← ENNReal.coe_sub, ENNReal.coe_le_coe]
        apply NNReal.coe_le_coe.mp
        norm_num [NNReal.sub_def]
      exact (mul_le_mul' hcoef le_rfl).trans hsub
    calc
      μ G = 2 * ((1 / 2 : ENNReal) * μ G) := by
        rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2 * μ K := mul_le_mul' le_rfl hhalf
  refine ⟨z, β, K, hz, hKm, hKG, ?_, hdel, ?_⟩
  · calc
      μ univ ≤ S.card * μ (binGroup E bin z) := htotal
      _ ≤ S.card * (2 * μ G) := mul_le_mul' le_rfl hβ
      _ ≤ S.card * (2 * (2 * μ K)) := by gcongr
      _ = (4 * S.card : ENNReal) * μ K := by ring
  · intro Q hQ hQratio L
    have h := Submission.Lib.K4StateFractionKeep.fractionKeep_union_ratio μ hstate hGm
      (by norm_num : (1 / 1000000000 : ENNReal) ≠ 0)
      (by norm_num : (1 / 1000000000 : ENNReal) ≠ ⊤) hQ
      (1 / 1000000000000) hQratio L
    have hratio : (1 / 1000000000000 : ENNReal) / (1 / 1000000000) = 1 / 1000 := by
      rw [← ENNReal.coe_one, ← ENNReal.coe_ofNat, ← ENNReal.coe_ofNat, ← ENNReal.coe_ofNat]
      rw [← ENNReal.coe_div (by norm_num : (1000000000000 : ℝ≥0) ≠ 0),
        ← ENNReal.coe_div (by norm_num : (1000000000 : ℝ≥0) ≠ 0),
        ← ENNReal.coe_div (by norm_num : (1000 : ℝ≥0) ≠ 0),
        ← ENNReal.coe_div (by norm_num : (1 / 1000000000 : ℝ≥0) ≠ 0)]
      norm_num
    simpa only [hratio] using h

/-- Two intercepts differing by at most two bin widths lie within two integer bins. -/
theorem floor_bin_close {a b width : ℝ} (hwidth : 0 < width)
    (hclose : |a - b| ≤ 2 * width) :
    ⌊a / width⌋ ∈ Icc (⌊b / width⌋ - 2) (⌊b / width⌋ + 2) := by
  have hfrac : |a / width - b / width| ≤ 2 := by
    rw [← sub_div, abs_div, abs_of_pos hwidth]
    exact (div_le_iff₀ hwidth).mpr hclose
  have hlo := Int.floor_mono (show b / width - 2 ≤ a / width by
    have := (abs_le.mp hfrac).1
    linarith)
  have hhi := Int.floor_mono (show a / width ≤ b / width + 2 by
    have := (abs_le.mp hfrac).2
    linarith)
  have hsub : ⌊b / width - 2⌋ = ⌊b / width⌋ - 2 := by
    simpa using Int.floor_sub_intCast (b / width) (2 : ℤ)
  have hadd : ⌊b / width + 2⌋ = ⌊b / width⌋ + 2 := by
    simpa [add_comm] using Int.floor_intCast_add (2 : ℤ) (b / width)
  exact ⟨by simpa only [hsub] using hlo, by simpa only [hadd] using hhi⟩


end

end Submission.Lib.K4ParentSignalPreparation.BranchGroups
