import Submission.Lib.K4ParentSignalPreparation.BranchGroups

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory
open Submission.Lib.K4ParentSignalPreparation.BranchGroups
open scoped ENNReal

noncomputable section

/-- Branch selection preserves the MK-heavy maximal-bin floor, independently
of the total number of intercept bins. All fraction tests use the original law. -/
theorem retain_branch_of_maximal_bin
    {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I] [Countable I]
    [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (hEm : MeasurableSet E)
    (hE : ∀ᵐ x ∂μ, x ∈ E)
    (bin : Ω → ℤ) (hbin : Measurable bin) (state : Ω → I) (hstate : Measurable state)
    (branch : Ω → Bool) (hbranch : Measurable branch) (z : ℤ)
    (hclose : ∀ x ∈ E, ∀ y ∈ E, state x = state y →
      bin x ∈ Icc (bin y - 2) (bin y + 2))
    (hmax : ∀ w : ℤ, μ (binGroup E bin w) ≤ μ (binGroup E bin z)) :
    ∃ (β : Bool) (G : Set Ω), MeasurableSet G ∧
      G ⊆ binGroup E bin z ∩ branch ⁻¹' {β} ∧
      μ (binGroup E bin z) ≤ 4 * μ G ∧
      (∀ Q : Set Ω, MeasurableSet Q →
        (∀ i, μ (state ⁻¹' {i} ∩ Q) ≤
          ENNReal.ofReal ((1 : ℝ)/1000000000000) * μ (state ⁻¹' {i})) →
        ∀ L : Set I, μ (G ∩ state ⁻¹' L ∩ Q) ≤
          ENNReal.ofReal ((1 : ℝ)/1000000) * μ (G ∩ state ⁻¹' L)) := by
  obtain ⟨β, hβ⟩ := exists_heavier_branch μ (binGroup E bin z) branch
  let B := binGroup E bin z ∩ branch ⁻¹' {β}
  have hBm : MeasurableSet B :=
    (hEm.inter (hbin (measurableSet_singleton z))).inter (hbranch (measurableSet_singleton β))
  let f : ENNReal := ENNReal.ofReal ((1:ℝ)/1000000)
  have hf0 : f ≠ 0 := (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
  have hftop : f ≠ ⊤ := ENNReal.ofReal_ne_top
  let G := Submission.Lib.K4StateFractionKeep.fractionKeep μ state B f
  have hGm : MeasurableSet G :=
    Submission.Lib.K4StateFractionKeep.measurableSet_fractionKeep hstate hBm f
  have hGB : G ⊆ B := inter_subset_left
  have hdel : μ (B \ G) ≤ f * (5 * μ (binGroup E bin z)) := by
    exact (Submission.Lib.K4StateFractionKeep.measure_diff_fractionKeep_le μ hstate B f).trans
      (mul_le_mul' le_rfl (saturation_le_five μ E bin state hE z B inter_subset_left hclose hmax))
  have hcover : μ B ≤ μ G + μ (B \ G) := by
    apply (measure_mono (μ := μ) (s := B) (t := G ∪ (B \ G)) ?_).trans (measure_union_le _ _)
    intro x hx
    by_cases hg : x ∈ G
    · exact Or.inl hg
    · exact Or.inr ⟨hx, hg⟩
  have hdelReal : μ.real (B \ G) ≤ (5 / 1000000 : ℝ) * μ.real (binGroup E bin z) := by
    have hr := ENNReal.toReal_mono (by finiteness) hdel
    dsimp only [f] at hr
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (by norm_num : 0 ≤ (1:ℝ)/1000000), ENNReal.toReal_ofNat] at hr
    convert hr using 1 <;> simp only [measureReal_def] <;> ring
  have hcoverReal : μ.real B ≤ μ.real G + μ.real (B \ G) := by
    have hr := ENNReal.toReal_mono (by finiteness) hcover
    simpa only [measureReal_def, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
      using hr
  have hβReal : μ.real (binGroup E bin z) ≤ 2 * μ.real B := by
    have hr := ENNReal.toReal_mono (by finiteness) hβ
    simpa only [B, measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hr
  have hmass : μ (binGroup E bin z) ≤ 4 * μ G := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) (by finiteness)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    change μ.real (binGroup E bin z) ≤ 4 * μ.real G
    nlinarith [show 0 ≤ μ.real G from measureReal_nonneg]
  refine ⟨β, G, hGm, hGB, hmass, ?_⟩
  intro Q hQ hQstrip L
  have hr := Submission.Lib.K4StateFractionKeep.fractionKeep_union_ratio μ hstate hBm
    hf0 hftop hQ (ENNReal.ofReal ((1:ℝ)/1000000000000)) hQstrip L
  have hratio : ENNReal.ofReal ((1:ℝ)/1000000000000) / f =
      ENNReal.ofReal ((1:ℝ)/1000000) := by
    dsimp only [f]
    rw [← ENNReal.ofReal_div_of_pos (by norm_num)]
    congr 1
    norm_num
  simpa only [hratio] using hr

/-- An MK-heavy original bin may be replaced by a maximal bin and then
one retained branch, paying four and keeping all original-state ratio tests. -/
theorem exists_retained_heavy_branch
    {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I] [Countable I]
    [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : Set Ω) (hEm : MeasurableSet E)
    (hE : ∀ᵐ x ∂μ, x ∈ E) (hEne : E.Nonempty)
    (bin : Ω → ℤ) (hbin : Measurable bin) (state : Ω → I) (hstate : Measurable state)
    (branch : Ω → Bool) (hbranch : Measurable branch)
    (catalogue : Finset ℤ) (hcat : ∀ x ∈ E, bin x ∈ catalogue)
    (hclose : ∀ x ∈ E, ∀ y ∈ E, state x = state y →
      bin x ∈ Icc (bin y - 2) (bin y + 2))
    {M : ℝ} (hheavy : ∃ g : ℤ, M ≤ μ.real (bin ⁻¹' {g})) :
    ∃ (g : ℤ) (β : Bool) (G : Set Ω), MeasurableSet G ∧
      G ⊆ binGroup E bin g ∩ branch ⁻¹' {β} ∧ M/4 ≤ μ.real G ∧
      (∀ Q : Set Ω, MeasurableSet Q →
        (∀ i, μ (state ⁻¹' {i} ∩ Q) ≤
          ENNReal.ofReal ((1:ℝ)/1000000000000) * μ (state ⁻¹' {i})) →
        ∀ L : Set I, μ (G ∩ state ⁻¹' L ∩ Q) ≤
          ENNReal.ofReal ((1:ℝ)/1000000) * μ (G ∩ state ⁻¹' L)) := by
  have hcatne : catalogue.Nonempty := by
    obtain ⟨x, hx⟩ := hEne
    exact ⟨bin x, hcat x hx⟩
  obtain ⟨g, hg, hmax, htotal⟩ := exists_maximal_bin μ E bin hE catalogue hcatne hcat
  obtain ⟨β, G, hGm, hGsub, hmass, hratios⟩ :=
    retain_branch_of_maximal_bin μ E hEm hE bin hbin state hstate branch hbranch g hclose hmax
  have hnullE : μ Eᶜ = 0 := by
    have he := ae_iff.mp hE
    have hset : Eᶜ = {x | x ∉ E} := by ext x; rfl
    rwa [hset]
  obtain ⟨g₀, hg₀⟩ := hheavy
  have hbinmass : μ (binGroup E bin g₀) = μ (bin ⁻¹' {g₀}) := by
    unfold binGroup
    rw [inter_comm, measure_inter_conull hnullE]
  have hmaxReal := ENNReal.toReal_mono (measure_ne_top μ _) (hmax g₀)
  have hmassReal := ENNReal.toReal_mono (by finiteness) hmass
  rw [hbinmass] at hmaxReal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hmassReal
  refine ⟨g, β, G, hGm, hGsub, ?_, hratios⟩
  change M/4 ≤ (μ G).toReal
  change M ≤ (μ (bin ⁻¹' {g₀})).toReal at hg₀
  linarith

end

end Submission.Obl.k4_physical_parent_potential_candidates
