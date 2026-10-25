import Mathlib
import Submission.Lib.K4OriginalStatePreparation

set_option linter.unusedVariables false

/-!
# Coefficient agreement: from velocity domination to the consensus pair table

At a finite family of fine states with conditional velocity domination, the conditional mass of
the entries (coefficient classes) disagreeing with a given entry is bounded by the palette
weight of the target classes (chart and coefficient class) that occur at the state and disagree.
This turns the pair table of the accepted state consensus into a sum of palette weights against
the original law.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

open scoped Classical in
/-- **Domination of disagreeing entries.** -/
theorem disagree_mass_le {Ω Q ι Tc : Type*} [MeasurableSpace Ω]
    (lam : Measure Ω) [IsFiniteMeasure lam] (σ : Ω → Q) (cls : Ω → ι)
    (tcl : Ω → Tc) (TcF : Finset Tc) (htcl : ∀ᵐ p ∂lam, tcl p ∈ TcF)
    (coarseOf : Tc → ι) (vb : Ω → ℤ) (Vt : Tc → Set ℤ) (πV : Measure ℤ)
    [IsFiniteMeasure πV] (C₁ : ℝ≥0∞)
    (hcls : ∀ᵐ p ∂lam, cls p = coarseOf (tcl p))
    (hvb : ∀ᵐ p ∂lam, vb p ∈ Vt (tcl p))
    (hdom : ∀ (q : Q) (A : Set ℤ), lam {p | σ p = q ∧ vb p ∈ A} ≤ C₁ * lam (σ ⁻¹' {q}) * πV A)
    (R : ι → ι → Prop) (q : Q) (j : ι) :
    lam {p | σ p = q ∧ ¬ R (cls p) j} ≤ C₁ * lam (σ ⁻¹' {q}) *
      ∑ τ ∈ TcF.filter (fun τ => lam {p | σ p = q ∧ tcl p = τ} ≠ 0 ∧ ¬ R (coarseOf τ) j),
        πV (Vt τ) := by
  set S := TcF.filter (fun τ => lam {p | σ p = q ∧ tcl p = τ} ≠ 0 ∧ ¬ R (coarseOf τ) j)
  have hnull : ∀ τ ∈ TcF, τ ∉ S → ¬ R (coarseOf τ) j → lam {p | σ p = q ∧ tcl p = τ} = 0 := by
    intro τ hτF hτ hR
    by_contra h
    exact hτ (Finset.mem_filter.mpr ⟨hτF, h, hR⟩)
  have hnull' : lam (⋃ τ ∈ (TcF.filter (fun τ => τ ∉ S ∧ ¬ R (coarseOf τ) j)),
      {p | σ p = q ∧ tcl p = τ}) = 0 := by
    apply measure_biUnion_null_iff (Finset.countable_toSet _) |>.mpr
    intro τ hτ
    simp only [Finset.coe_filter, mem_ofPred_eq] at hτ
    exact hnull τ hτ.1 hτ.2.1 hτ.2.2
  have hsub : {p | σ p = q ∧ ¬ R (cls p) j} ≤ᵐ[lam]
      ({p | σ p = q ∧ vb p ∈ ⋃ τ ∈ S, Vt τ} ∪
        ⋃ τ ∈ (TcF.filter (fun τ => τ ∉ S ∧ ¬ R (coarseOf τ) j)),
          {p | σ p = q ∧ tcl p = τ}) := by
    filter_upwards [hcls, hvb, htcl] with p hc hv hF hp
    obtain ⟨hq, hR⟩ := hp
    rw [hc] at hR
    by_cases hS : tcl p ∈ S
    · left
      exact ⟨hq, mem_biUnion hS hv⟩
    · right
      exact mem_biUnion (by simp [hS, hR, hF]) ⟨hq, rfl⟩
  calc lam {p | σ p = q ∧ ¬ R (cls p) j}
      ≤ lam ({p | σ p = q ∧ vb p ∈ ⋃ τ ∈ S, Vt τ} ∪
        ⋃ τ ∈ (TcF.filter (fun τ => τ ∉ S ∧ ¬ R (coarseOf τ) j)),
          {p | σ p = q ∧ tcl p = τ}) := measure_mono_ae hsub
    _ ≤ lam {p | σ p = q ∧ vb p ∈ ⋃ τ ∈ S, Vt τ} + 0 := by
        refine (measure_union_le _ _).trans ?_
        rw [hnull']
    _ = lam {p | σ p = q ∧ vb p ∈ ⋃ τ ∈ S, Vt τ} := add_zero _
    _ ≤ C₁ * lam (σ ⁻¹' {q}) * πV (⋃ τ ∈ S, Vt τ) := hdom q _
    _ ≤ C₁ * lam (σ ⁻¹' {q}) * ∑ τ ∈ S, πV (Vt τ) := by
        gcongr
        exact measure_biUnion_finset_le _ _

open scoped Classical in
theorem sum_disagree_eq {Ω Q ι : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (lam : Measure Ω) [IsFiniteMeasure lam] (σ : Ω → Q) (cls : Ω → ι)
    (hσ : Measurable σ) (hcls : Measurable cls) (R : ι → ι → Prop) (q : Q) (j : ι) :
    (∑ i, if R i j then 0 else
      Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam σ cls q i) =
      lam.real {p | σ p = q ∧ ¬ R (cls p) j} := by
  have hset : {p | σ p = q ∧ ¬ R (cls p) j} =
      ⋃ i ∈ Finset.univ.filter (fun i => ¬ R i j), {p | σ p = q ∧ cls p = i} := by
    ext p; simp
  rw [hset, measureReal_biUnion_finset]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> rfl
  · intro i _ i' _ hii'
    exact Set.disjoint_left.mpr fun p h1 h2 => hii' (h1.2.symm.trans h2.2)
  · intro i _
    exact (hσ (measurableSet_singleton q)).inter (hcls (measurableSet_singleton i))

open scoped Classical in
/-- **The consensus pair table is bounded by palette weights of disagreeing occurring
targets.** -/
theorem consensus_pair_le {Ω Q ι Tc : Type*} [MeasurableSpace Ω] [Fintype Q] [Fintype ι]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (lam : Measure Ω) [IsFiniteMeasure lam] (σ : Ω → Q) (cls : Ω → ι)
    (hσ : Measurable σ) (hclsm : Measurable cls)
    (tcl : Ω → Tc) (TcF : Finset Tc) (htcl : ∀ᵐ p ∂lam, tcl p ∈ TcF) (coarseOf : Tc → ι) (vb : Ω → ℤ) (Vt : Tc → Set ℤ) (πV : Measure ℤ)
    [IsFiniteMeasure πV] (C₁ : ℝ≥0∞) (hC₁ : C₁ ≠ ∞)
    (hcls : ∀ᵐ p ∂lam, cls p = coarseOf (tcl p))
    (hvb : ∀ᵐ p ∂lam, vb p ∈ Vt (tcl p))
    (hdom : ∀ (q : Q) (A : Set ℤ), lam {p | σ p = q ∧ vb p ∈ A} ≤ C₁ * lam (σ ⁻¹' {q}) * πV A)
    (R : Q → ι → ι → Prop) :
    (∑ q, (∑ j, Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam σ cls q j *
        ∑ i, if R q i j then 0 else
          Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam σ cls q i) /
          lam.real (σ ⁻¹' {q})) ≤
      C₁.toReal * ∑ q, ∑ j, Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam σ cls q j *
        ∑ τ ∈ TcF.filter (fun τ => lam {p | σ p = q ∧ tcl p = τ} ≠ 0 ∧
          ¬ R q (coarseOf τ) j), (πV (Vt τ)).toReal := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  set W := lam.real (σ ⁻¹' {q})
  have hW0 : 0 ≤ W := measureReal_nonneg
  by_cases hW : W = 0
  · have hz : ∀ j, Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam σ cls q j = 0 := by
      intro j
      apply le_antisymm _ measureReal_nonneg
      calc _ ≤ W := measureReal_mono (fun p hp => hp.1) (measure_ne_top _ _)
        _ = 0 := hW
    simp [hz, hW]
  · have hWpos : 0 < W := lt_of_le_of_ne hW0 (Ne.symm hW)
    rw [div_le_iff₀ hWpos, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [sum_disagree_eq lam σ cls hσ hclsm (R q) q j]
    have h1 := disagree_mass_le lam σ cls tcl TcF htcl coarseOf vb Vt πV C₁ hcls hvb hdom (R q) q j
    have h2 : lam.real {p | σ p = q ∧ ¬ R q (cls p) j} ≤ C₁.toReal * W *
        ∑ τ ∈ TcF.filter (fun τ => lam {p | σ p = q ∧ tcl p = τ} ≠ 0 ∧
          ¬ R q (coarseOf τ) j), (πV (Vt τ)).toReal := by
      have hne : C₁ * lam (σ ⁻¹' {q}) * ∑ τ ∈ TcF.filter (fun τ =>
          lam {p | σ p = q ∧ tcl p = τ} ≠ 0 ∧ ¬ R q (coarseOf τ) j), πV (Vt τ) ≠ ∞ := by
        apply ENNReal.mul_ne_top (ENNReal.mul_ne_top hC₁ (measure_ne_top _ _))
        exact ENNReal.sum_ne_top.mpr fun τ _ => measure_ne_top _ _
      have := ENNReal.toReal_mono hne h1
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sum
        (fun τ _ => measure_ne_top _ _)] at this
      exact this
    have hw0 : 0 ≤ Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam σ cls q j :=
      measureReal_nonneg
    calc Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam σ cls q j *
          lam.real {p | σ p = q ∧ ¬ R q (cls p) j}
        ≤ Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam σ cls q j *
          (C₁.toReal * W * ∑ τ ∈ TcF.filter (fun τ => lam {p | σ p = q ∧ tcl p = τ} ≠ 0 ∧
            ¬ R q (coarseOf τ) j), (πV (Vt τ)).toReal) := mul_le_mul_of_nonneg_left h2 hw0
      _ = _ := by ring

open scoped Classical in
/-- **Integrated disagreement.**  The palette-weighted pair table is bounded by the matching
volumes: every disagreeing occurring target of an incidence is near its source cell and its
transverse coordinate lies in a short matching set. -/
theorem agreement_sum_bound {Ω Q ι Src : Type*} [MeasurableSpace Ω] [Fintype Q] [Fintype ι]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (lam : Measure Ω) [IsFiniteMeasure lam] (σ : Ω → Q) (cls : Ω → ι)
    (hσ : Measurable σ) (hclsm : Measurable cls)
    (R : Q → ι → ι → Prop) (πt : ι → ℝ≥0∞)
    (src : Ω → Src) (SrcF : Finset Src) (cell : Ω → ℤ) (CF : Finset ℤ) (u : Ω → ℝ)
    (Near : Src → ℤ → ι → Prop) (M : Src → ℤ → ι → Set ℝ)
    (hsrc : ∀ᵐ p ∂lam, src p ∈ SrcF ∧ cell p ∈ CF)
    (hmatch : ∀ᵐ p ∂lam, ∀ γ, lam {x | σ x = σ p ∧ cls x = γ} ≠ 0 → ¬ R (σ p) γ (cls p) →
      Near (src p) (cell p) γ ∧ u p ∈ M (src p) (cell p) γ)
    (dens : Src → ℤ → ℝ≥0∞) (ℓ Pi : ℝ≥0∞)
    (hdens : ∀ s ∈ SrcF, ∀ c ∈ CF, ∀ γ, Near s c γ →
      lam {p | src p = s ∧ cell p = c ∧ u p ∈ M s c γ} ≤ dens s c * ℓ)
    (hPi : ∀ s ∈ SrcF, ∀ c ∈ CF, ∑ γ ∈ Finset.univ.filter (fun γ => Near s c γ), πt γ ≤ Pi) :
    ∑ q, ∑ j, lam {p | σ p = q ∧ cls p = j} *
      ∑ γ ∈ Finset.univ.filter (fun γ => lam {p | σ p = q ∧ cls p = γ} ≠ 0 ∧ ¬ R q γ j), πt γ ≤
    ℓ * Pi * ∑ s ∈ SrcF, ∑ c ∈ CF, dens s c := by
  -- regroup by targets
  have hswap : ∑ q, ∑ j, lam {p | σ p = q ∧ cls p = j} *
      ∑ γ ∈ Finset.univ.filter (fun γ => lam {p | σ p = q ∧ cls p = γ} ≠ 0 ∧ ¬ R q γ j), πt γ =
      ∑ γ, πt γ * ∑ q, ∑ j, (if lam {p | σ p = q ∧ cls p = γ} ≠ 0 ∧ ¬ R q γ j then
        lam {p | σ p = q ∧ cls p = j} else 0) := by
    have h1 : ∀ q j, lam {p | σ p = q ∧ cls p = j} *
        ∑ γ ∈ Finset.univ.filter (fun γ => lam {p | σ p = q ∧ cls p = γ} ≠ 0 ∧ ¬ R q γ j), πt γ =
        ∑ γ, (if lam {p | σ p = q ∧ cls p = γ} ≠ 0 ∧ ¬ R q γ j then
          lam {p | σ p = q ∧ cls p = j} * πt γ else 0) := by
      intro q j
      rw [Finset.mul_sum, Finset.sum_filter]
    have h2 : ∀ γ, πt γ * ∑ q, ∑ j, (if lam {p | σ p = q ∧ cls p = γ} ≠ 0 ∧ ¬ R q γ j then
        lam {p | σ p = q ∧ cls p = j} else 0) =
        ∑ q, ∑ j, (if lam {p | σ p = q ∧ cls p = γ} ≠ 0 ∧ ¬ R q γ j then
          lam {p | σ p = q ∧ cls p = j} * πt γ else 0) := by
      intro γ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro q _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> simp [mul_comm]
    simp only [h1, h2]
    rw [Finset.sum_congr rfl (fun q _ => Finset.sum_comm), Finset.sum_comm]
  have hpiece : ∀ γ, ∑ q, ∑ j, (if lam {p | σ p = q ∧ cls p = γ} ≠ 0 ∧ ¬ R q γ j then
      lam {p | σ p = q ∧ cls p = j} else 0) =
      lam {p | lam {x | σ x = σ p ∧ cls x = γ} ≠ 0 ∧ ¬ R (σ p) γ (cls p)} := by
    intro γ
    have hset : {p | lam {x | σ x = σ p ∧ cls x = γ} ≠ 0 ∧ ¬ R (σ p) γ (cls p)} =
        ⋃ qj ∈ (Finset.univ : Finset (Q × ι)).filter
          (fun qj => lam {x | σ x = qj.1 ∧ cls x = γ} ≠ 0 ∧ ¬ R qj.1 γ qj.2),
          {p | σ p = qj.1 ∧ cls p = qj.2} := by
      ext p; simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        exists_prop, Prod.exists]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨σ p, cls p, ⟨h1, h2⟩, rfl, rfl⟩
      · rintro ⟨q, j, ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨h1, h2⟩
    rw [hset, measure_biUnion_finset]
    · rw [← Finset.sum_product', Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro qj _
      rfl
    · intro a _ b _ hab
      exact Set.disjoint_left.mpr fun p h1 h2 => hab (Prod.ext (h1.1.symm.trans h2.1)
        (h1.2.symm.trans h2.2))
    · intro qj _
      exact (hσ (measurableSet_singleton _)).inter (hclsm (measurableSet_singleton _))
  rw [hswap]
  have hbound : ∀ γ, lam {p | lam {x | σ x = σ p ∧ cls x = γ} ≠ 0 ∧ ¬ R (σ p) γ (cls p)} ≤
      ∑ s ∈ SrcF, ∑ c ∈ CF, if Near s c γ then lam {p | src p = s ∧ cell p = c ∧ u p ∈ M s c γ}
        else 0 := by
    intro γ
    have hsub : {p | lam {x | σ x = σ p ∧ cls x = γ} ≠ 0 ∧ ¬ R (σ p) γ (cls p)} ≤ᵐ[lam]
        ⋃ sc ∈ (SrcF ×ˢ CF).filter (fun sc => Near sc.1 sc.2 γ),
          {p | src p = sc.1 ∧ cell p = sc.2 ∧ u p ∈ M sc.1 sc.2 γ} := by
      filter_upwards [hmatch, hsrc] with p hp hs hpq
      obtain ⟨hN, hu⟩ := hp γ hpq.1 hpq.2
      exact mem_biUnion (x := (src p, cell p))
        (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs.1, hs.2⟩, hN⟩) ⟨rfl, rfl, hu⟩
    calc _ ≤ lam (⋃ sc ∈ (SrcF ×ˢ CF).filter (fun sc => Near sc.1 sc.2 γ),
          {p | src p = sc.1 ∧ cell p = sc.2 ∧ u p ∈ M sc.1 sc.2 γ}) := measure_mono_ae hsub
      _ ≤ ∑ sc ∈ (SrcF ×ˢ CF).filter (fun sc => Near sc.1 sc.2 γ),
          lam {p | src p = sc.1 ∧ cell p = sc.2 ∧ u p ∈ M sc.1 sc.2 γ} :=
          measure_biUnion_finset_le _ _
      _ = _ := by rw [Finset.sum_filter, Finset.sum_product]
  calc ∑ γ, πt γ * ∑ q, ∑ j, (if lam {p | σ p = q ∧ cls p = γ} ≠ 0 ∧ ¬ R q γ j then
        lam {p | σ p = q ∧ cls p = j} else 0)
      ≤ ∑ γ, πt γ * ∑ s ∈ SrcF, ∑ c ∈ CF, (if Near s c γ then dens s c * ℓ else 0) := by
        apply Finset.sum_le_sum; intro γ _
        rw [hpiece γ]
        gcongr
        refine (hbound γ).trans ?_
        apply Finset.sum_le_sum; intro s hs
        apply Finset.sum_le_sum; intro c hc
        split_ifs with hN
        · exact hdens s hs c hc γ hN
        · rfl
    _ = ℓ * ∑ s ∈ SrcF, ∑ c ∈ CF, dens s c *
          ∑ γ ∈ Finset.univ.filter (fun γ => Near s c γ), πt γ := by
        simp only [Finset.mul_sum, Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro s _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro c _
        apply Finset.sum_congr rfl; intro γ _
        split_ifs <;> ring
    _ ≤ ℓ * ∑ s ∈ SrcF, ∑ c ∈ CF, dens s c * Pi := by
        gcongr with s hs c hc
        exact hPi s hs c hc
    _ = ℓ * Pi * ∑ s ∈ SrcF, ∑ c ∈ CF, dens s c := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        apply Finset.sum_congr rfl; intro c _
        ring

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
