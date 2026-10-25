import Submission.Obl.k4_general_parent_wide_layer_candidates.Confine.Groups

/-!
# The frame mass of the physical bad set

The physical bad set at an intermediate depth `s` is charged to a list frame through its
original domination. Dyadic times and uncovered incidences carry no original mass; a block
at depth `s` meets the frame's parent region off the dyadic times of the parent level only
when it is nested in the parent, and the nested blocks pack into the parent region. Hence
the frame mass of the bad set is at most `K` times the proportional loss of the blocks.
-/

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_wide_velocity_lists_scalar_preparation (dyadic_Ico_disjoint)

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α]

theorem volume_block (T : ℕ) (j : Fin (2 ^ T)) :
    volume (block T j) = ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ := by
  change volume (Icc (((j : ℕ) : ℝ) / 2 ^ T) ((((j : ℕ) : ℝ) + 1) / 2 ^ T)) = _
  rw [Real.volume_Icc]
  congr 1
  field_simp
  ring

theorem volume_block_Ico (T : ℕ) (j : Fin (2 ^ T)) :
    volume (Ico (((j : ℕ) : ℝ) / 2 ^ T) ((((j : ℕ) : ℝ) + 1) / 2 ^ T)) =
      ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ := by
  rw [Real.volume_Ico]
  congr 1
  field_simp
  ring

/-- Dyadic times carry no original incidence mass. -/
theorem Valid.dyadic_null {p : Parent α} (h : p.Valid) (k T : ℕ) :
    p.μ k {z : α × ℝ | z.2 ∈ dyadicTimes T} = 0 := by
  have hset : {z : α × ℝ | z.2 ∈ dyadicTimes T} = (univ : Set α) ×ˢ dyadicTimes T := by
    ext z
    simp
  apply le_antisymm _ zero_le
  calc p.μ k {z : α × ℝ | z.2 ∈ dyadicTimes T} ≤
        (ENNReal.ofReal (p.K k) • ((p.ν k).prod volume)) {z : α × ℝ | z.2 ∈ dyadicTimes T} :=
        (h.basic k).2.2.2.1 _
    _ = 0 := by
        have : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
        rw [hset, Measure.smul_apply, Measure.prod_prod,
          (countable_dyadicTimes T).measure_zero, mul_zero, smul_zero]

/-- Incidences outside every true block of a prepared depth carry no original mass. -/
theorem AtDepth.uncovered_null {p : Parent α} {k : ℕ} {s R : ℝ} (hat : p.AtDepth k s R) :
    p.μ k (⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i))ᶜ = 0 := by
  have hcov := hat.2.2.2.2.2.1
  have h0 := ae_iff.mp hcov
  have hset : (⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i))ᶜ =
      {ω : α × ℝ | ¬∃ i, ω.1 ∈ p.B k s i ∧ ω.2 ∈ block (p.T k s) (p.j k s i)} := by
    ext ω
    simp only [mem_compl_iff, mem_iUnion, mem_prod, mem_ofPred_eq]
  rw [hset]
  exact h0

/-- The original incidence mass of a true block is at most `K` times its reference. -/
theorem Valid.block_mass_le {p : Parent α} (h : p.Valid) {k : ℕ} {s : ℝ}
    (i : Fin (p.n k s)) (hBA : p.B k s i ⊆ p.A k s i) :
    p.μ k (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) ≤
      ENNReal.ofReal (p.K k) * (ENNReal.ofReal ((2 : ℝ) ^ p.T k s)⁻¹ * p.ν k (p.A k s i)) := by
  have : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  calc p.μ k (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) ≤
        p.μ k (p.A k s i ×ˢ block (p.T k s) (p.j k s i)) :=
        measure_mono (prod_mono hBA le_rfl)
    _ ≤ (ENNReal.ofReal (p.K k) • ((p.ν k).prod volume))
          (p.A k s i ×ˢ block (p.T k s) (p.j k s i)) := (h.basic k).2.2.2.1 _
    _ = _ := by
        rw [Measure.smul_apply, Measure.prod_prod, volume_block, smul_eq_mul, mul_comm
          (p.ν k (p.A k s i))]

omit [MeasurableSpace α] in
/-- True blocks of one depth nested in one region pack into it. -/
theorem nested_packing {β : Type} [MeasurableSpace β] (ν : Measure β) [SFinite ν]
    {n T : ℕ} {A : Fin n → Set β} {j : Fin n → Fin (2 ^ T)}
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i'))
    {P : Set β} {I : Set ℝ} (S : Finset (Fin n))
    (hS : ∀ i ∈ S, A i ⊆ P ∧ block T (j i) ⊆ I) :
    ∑ i ∈ S, ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν (A i) ≤ volume I * ν P := by
  let piece : Fin n → Set (β × ℝ) := fun i =>
    A i ×ˢ Ico (((j i : ℕ) : ℝ) / 2 ^ T) ((((j i : ℕ) : ℝ) + 1) / 2 ^ T)
  have hpiece : ∀ i, ν.prod volume (piece i) = ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν (A i) := by
    intro i
    simp only [piece]
    rw [Measure.prod_prod, volume_block_Ico, mul_comm]
  have hdisjS : (S : Set (Fin n)).PairwiseDisjoint piece := by
    intro i _ i' _ hii'
    simp only [Function.onFun, piece]
    by_cases hj : j i = j i'
    · exact Set.disjoint_prod.mpr (Or.inl (hdisj i i' hii' hj))
    · exact Set.disjoint_prod.mpr (Or.inr (dyadic_Ico_disjoint
        (fun h => hj (Fin.ext h))))
  have hsub : (⋃ i ∈ S, piece i) ⊆ P ×ˢ I := by
    intro x hx
    obtain ⟨i, hiS, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hA', hI⟩ := hS i hiS
    exact ⟨hA' hxi.1, hI (Ico_subset_Icc_self hxi.2)⟩
  calc ∑ i ∈ S, ENNReal.ofReal ((2 : ℝ) ^ T)⁻¹ * ν (A i) =
        ∑ i ∈ S, ν.prod volume (piece i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hpiece]
    _ = ν.prod volume (⋃ i ∈ S, piece i) :=
        (measure_biUnion_finset hdisjS (fun i _ => (hA i).prod measurableSet_Ico)).symm
    _ ≤ ν.prod volume (P ×ˢ I) := measure_mono hsub
    _ = volume I * ν P := by rw [Measure.prod_prod, mul_comm]

namespace ListFrame

variable {p : Parent α} {k : ℕ} {r v m ε : ℝ}

theorem weight_ne_zero (f : p.ListFrame k r v m ε) {R : ℝ} (hat : p.AtDepth k r R)
    (h : p.Valid) : f.weight ≠ 0 := by
  have hN : 0 < p.N k := by linarith [h.scale k]
  have hK : 0 < p.K k := by linarith [h.subpower.1 k]
  have hmass := (hat.2.2.2.2.1 f.parent).1
  have hpos : 0 < (p.N k ^ (-r)) ^ p.d * ((2 : ℝ) ^ (-(p.T k r : ℤ))) ^ 2 *
      p.N k ^ (-p.ℓ * r) / p.K k := by
    have h1 : 0 < p.N k ^ (-r) := Real.rpow_pos_of_pos hN _
    have h2 : 0 < (p.N k ^ (-r)) ^ p.d := Real.rpow_pos_of_pos h1 _
    have h3 : 0 < p.N k ^ (-p.ℓ * r) := Real.rpow_pos_of_pos hN _
    positivity
  have hν : p.ν k (p.A k r f.parent) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hpos) hmass).ne'
  have hq : ENNReal.ofReal f.q ≠ 0 := (ENNReal.ofReal_pos.mpr f.q_pos).ne'
  exact mul_ne_zero hq hν

theorem weight_ne_top (f : p.ListFrame k r v m ε) (h : p.Valid) : f.weight ≠ ⊤ := by
  have : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

/-- Almost every frame event is mapped into the parent's region. -/
theorem law_timeMap_compl_parent (f : p.ListFrame k r v m ε) :
    f.law (f.timeMap ⁻¹' (p.B k r f.parent ×ˢ block (p.T k r) (p.j k r f.parent))ᶜ) = 0 := by
  have ht : ∀ᵐ ω ∂f.law, ω ∈ (univ : Set α) ×ˢ Icc (0 : ℝ) 1 := ae_iff.mpr f.time_support
  have hae : ∀ᵐ ω ∂f.law,
      f.timeMap ω ∈ p.B k r f.parent ×ˢ block (p.T k r) (p.j k r f.parent) := by
    filter_upwards [f.good_ae, ht] with ω hg hω
    exact ⟨f.good_subset hg, f.unit_time_mem ω.2 hω.2⟩
  exact ae_iff.mp hae

/-- **The frame mass of the physical bad set.** If every true block at depth `s` loses at
most an `η` proportion of its incidence mass, the physical bad set has frame mass at most
`K η`. -/
theorem law_physBad_le (f : p.ListFrame k r v m ε) (h : p.Valid) {s R : ℝ}
    (hat_r : p.AtDepth k r R) (hat_s : p.AtDepth k s R)
    (hnest : ∀ i : Fin (p.n k s), ∃ h : Fin (p.n k r), p.A k s i ⊆ p.A k r h ∧
      block (p.T k s) (p.j k s i) ⊆ block (p.T k r) (p.j k r h))
    {E : Fin (p.n k s) → Fin 2 → Set (α × ℝ)} (hEm : ∀ i e, MeasurableSet (E i e))
    {η : ℝ≥0∞}
    (hEloss : ∀ i, p.μ k ((p.B k s i ×ˢ block (p.T k s) (p.j k s i)) \ ⋃ e, E i e) ≤
      p.μ k (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) * η) :
    f.law (f.timeMap ⁻¹' p.physBad k s E) ≤ ENNReal.ofReal (p.K k) * η := by
  classical
  have hνprob : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  have hρμ : p.ρ k ≤ p.μ k := (h.basic k).2.2.2.2.1
  have hw0 := f.weight_ne_zero hat_r h
  have hwt := f.weight_ne_top h
  have hmeas_r := hat_r.2.2.1
  have hdisj_r := hat_r.2.2.2.1
  have hmeas_s := hat_s.2.2.1
  have hdisj_s := hat_s.2.2.2.1
  set par := f.parent with hpar
  set Par : Set (α × ℝ) := p.B k r par ×ˢ block (p.T k r) (p.j k r par) with hParDef
  have hParm : MeasurableSet Par := (hmeas_r par).2.1.prod measurableSet_Icc
  have hbadm : MeasurableSet (p.physBad k s E) :=
    measurableSet_physBad (fun i => (hmeas_s i).2.1) hEm
  set L : Fin (p.n k s) → Set (α × ℝ) := fun i =>
    (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) \ ⋃ e, E i e with hLdef
  set S : Finset (Fin (p.n k s)) := Finset.univ.filter (fun i =>
    p.A k s i ⊆ p.A k r par ∧ block (p.T k s) (p.j k s i) ⊆ block (p.T k r) (p.j k r par))
    with hSdef
  set Z : Set (α × ℝ) := ({z | z.2 ∈ dyadicTimes (p.T k s)} ∪
    (⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i))ᶜ) ∪ {z | z.2 ∈ dyadicTimes (p.T k r)}
    with hZdef
  have hZ : p.μ k Z = 0 := by
    apply le_antisymm _ zero_le
    calc p.μ k Z ≤ p.μ k ({z : α × ℝ | z.2 ∈ dyadicTimes (p.T k s)} ∪
          (⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i))ᶜ) +
          p.μ k {z : α × ℝ | z.2 ∈ dyadicTimes (p.T k r)} := measure_union_le _ _
      _ ≤ (p.μ k {z : α × ℝ | z.2 ∈ dyadicTimes (p.T k s)} +
          p.μ k (⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i))ᶜ) +
          p.μ k {z : α × ℝ | z.2 ∈ dyadicTimes (p.T k r)} := by
          gcongr
          exact measure_union_le _ _
      _ = 0 := by rw [h.dyadic_null, h.dyadic_null, hat_s.uncovered_null]; simp
  -- the bad part of the parent region
  have hsub : p.physBad k s E ∩ Par ⊆ Z ∪ ⋃ i ∈ S, L i := by
    rintro z ⟨hz, hzP⟩
    rcases hz with hz | hz
    · exact Or.inl (Or.inl hz)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      by_cases hDr : z.2 ∈ dyadicTimes (p.T k r)
      · exact Or.inl (Or.inr hDr)
      · obtain ⟨h', hA', hI'⟩ := hnest i
        have hzA : z.1 ∈ p.A k s i := (hmeas_s i).2.2 hi.1.1
        have hh' : h' = par :=
          block_eq_of_mem hdisj_r (hA' hzA) ((hmeas_r par).2.2 hzP.1) (hI' hi.1.2) hzP.2 hDr
        subst hh'
        refine Or.inr (mem_iUnion₂.mpr ⟨i, ?_, hi⟩)
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hA', hI'⟩
  have hphys : p.μ k (p.physBad k s E ∩ Par) ≤ ∑ i ∈ S, p.μ k (L i) := by
    calc p.μ k (p.physBad k s E ∩ Par) ≤ p.μ k (Z ∪ ⋃ i ∈ S, L i) := measure_mono hsub
      _ ≤ p.μ k Z + p.μ k (⋃ i ∈ S, L i) := measure_union_le _ _
      _ = p.μ k (⋃ i ∈ S, L i) := by rw [hZ, zero_add]
      _ ≤ ∑ i ∈ S, p.μ k (L i) := measure_biUnion_finset_le _ _
  have hpack : ∑ i ∈ S, ENNReal.ofReal ((2 : ℝ) ^ p.T k s)⁻¹ * p.ν k (p.A k s i) ≤
      f.weight := by
    have h1 := nested_packing (p.ν k) (fun i => (hmeas_s i).1) hdisj_s
      (P := p.A k r par) (I := block (p.T k r) (p.j k r par)) S (by
        intro i hi
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi)
    have hvol : volume (block (p.T k r) (p.j k r par)) = ENNReal.ofReal f.q := by
      rw [volume_block, f.q_eq]
    rw [hvol] at h1
    exact h1
  have hL : ∑ i ∈ S, p.μ k (L i) ≤ ENNReal.ofReal (p.K k) * f.weight * η := by
    calc ∑ i ∈ S, p.μ k (L i) ≤ ∑ i ∈ S, ENNReal.ofReal (p.K k) *
          (ENNReal.ofReal ((2 : ℝ) ^ p.T k s)⁻¹ * p.ν k (p.A k s i)) * η := by
          apply Finset.sum_le_sum
          intro i _
          refine (hEloss i).trans ?_
          gcongr
          exact h.block_mass_le i (hmeas_s i).2.2
      _ = ENNReal.ofReal (p.K k) * (∑ i ∈ S,
          ENNReal.ofReal ((2 : ℝ) ^ p.T k s)⁻¹ * p.ν k (p.A k s i)) * η := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ ENNReal.ofReal (p.K k) * f.weight * η := by gcongr
  have hsplit : f.timeMap ⁻¹' p.physBad k s E ⊆
      f.timeMap ⁻¹' (p.physBad k s E ∩ Par) ∪ f.timeMap ⁻¹' Parᶜ := by
    intro ω hω
    by_cases hP : f.timeMap ω ∈ Par
    · exact Or.inl ⟨hω, hP⟩
    · exact Or.inr hP
  calc f.law (f.timeMap ⁻¹' p.physBad k s E) ≤
        f.law (f.timeMap ⁻¹' (p.physBad k s E ∩ Par)) + f.law (f.timeMap ⁻¹' Parᶜ) :=
        (measure_mono hsplit).trans (measure_union_le _ _)
    _ = f.law (f.timeMap ⁻¹' (p.physBad k s E ∩ Par)) := by
        rw [f.law_timeMap_compl_parent, add_zero]
    _ ≤ f.weight⁻¹ * p.μ k (p.physBad k s E ∩ Par) :=
        f.law_preimage_le hρμ hw0 hwt (hbadm.inter hParm)
    _ ≤ f.weight⁻¹ * (ENNReal.ofReal (p.K k) * f.weight * η) := by
        gcongr
        exact hphys.trans hL
    _ = ENNReal.ofReal (p.K k) * η := by
        rw [mul_comm (ENNReal.ofReal (p.K k)) f.weight, mul_assoc, ← mul_assoc f.weight⁻¹,
          ENNReal.inv_mul_cancel hw0 hwt, one_mul]

end ListFrame

end Parent

end

end Submission.Obl.k4_general_parent_wide_layer_candidates
