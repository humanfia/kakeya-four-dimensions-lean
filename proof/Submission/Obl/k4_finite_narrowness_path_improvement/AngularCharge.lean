import Mathlib

/-!
# Known labels with concentrated velocities are charged by the angular cap

The mechanism of paper Lemma a01:largest-axis (fullness of the largest spatial scale), of the
alignment of strip rows in Prop. 4.11, and of the vacuity of the interface X for `l > 0` and
`S > 1`: labels known through an observation `obs` by lists of size `κ`, whose incidences have
their velocity cell in a set of at most `M` cells, carry on the good set (joint density of
`(obs, cell)` at most `α`, density of `obs` at least `β`) at most `κ M (α / β)` times the total
mass (`known_label_charge`). `share_pruning` and `label_conditional_cap`: after removing the
incidences where a listed label's conditional share is below `θ` (total cost `κ θ μ(univ)`),
the label's good velocity cells carry at most `(α/β)/θ` of its mass (conditional velocity
domination, used throughout paper Sections 8 and 9).

The lists are arbitrary functions of the observation (no measurability); the proof disintegrates
the measure along `obs` (`Measure.condKernel`): the conditional laws live on the fibers
(`disint_fiber`), the conditional cell probabilities are `G / g` (`disint_cell_density`), and on
each fiber only the listed labels can carry mass.
-/

namespace Submission.Obl.k4_finite_narrowness_path_improvement

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {P O : Type*} [MeasurableSpace P] [StandardBorelSpace P] [Nonempty P] [MeasurableSpace O]

/-- Disintegration of `μ` along `obs`: `μ S = ∫⁻ o, K o S ∂(μ.map obs)`. -/
theorem disint_apply (μ : Measure P) [IsFiniteMeasure μ] (obs : P → O) (hobs : Measurable obs)
    {S : Set P} (hS : MeasurableSet S) :
    μ S = ∫⁻ o, (μ.map (fun p => (obs p, p))).condKernel o S ∂(μ.map obs) := by
  set ρ := μ.map (fun p => (obs p, p)) with hρ
  have hm : Measurable (fun p => (obs p, p)) := hobs.prodMk measurable_id
  have hfst : ρ.fst = μ.map obs := by
    rw [hρ, Measure.fst, Measure.map_map measurable_fst hm]
    rfl
  have h1 : μ S = ρ (Set.univ ×ˢ S) := by
    rw [hρ, Measure.map_apply hm (MeasurableSet.univ.prod hS)]
    congr 1
    ext p
    simp
  rw [h1, ← Measure.disintegrate ρ ρ.condKernel, Measure.compProd_apply
    (MeasurableSet.univ.prod hS), hfst]
  congr 1
  ext o
  congr 1
  ext p
  simp

/-- The conditional kernel lives on the fibers of `obs`. -/
theorem disint_fiber [MeasurableEq O] (μ : Measure P) [IsFiniteMeasure μ] (obs : P → O) (hobs : Measurable obs) :
    ∀ᵐ o ∂(μ.map obs), (μ.map (fun p => (obs p, p))).condKernel o {p | obs p ≠ o} = 0 := by
  set ρ := μ.map (fun p => (obs p, p)) with hρ
  have hm : Measurable (fun p => (obs p, p)) := hobs.prodMk measurable_id
  have hfst : ρ.fst = μ.map obs := by
    rw [hρ, Measure.fst, Measure.map_map measurable_fst hm]
    rfl
  have hD : MeasurableSet {q : O × P | obs q.2 ≠ q.1} := by
    have : {q : O × P | obs q.2 ≠ q.1} = (fun q : O × P => (obs q.2, q.1)) ⁻¹'
        {q : O × O | q.1 = q.2}ᶜ := by
      ext q
      simp
    rw [this]
    exact ((hobs.comp measurable_snd).prodMk measurable_fst) measurableSet_diagonal.compl
  have h0 : ρ {q : O × P | obs q.2 ≠ q.1} = 0 := by
    rw [hρ, Measure.map_apply hm hD]
    simp
  rw [← Measure.disintegrate ρ ρ.condKernel, Measure.compProd_apply hD, hfst] at h0
  rw [lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hD)] at h0
  filter_upwards [h0] with o ho
  simpa using ho

variable {Γ : Type*} [MeasurableSpace Γ] [Countable Γ] [MeasurableSingletonClass Γ]

theorem setLIntegral_prod_singleton (lam : Measure O) [SigmaFinite lam] (G : O × Γ → ℝ≥0∞)
    (hG : Measurable G) (A : Set O) (c : Γ) :
    ∫⁻ q in A ×ˢ {c}, G q ∂(lam.prod Measure.count) = ∫⁻ o in A, G (o, c) ∂lam := by
  rw [← Measure.prod_restrict, lintegral_prod _ hG.aemeasurable]
  congr 1
  ext o
  rw [Measure.restrict_singleton, Measure.count_singleton, one_smul, lintegral_dirac]

theorem disint_cell_density [MeasurableEq O] (μ : Measure P) [IsFiniteMeasure μ] (obs : P → O)
    (hobs : Measurable obs) (cell : P → Γ) (hcell : Measurable cell) (lam : Measure O)
    [SigmaFinite lam] (g : O → ℝ≥0∞) (hg : Measurable g) (hmap : μ.map obs = lam.withDensity g)
    (G : O × Γ → ℝ≥0∞) (hG : Measurable G)
    (hmapG : μ.map (fun p => (obs p, cell p)) = (lam.prod Measure.count).withDensity G) :
    ∀ᵐ o ∂lam, ∀ c, (μ.map (fun p => (obs p, p))).condKernel o (cell ⁻¹' {c}) * g o = G (o, c) := by
  set K := (μ.map (fun p => (obs p, p))).condKernel with hK
  rw [ae_all_iff]
  intro c
  have hcm : MeasurableSet (cell ⁻¹' {c}) := hcell (measurableSet_singleton c)
  have hKm : Measurable fun o => K o (cell ⁻¹' {c}) := Kernel.measurable_coe K hcm
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (hKm.mul hg)
    (hG.comp (measurable_id.prodMk measurable_const)) ?_
  intro A hA _
  have hfib := disint_fiber μ obs hobs
  -- left side as a mass of μ
  have hL : ∫⁻ o in A, K o (cell ⁻¹' {c}) * g o ∂lam = μ (obs ⁻¹' A ∩ cell ⁻¹' {c}) := by
    have h1 : ∫⁻ o in A, K o (cell ⁻¹' {c}) * g o ∂lam =
        ∫⁻ o in A, K o (cell ⁻¹' {c}) ∂(μ.map obs) := by
      rw [hmap, setLIntegral_withDensity_eq_setLIntegral_mul _ hg hKm hA]
      congr 1
      ext o
      simp [mul_comm]
    rw [h1, disint_apply μ obs hobs ((hobs hA).inter hcm), ← lintegral_indicator hA]
    apply lintegral_congr_ae
    filter_upwards [hfib] with o ho
    by_cases hoA : o ∈ A
    · rw [Set.indicator_of_mem hoA]
      refine le_antisymm ?_ (measure_mono Set.inter_subset_right)
      calc K o (cell ⁻¹' {c}) ≤ K o (obs ⁻¹' A ∩ cell ⁻¹' {c}) + K o {p | obs p ≠ o} := by
            apply (measure_mono _).trans (measure_union_le _ _)
            intro p hp
            by_cases hpo : obs p = o
            · exact Or.inl ⟨by simp [hpo, hoA], hp⟩
            · exact Or.inr hpo
        _ = K o (obs ⁻¹' A ∩ cell ⁻¹' {c}) := by rw [ho, add_zero]
    · rw [Set.indicator_of_notMem hoA]
      refine (le_antisymm ?_ bot_le).symm
      calc K o (obs ⁻¹' A ∩ cell ⁻¹' {c}) ≤ K o {p | obs p ≠ o} := by
            apply measure_mono
            intro p hp hpo
            exact hoA (hpo ▸ hp.1)
        _ = 0 := ho
  have hR : ∫⁻ o in A, G (o, c) ∂lam = μ (obs ⁻¹' A ∩ cell ⁻¹' {c}) := by
    rw [← setLIntegral_prod_singleton lam G hG A c, ← withDensity_apply _
      (hA.prod (measurableSet_singleton c)), ← hmapG,
      Measure.map_apply (hobs.prodMk hcell) (hA.prod (measurableSet_singleton c))]
    rfl
  rw [hL, hR]

/-- **Known labels with concentrated velocities are charged by the angular cap.**
Labels `F b` are known through the observation `obs` (lists of size `κ`), and the velocity cell
`cell p` of every incidence of `F b` lies in a set `V b` of at most `M` cells. On the good
incidences, where the joint density `G` of `(obs, cell)` is at most `α` and the density `g` of
`obs` is at least `β`, the total label mass is at most `κ M (α / β) μ(univ)`. -/
theorem known_label_charge [MeasurableEq O] (μ : Measure P) [IsFiniteMeasure μ] (obs : P → O)
    (hobs : Measurable obs) (cell : P → Γ) (hcell : Measurable cell) (lam : Measure O)
    [SigmaFinite lam] (g : O → ℝ≥0∞) (hg : Measurable g) (hmap : μ.map obs = lam.withDensity g)
    (G : O × Γ → ℝ≥0∞) (hG : Measurable G)
    (hmapG : μ.map (fun p => (obs p, cell p)) = (lam.prod Measure.count).withDensity G)
    {ι : Type*} [Fintype ι] (F : ι → Set P) (hF : ∀ b, MeasurableSet (F b))
    (lst : O → Finset ι) (hlst : ∀ b, ∀ p ∈ F b, b ∈ lst (obs p)) (κ : ℕ)
    (hκ : ∀ o, (lst o).card ≤ κ) (V : ι → Finset Γ) (hV : ∀ b, ∀ p ∈ F b, cell p ∈ V b)
    (M : ℕ) (hM : ∀ b, (V b).card ≤ M) (α β : ℝ≥0∞) (hβ : β ≠ 0) :
    ∑ b, μ (F b ∩ {p | G (obs p, cell p) ≤ α ∧ β ≤ g (obs p)}) ≤
      ((κ : ℝ≥0∞) * M * (α / β)) * μ Set.univ := by
  classical
  set K := (μ.map (fun p => (obs p, p))).condKernel with hK
  set Good := {p | G (obs p, cell p) ≤ α ∧ β ≤ g (obs p)} with hGood
  have hGm : MeasurableSet Good := by
    refine (measurableSet_le (hG.comp (hobs.prodMk hcell)) measurable_const).inter ?_
    exact measurableSet_le measurable_const (hg.comp hobs)
  -- step 1: disintegrate every label
  have h1 : ∑ b, μ (F b ∩ Good) = ∫⁻ o, ∑ b, K o (F b ∩ Good) ∂(μ.map obs) := by
    rw [lintegral_finsetSum _ (fun b _ => Kernel.measurable_coe K ((hF b).inter hGm))]
    exact Finset.sum_congr rfl fun b _ => disint_apply μ obs hobs ((hF b).inter hGm)
  -- a.e. facts on the observation law
  have hac : μ.map obs ≪ lam := by
    rw [hmap]
    exact withDensity_absolutelyContinuous lam g
  have hfib := disint_fiber μ obs hobs
  have hdens := hac.ae_le (disint_cell_density μ obs hobs cell hcell lam g hg hmap G hG hmapG)
  have hfin : ∀ᵐ o ∂(μ.map obs), g o ≠ ∞ := by
    have hint : ∫⁻ o, g o ∂lam ≠ ∞ := by
      have : ∫⁻ o, g o ∂lam = (lam.withDensity g) Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      rw [this, ← hmap, Measure.map_apply hobs MeasurableSet.univ]
      exact measure_ne_top _ _
    exact hac.ae_le (ae_lt_top hg hint |>.mono fun o h => h.ne)
  -- step 2: the pointwise bound
  have h2 : ∀ᵐ o ∂(μ.map obs), ∑ b, K o (F b ∩ Good) ≤ (κ : ℝ≥0∞) * M * (α / β) := by
    filter_upwards [hfib, hdens, hfin] with o ho hd hgo
    have hcell_le : ∀ c, G (o, c) ≤ α → β ≤ g o → K o (cell ⁻¹' {c}) ≤ α / β := by
      intro c hGc hβg
      have hg0 : g o ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.mpr hβ) hβg).ne'
      have : K o (cell ⁻¹' {c}) = G (o, c) / g o := by
        rw [← hd c, ENNReal.mul_div_cancel_right hg0 hgo]
      rw [this]
      exact ENNReal.div_le_div hGc hβg
    have hb : ∀ b, K o (F b ∩ Good) ≤ if b ∈ lst o then (M : ℝ≥0∞) * (α / β) else 0 := by
      intro b
      have hsplit : K o (F b ∩ Good) ≤ K o (F b ∩ Good ∩ {p | obs p = o}) := by
        calc K o (F b ∩ Good) ≤ K o (F b ∩ Good ∩ {p | obs p = o}) + K o {p | obs p ≠ o} := by
              apply (measure_mono _).trans (measure_union_le _ _)
              intro p hp
              by_cases hpo : obs p = o
              · exact Or.inl ⟨hp, hpo⟩
              · exact Or.inr hpo
          _ = _ := by rw [ho, add_zero]
      split_ifs with hbo
      · refine hsplit.trans ?_
        have hsub : F b ∩ Good ∩ {p | obs p = o} ⊆
            ⋃ c ∈ (V b).filter (fun c => G (o, c) ≤ α ∧ β ≤ g o), cell ⁻¹' {c} := by
          intro p ⟨⟨hpF, hpG⟩, hpo⟩
          simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_filter,
            exists_prop]
          refine ⟨cell p, ⟨hV b p hpF, ?_⟩, rfl⟩
          have hpo' : obs p = o := hpo
          have hpG' : G (obs p, cell p) ≤ α ∧ β ≤ g (obs p) := hpG
          rw [hpo'] at hpG'
          exact hpG'
        calc K o (F b ∩ Good ∩ {p | obs p = o})
            ≤ ∑ c ∈ (V b).filter (fun c => G (o, c) ≤ α ∧ β ≤ g o), K o (cell ⁻¹' {c}) :=
              (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
          _ ≤ ∑ c ∈ (V b).filter (fun c => G (o, c) ≤ α ∧ β ≤ g o), α / β := by
              apply Finset.sum_le_sum
              intro c hc
              rw [Finset.mem_filter] at hc
              exact hcell_le c hc.2.1 hc.2.2
          _ ≤ ∑ c ∈ V b, α / β := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
          _ = (V b).card * (α / β) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ M * (α / β) := by gcongr; exact_mod_cast hM b
      · refine hsplit.trans (le_of_eq ?_)
        have hempty : F b ∩ Good ∩ {p | obs p = o} = ∅ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
          intro hpF hpo
          have := hlst b p hpF.1
          have hpo' : obs p = o := hpo
          rw [hpo'] at this
          exact hbo this
        rw [hempty, measure_empty]
    calc ∑ b, K o (F b ∩ Good) ≤ ∑ b, (if b ∈ lst o then (M : ℝ≥0∞) * (α / β) else 0) :=
          Finset.sum_le_sum fun b _ => hb b
      _ = ∑ b ∈ lst o, (M : ℝ≥0∞) * (α / β) := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = (lst o).card * ((M : ℝ≥0∞) * (α / β)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ κ * ((M : ℝ≥0∞) * (α / β)) := by gcongr; exact_mod_cast hκ o
      _ = (κ : ℝ≥0∞) * M * (α / β) := by ring
  -- step 3: integrate
  rw [h1]
  calc ∫⁻ o, ∑ b, K o (F b ∩ Good) ∂(μ.map obs)
      ≤ ∫⁻ _o, (κ : ℝ≥0∞) * M * (α / β) ∂(μ.map obs) := lintegral_mono_ae h2
    _ = (κ : ℝ≥0∞) * M * (α / β) * μ Set.univ := by
        rw [lintegral_const, Measure.map_apply hobs MeasurableSet.univ, Set.preimage_univ]


/-- The share of a label `F` in the conditional law at the observation of `p`. -/
noncomputable def labelShare (μ : Measure P) [IsFiniteMeasure μ] (obs : P → O) (F : Set P)
    (p : P) : ℝ≥0∞ :=
  (μ.map (fun p => (obs p, p))).condKernel (obs p) F

theorem measurable_labelShare (μ : Measure P) [IsFiniteMeasure μ] {obs : P → O}
    (hobs : Measurable obs) {F : Set P} (hF : MeasurableSet F) :
    Measurable (labelShare μ obs F) :=
  (Kernel.measurable_coe _ hF).comp hobs

/-- **Share pruning.** Removing the incidences where a listed label has conditional share below
`θ` costs at most `κ θ μ(univ)` in total. -/
theorem share_pruning [MeasurableEq O] (μ : Measure P) [IsFiniteMeasure μ] (obs : P → O) (hobs : Measurable obs)
    {ι : Type*} [Fintype ι] (F : ι → Set P) (hF : ∀ b, MeasurableSet (F b))
    (lst : O → Finset ι) (hlst : ∀ b, ∀ p ∈ F b, b ∈ lst (obs p)) (κ : ℕ)
    (hκ : ∀ o, (lst o).card ≤ κ) (θ : ℝ≥0∞) :
    ∑ b, μ (F b ∩ {p | labelShare μ obs (F b) p < θ}) ≤ κ * θ * μ Set.univ := by
  classical
  set K := (μ.map (fun p => (obs p, p))).condKernel with hK
  have hS : ∀ b, MeasurableSet {p | labelShare μ obs (F b) p < θ} := fun b =>
    measurableSet_lt (measurable_labelShare μ hobs (hF b)) measurable_const
  have hfib := disint_fiber μ obs hobs
  have h1 : ∑ b, μ (F b ∩ {p | labelShare μ obs (F b) p < θ}) =
      ∫⁻ o, ∑ b, K o (F b ∩ {p | labelShare μ obs (F b) p < θ}) ∂(μ.map obs) := by
    rw [lintegral_finsetSum _ (fun b _ => Kernel.measurable_coe K ((hF b).inter (hS b)))]
    exact Finset.sum_congr rfl fun b _ => disint_apply μ obs hobs ((hF b).inter (hS b))
  have h2 : ∀ᵐ o ∂(μ.map obs), ∑ b, K o (F b ∩ {p | labelShare μ obs (F b) p < θ}) ≤ κ * θ := by
    filter_upwards [hfib] with o ho
    have hb : ∀ b, K o (F b ∩ {p | labelShare μ obs (F b) p < θ}) ≤
        if b ∈ lst o then θ else 0 := by
      intro b
      have hsplit : K o (F b ∩ {p | labelShare μ obs (F b) p < θ}) ≤
          K o (F b ∩ {p | labelShare μ obs (F b) p < θ} ∩ {p | obs p = o}) := by
        calc _ ≤ K o (F b ∩ {p | labelShare μ obs (F b) p < θ} ∩ {p | obs p = o}) +
              K o {p | obs p ≠ o} := by
              apply (measure_mono _).trans (measure_union_le _ _)
              intro p hp
              by_cases hpo : obs p = o
              · exact Or.inl ⟨hp, hpo⟩
              · exact Or.inr hpo
          _ = _ := by rw [ho, add_zero]
      split_ifs with hbo
      · refine hsplit.trans ?_
        by_cases hne : (F b ∩ {p | labelShare μ obs (F b) p < θ} ∩ {p | obs p = o}).Nonempty
        · obtain ⟨p, ⟨⟨_, hp⟩, hpo⟩⟩ := hne
          have hpo' : obs p = o := hpo
          have hp' : labelShare μ obs (F b) p < θ := hp
          unfold labelShare at hp'
          rw [hpo'] at hp'
          exact (measure_mono (fun q hq => hq.1.1)).trans hp'.le
        · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
          exact bot_le
      · refine hsplit.trans (le_of_eq ?_)
        have hempty : F b ∩ {p | labelShare μ obs (F b) p < θ} ∩ {p | obs p = o} = ∅ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
          intro hpF hpo
          have := hlst b p hpF.1
          have hpo' : obs p = o := hpo
          rw [hpo'] at this
          exact hbo this
        rw [hempty, measure_empty]
    calc ∑ b, K o (F b ∩ {p | labelShare μ obs (F b) p < θ})
        ≤ ∑ b, (if b ∈ lst o then θ else 0) := Finset.sum_le_sum fun b _ => hb b
      _ = ∑ b ∈ lst o, θ := by rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = (lst o).card * θ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ κ * θ := by gcongr; exact_mod_cast hκ o
  rw [h1]
  calc ∫⁻ o, ∑ b, K o (F b ∩ {p | labelShare μ obs (F b) p < θ}) ∂(μ.map obs)
      ≤ ∫⁻ _o, (κ : ℝ≥0∞) * θ ∂(μ.map obs) := lintegral_mono_ae h2
    _ = κ * θ * μ Set.univ := by
        rw [lintegral_const, Measure.map_apply hobs MeasurableSet.univ, Set.preimage_univ]

/-- **Label-conditional angular cap.** On the incidences of a label `F` whose conditional share
at their observation is at least `θ`, the good part of a velocity cell carries at most
`(α / β) / θ` times the label mass: conditional velocity domination by the angular cap. -/
theorem label_conditional_cap [MeasurableEq O] (μ : Measure P) [IsFiniteMeasure μ] (obs : P → O)
    (hobs : Measurable obs) (cell : P → Γ) (hcell : Measurable cell) (lam : Measure O)
    [SigmaFinite lam] (g : O → ℝ≥0∞) (hg : Measurable g) (hmap : μ.map obs = lam.withDensity g)
    (G : O × Γ → ℝ≥0∞) (hG : Measurable G)
    (hmapG : μ.map (fun p => (obs p, cell p)) = (lam.prod Measure.count).withDensity G)
    {F : Set P} (hF : MeasurableSet F) (θ α β : ℝ≥0∞) (hθ : θ ≠ 0) (hβ : β ≠ 0) (c : Γ) :
    μ (F ∩ {p | θ ≤ labelShare μ obs F p} ∩
        {p | G (obs p, cell p) ≤ α ∧ β ≤ g (obs p)} ∩ {p | cell p = c}) ≤
      (α / β) / θ * μ F := by
  set K := (μ.map (fun p => (obs p, p))).condKernel with hK
  have hPr : MeasurableSet {p | θ ≤ labelShare μ obs F p} :=
    measurableSet_le measurable_const (measurable_labelShare μ hobs hF)
  have hGm : MeasurableSet {p | G (obs p, cell p) ≤ α ∧ β ≤ g (obs p)} :=
    (measurableSet_le (hG.comp (hobs.prodMk hcell)) measurable_const).inter
      (measurableSet_le measurable_const (hg.comp hobs))
  have hCm : MeasurableSet {p | cell p = c} := hcell (measurableSet_singleton c)
  have hSm := ((hF.inter hPr).inter hGm).inter hCm
  have hac : μ.map obs ≪ lam := by
    rw [hmap]
    exact withDensity_absolutelyContinuous lam g
  have hfib := disint_fiber μ obs hobs
  have hdens := hac.ae_le (disint_cell_density μ obs hobs cell hcell lam g hg hmap G hG hmapG)
  have hfin : ∀ᵐ o ∂(μ.map obs), g o ≠ ∞ := by
    have hint : ∫⁻ o, g o ∂lam ≠ ∞ := by
      have : ∫⁻ o, g o ∂lam = (lam.withDensity g) Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      rw [this, ← hmap, Measure.map_apply hobs MeasurableSet.univ]
      exact measure_ne_top _ _
    exact hac.ae_le (ae_lt_top hg hint |>.mono fun o h => h.ne)
  have hpt : ∀ᵐ o ∂(μ.map obs), K o (F ∩ {p | θ ≤ labelShare μ obs F p} ∩
      {p | G (obs p, cell p) ≤ α ∧ β ≤ g (obs p)} ∩ {p | cell p = c}) ≤
      (α / β) / θ * K o F := by
    filter_upwards [hfib, hdens, hfin] with o ho hd hgo
    set S := F ∩ {p | θ ≤ labelShare μ obs F p} ∩
      {p | G (obs p, cell p) ≤ α ∧ β ≤ g (obs p)} ∩ {p | cell p = c}
    have hsplit : K o S ≤ K o (S ∩ {p | obs p = o}) := by
      calc K o S ≤ K o (S ∩ {p | obs p = o}) + K o {p | obs p ≠ o} := by
            apply (measure_mono _).trans (measure_union_le _ _)
            intro p hp
            by_cases hpo : obs p = o
            · exact Or.inl ⟨hp, hpo⟩
            · exact Or.inr hpo
        _ = _ := by rw [ho, add_zero]
    refine hsplit.trans ?_
    by_cases hne : (S ∩ {p | obs p = o}).Nonempty
    · obtain ⟨p, ⟨⟨⟨⟨_, hpPr⟩, hpG⟩, hpc⟩, hpo⟩⟩ := hne
      have hpo' : obs p = o := hpo
      have hshare : θ ≤ K o F := by
        have : θ ≤ labelShare μ obs F p := hpPr
        unfold labelShare at this
        rwa [hpo'] at this
      have hgood : G (o, c) ≤ α ∧ β ≤ g o := by
        have h' : G (obs p, cell p) ≤ α ∧ β ≤ g (obs p) := hpG
        have hc' : cell p = c := hpc
        rw [hpo', hc'] at h'
        exact h'
      have hg0 : g o ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.mpr hβ) hgood.2).ne'
      have hcellK : K o (cell ⁻¹' {c}) ≤ α / β := by
        have : K o (cell ⁻¹' {c}) = G (o, c) / g o := by
          rw [← hd c, ENNReal.mul_div_cancel_right hg0 hgo]
        rw [this]
        exact ENNReal.div_le_div hgood.1 hgood.2
      have hθtop : θ ≠ ∞ := by
        intro h
        rw [h] at hshare
        exact absurd (top_le_iff.mp hshare) (measure_ne_top (K o) F)
      calc K o (S ∩ {p | obs p = o}) ≤ K o (cell ⁻¹' {c}) :=
            measure_mono fun q hq => hq.1.2
        _ ≤ α / β := hcellK
        _ ≤ (α / β) / θ * K o F := by
            calc α / β = (α / β) / θ * θ := (ENNReal.div_mul_cancel hθ hθtop).symm
              _ ≤ (α / β) / θ * K o F := by gcongr
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, measure_empty]
      exact bot_le
  rw [disint_apply μ obs hobs hSm, disint_apply μ obs hobs hF]
  calc ∫⁻ o, K o (F ∩ {p | θ ≤ labelShare μ obs F p} ∩
        {p | G (obs p, cell p) ≤ α ∧ β ≤ g (obs p)} ∩ {p | cell p = c}) ∂(μ.map obs)
      ≤ ∫⁻ o, (α / β) / θ * K o F ∂(μ.map obs) := lintegral_mono_ae hpt
    _ = (α / β) / θ * ∫⁻ o, K o F ∂(μ.map obs) :=
        lintegral_const_mul _ (Kernel.measurable_coe K hF)

end Submission.Obl.k4_finite_narrowness_path_improvement
