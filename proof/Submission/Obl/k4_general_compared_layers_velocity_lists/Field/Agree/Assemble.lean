-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Assemble; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Disagreement
import Submission.Obl.k4_general_compared_layers_velocity_lists.OriginalBudgets

/-!
# Coefficient consensus at one index (paper Prop. 8.4)

`consensus_at_index`: at one index, with the numeric inequalities of that index and a native
fine-state pruning of every original block, a compared sample yields a `ConsensusLaw`:

1. restrict the sample law to the color-0 events of each parent block and prune it at native
   states (loss `ϑ` times the block reference, domination constant `324 K / ϑ`);
2. sum over blocks: the pruned law has conditional palette domination at the combined states;
3. its conditional pair law disagrees on mass at most `1 / (16 H)` (`disagreement_le`), so the
   consensus kernel gives a center per combined state and a consensus set losing at most
   `2 / (16 H)`, keeping half of every occupied state;
4. a block of mass at least `1 / (4 H)` of its reference exists (the references sum to `≤ 1`);
   its consensus part is the law, with domination constant `2 · 324 K / ϑ`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial Kernels
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

namespace ComparedSample

variable {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)

theorem agree_law_univ_eq_sum : s.law univ = ∑ Q, s.law (s.agEvQ Q) := by
  have hcov : ∀ᵐ ω ∂s.law, ω ∈ ⋃ Q, s.agEvQ Q := by
    filter_upwards [s.event_cover 0] with ω ⟨e, he⟩
    exact mem_iUnion.mpr ⟨_, s.agree_mem_evQ_of_mem_event he⟩
  have hnull : s.law (⋃ Q, s.agEvQ Q)ᶜ = 0 := ae_iff.mp hcov
  have hmeas : MeasurableSet (⋃ Q, s.agEvQ Q) := MeasurableSet.iUnion s.agree_measurableSet_evQ
  have h1 : s.law univ = s.law (⋃ Q, s.agEvQ Q) := by
    rw [← measure_add_measure_compl hmeas, hnull, add_zero]
  rw [h1]
  have h2 : (⋃ Q, s.agEvQ Q) = ⋃ Q ∈ (Finset.univ : Finset (Fin (p.n k r))), s.agEvQ Q := by
    simp
  rw [h2, measure_biUnion_finset]
  · intro Q _ Q' _ hne
    exact s.agree_evQ_disjoint hne
  · intro Q _
    exact s.agree_measurableSet_evQ Q

/-- **Coefficient consensus at one index.** -/
theorem consensus_at_index (hbase : p.Basic) {R : ℝ} (hat : p.AtDepth k r R) (hN : 1 < p.N k)
    (hK1 : 1 ≤ p.K k) (hKH : p.K k ≤ H) (hℓr : 0 ≤ p.ℓ * r) (hm : 0 ≤ m) (hru : 0 ≤ r + u)
    (hd0 : 0 ≤ p.d) (hd1 : p.d ≤ 1) {βb : ℝ}
    (hδb1 : p.N k ^ (-βb) ≤ 1) (hχ1 : p.N k ^ (-m) ≤ 1)
    (hδbχ' : p.N k ^ (-βb) ≤ p.N k ^ (-m))
    (hfz : 8000000 * p.K k ^ 11 * p.N k ^ (m / 1000) * (p.N k ^ (-βb) + p.N k ^ (-m)) ≤
      p.N k ^ (-(r + u)))
    (hδbχ : 2 * (p.K k + 1) * p.N k ^ (-βb) ≤ p.N k ^ (-m))
    {E : ℝ} (haE : p.N k ^ (-(r + u)) ≤ E)
    {rm : ℝ} (hrm1 : p.N k ^ (-rm) ≤ p.blockLen k r * p.N k ^ (-βb) / 2)
    (hrm2 : 3 * p.K k ^ 2 * p.N k ^ (-rm) ≤ p.N k ^ (-m))
    (hrm3 : 54 * p.N k ^ (m / 1000) * (p.K k + 1) ^ 4 * p.N k ^ (-rm) ≤ p.N k ^ (-(r + u)))
    (hcapk : ∀ s' : ℝ, 0 ≤ s' → s' ≤ r + u → ∀ (q : Fin 3 → ℤ) (a v' : ℤ),
      p.μ k {ω | p.z k (p.N k) rm ω = q ∧
        ⌊eval (p.x k ω.1 ω.2) (p.P k) / (p.N k ^ (-s'))⌋ = a ∧
        ⌊p.b k ω.1 3 / (p.N k ^ (-m))⌋ = v'} ≤
      ENNReal.ofReal (p.K k * p.N k ^ (-3 * rm - p.d * s')) *
        p.π k {w : ℝ | ⌊w / (p.N k ^ (-m))⌋ = v'})
    {θ' : ℝ} (hθ' : 0 < θ') (hθ'E : θ' ≤ E / 8)
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ : ϑ ≤ 1 / (16 * H))
    (hprune : ∀ (Q : Fin (p.n k r)) (θ : Measure (α × ℝ)), θ ≤ p.μ k →
      (∀ᵐ ω ∂θ, ω.1 ∈ p.B k r Q ∧ ω.2 ∈ block (p.T k r) (p.j k r Q)) →
      ∃ θ' : Measure (α × ℝ), θ' ≤ θ ∧
        θ univ ≤ θ' univ +
          ENNReal.ofReal ϑ * (ENNReal.ofReal (p.blockLen k r) * p.ν k (p.A k r Q)) ∧
        ∀ (σ : Fin 4 → ℤ) (j : ℤ),
          θ' {ω | p.nativeState k r Q (p.N k ^ (-βb)) (p.N k ^ (-(r + u))) ω = σ ∧
              ⌊p.b k ω.1 3 / p.N k ^ (-βb)⌋ = j} ≤
            ENNReal.ofReal (324 * p.K k / ϑ) *
              θ' {ω | p.nativeState k r Q (p.N k ^ (-βb)) (p.N k ^ (-(r + u))) ω = σ} *
              p.π k {x | ⌊x / p.N k ^ (-βb)⌋ = j})
    (hεnum : (324 * p.K k / ϑ) * (45 * H ^ 4) * (4200 * p.K k ^ 2 * H * H) *
      (2 * θ' * (4 * p.K k + 2) / (E / 4) +
        8 * (H ^ 4 * p.N k ^ (p.d * u)) * (6 * H * p.N k ^ (-(r + u))) / θ' +
        (2 * (H ^ 4 * p.N k ^ (p.d * u)) + 1) *
          (4 * p.K k * p.N k ^ (-m) / p.blockWidth k r)) ≤ 1 / (16 * H))
    {C : ℝ} (hC : 2 * (324 * p.K k / ϑ) ≤ C) :
    Nonempty (p.ConsensusLaw k s βb (r + u) βb E C) := by
  classical
  have hNpos : 0 < p.N k := by linarith
  have hN1 : 1 ≤ p.N k := hN.le
  have hH2 : 2 ≤ H := s.loss_one
  have hH0 : 0 < H := by linarith
  have hK0 : 0 ≤ p.K k := by linarith
  have hb : Measurable (p.b k) := (hbase k).1
  have hδb : 0 < p.N k ^ (-βb) := Real.rpow_pos_of_pos hNpos _
  have ha : 0 < p.N k ^ (-(r + u)) := Real.rpow_pos_of_pos hNpos _
  have hE : 0 < E := lt_of_lt_of_le ha haE
  set δb := p.N k ^ (-βb) with hδb_def
  set a₁ := p.N k ^ (-(r + u)) with ha₁_def
  have hlawμ := s.agree_law_le_mu hbase
  haveI : IsFiniteMeasure s.law := s.agree_isFiniteMeasure_law hbase
  set Cd := 324 * p.K k / ϑ with hCd_def
  have hCd : 0 ≤ Cd := by positivity
  -- the box of native states
  set M : ℕ := ⌈p.K k / δb + p.K k / a₁⌉₊ + 1 with hM_def
  have hM : p.K k / δb + p.K k / a₁ + 1 ≤ M := by
    rw [hM_def]
    push_cast
    linarith [Nat.le_ceil (p.K k / δb + p.K k / a₁)]
  -- 1. per-block pruning
  let θ₀ : Fin (p.n k r) → Measure (α × ℝ) := fun Q => s.law.restrict (s.agEvQ Q)
  have hθ₀μ : ∀ Q, θ₀ Q ≤ p.μ k := fun Q => Measure.restrict_le_self.trans hlawμ
  have hθ₀ev : ∀ Q, ∀ᵐ ω ∂θ₀ Q, ω ∈ s.agEvQ Q := fun Q => ae_restrict_mem (s.agree_measurableSet_evQ Q)
  have hθ₀supp : ∀ Q, ∀ᵐ ω ∂θ₀ Q, ω.1 ∈ p.B k r Q ∧ ω.2 ∈ block (p.T k r) (p.j k r Q) ∧
      ω ∈ p.baseGood k := by
    intro Q
    filter_upwards [hθ₀ev Q] with ω hω
    obtain ⟨e, he, hωe⟩ := s.agree_mem_evQ.mp hω
    obtain ⟨hgood, hB, ht, -, -⟩ := s.agree_event_data0 hωe
    rw [he] at hB ht
    exact ⟨hB, ht, hgood⟩
  choose θ₁f hθ₁le hθ₁mass hθ₁dom using fun Q => hprune Q (θ₀ Q) (hθ₀μ Q)
    ((hθ₀supp Q).mono fun ω h => ⟨h.1, h.2.1⟩)
  -- 2. the summed pruned law
  let θ₁ : Measure (α × ℝ) := ∑ Q, θ₁f Q
  have hθ₁apply : ∀ A, θ₁ A = ∑ Q, θ₁f Q A := fun A => Measure.finsetSum_apply _ _ _
  have hθ₁fev : ∀ Q, θ₁f Q (s.agEvQ Q)ᶜ = 0 := by
    intro Q
    refine le_antisymm ((hθ₁le Q _).trans ?_) zero_le
    rw [Measure.restrict_apply (s.agree_measurableSet_evQ Q).compl, compl_inter_self, measure_empty]
  have hθ₁fother : ∀ Q Q', Q' ≠ Q → θ₁f Q' (s.agEvQ Q) = 0 := by
    intro Q Q' hne
    refine le_antisymm ((hθ₁le Q' _).trans ?_) zero_le
    rw [Measure.restrict_apply (s.agree_measurableSet_evQ Q)]
    rw [Set.disjoint_iff_inter_eq_empty.mp (s.agree_evQ_disjoint hne.symm), measure_empty]
  have hθ₁inter : ∀ Q A, θ₁ (A ∩ s.agEvQ Q) = θ₁f Q A := by
    intro Q A
    rw [hθ₁apply, Finset.sum_eq_single Q]
    · apply le_antisymm (measure_mono inter_subset_left)
      calc θ₁f Q A ≤ θ₁f Q (A ∩ s.agEvQ Q) + θ₁f Q (A \ s.agEvQ Q) :=
            measure_le_inter_add_sdiff _ _ _
        _ ≤ θ₁f Q (A ∩ s.agEvQ Q) + 0 := by
            gcongr
            exact (measure_mono (fun ω hω => hω.2)).trans (hθ₁fev Q).le
        _ = _ := add_zero _
    · intro Q' _ hne
      exact measure_mono_null inter_subset_right (hθ₁fother Q Q' hne)
    · intro h
      exact absurd (Finset.mem_univ Q) h
  have hθ₁law : θ₁ ≤ s.law := by
    rw [Measure.le_iff]
    intro A hA
    rw [hθ₁apply]
    calc ∑ Q, θ₁f Q A ≤ ∑ Q, θ₀ Q A := Finset.sum_le_sum fun Q _ => hθ₁le Q A
      _ = ∑ Q, s.law (A ∩ s.agEvQ Q) := by
          apply Finset.sum_congr rfl
          intro Q _
          exact Measure.restrict_apply hA
      _ = s.law (⋃ Q ∈ (Finset.univ : Finset (Fin (p.n k r))), A ∩ s.agEvQ Q) := by
          rw [measure_biUnion_finset]
          · intro Q _ Q' _ hne
            exact Disjoint.mono inter_subset_right inter_subset_right (s.agree_evQ_disjoint hne)
          · intro Q _
            exact hA.inter (s.agree_measurableSet_evQ Q)
      _ ≤ s.law A := measure_mono (by
          intro ω hω
          simp only [mem_iUnion] at hω
          obtain ⟨Q, -, hω⟩ := hω
          exact hω.1)
  haveI : IsFiniteMeasure θ₁ := isFiniteMeasure_of_le s.law hθ₁law
  have hθ₁fle : ∀ Q A, θ₁f Q A ≤ θ₁ A := by
    intro Q A
    rw [← hθ₁inter Q A]
    exact measure_mono inter_subset_left
  have hgood0 : θ₁ s.agGoodᶜ = 0 :=
    le_antisymm ((hθ₁law _).trans (s.agree_law_good_compl hbase).le) zero_le
  -- the combined state and its domination
  set st := s.agStF δb a₁ M with hst_def
  have hs : ∀ q, MeasurableSet (st ⁻¹' {q}) := s.agree_measurableSet_stF hb δb a₁ M
  have hnone : θ₁ (st ⁻¹' {none}) = 0 := by
    refine measure_mono_null ?_ hgood0
    intro ω hω hωg
    obtain ⟨e, he⟩ := s.agree_good_event hωg
    obtain ⟨hb', hstω, -⟩ := s.agree_good_state hat hNpos hK1 hδb ha hM hωg he
    have h1 : st ω = none := hω
    rw [hst_def, hstω] at h1
    simp at h1
  have hstsome : ∀ (Q : Fin (p.n k r)) (σ : {σ : Fin 4 → ℤ // σ ∈ agStateBox M}),
      st ⁻¹' {some (Q, σ)} = p.nativeState k r Q δb a₁ ⁻¹' {σ.1} ∩ s.agEvQ Q := by
    intro Q σ
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff]
    rw [hst_def, s.agree_stF_eq_some_iff]
    exact and_comm
  have hdom₁ : ∀ q (j : ℤ),
      θ₁ (st ⁻¹' {q} ∩ {ω | ⌊p.b k ω.1 3 / δb⌋ = j}) ≤
        ENNReal.ofReal Cd * θ₁ (st ⁻¹' {q}) * p.π k {x | ⌊x / δb⌋ = j} := by
    intro q j
    cases q with
    | none =>
      rw [measure_mono_null inter_subset_left hnone]
      exact zero_le
    | some q =>
      obtain ⟨Q, σ⟩ := q
      rw [hstsome Q σ]
      have heq : p.nativeState k r Q δb a₁ ⁻¹' {σ.1} ∩ s.agEvQ Q ∩
          {ω | ⌊p.b k ω.1 3 / δb⌋ = j} =
          {ω | p.nativeState k r Q δb a₁ ω = σ.1 ∧ ⌊p.b k ω.1 3 / δb⌋ = j} ∩ s.agEvQ Q := by
        ext ω
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_setOf_eq]
        tauto
      rw [heq, hθ₁inter, hθ₁inter]
      exact hθ₁dom Q σ.1 j
  -- 3. the disagreement mass and the consensus
  have hD := s.disagreement_le hbase hat hN hK1 hKH hℓr hm hru hd0 hd1 hδb hδb1 hχ1 hδbχ' hfz
    hδbχ haE hrm1 hrm2 hrm3 hcapk hM hθ' hθ'E θ₁ hθ₁law hCd hdom₁
  set ε : ℝ≥0∞ := ENNReal.ofReal (1 / (16 * H)) with hε_def
  have hDε : statePair θ₁ st {pp | ¬ s.agreeRel δb E M (st pp.1) (s.agEntF pp.1) (s.agEntF pp.2)} ≤
      ε := by
    refine hD.trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hεnum
  obtain ⟨center₀, Hc, hHc, hR, hhalf, hmass, -⟩ := consensus_of_pair_mass_le θ₁ st s.agEntF hs
    s.agree_measurableSet_entF (s.agreeRel δb E M) ε hDε
  -- 4. a heavy block
  have hbudget := AtDepth.reference_budget p hbase hat
  have hθ₀univ : ∀ Q, θ₀ Q univ = s.law (s.agEvQ Q) := fun Q => Measure.restrict_apply_univ _
  have hlaw_univ : s.law univ ≤ θ₁ univ + ENNReal.ofReal ϑ := by
    rw [s.agree_law_univ_eq_sum]
    calc ∑ Q, s.law (s.agEvQ Q) ≤ ∑ Q, (θ₁f Q univ +
          ENNReal.ofReal ϑ * (ENNReal.ofReal (p.blockLen k r) * p.ν k (p.A k r Q))) := by
          apply Finset.sum_le_sum
          intro Q _
          rw [← hθ₀univ]
          exact hθ₁mass Q
      _ = θ₁ univ + ENNReal.ofReal ϑ * ∑ Q, p.referenceWeight k r Q := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hθ₁apply]
          rfl
      _ ≤ θ₁ univ + ENNReal.ofReal ϑ * 1 := by gcongr
      _ = θ₁ univ + ENNReal.ofReal ϑ := by rw [mul_one]
  have hheavy : ∃ Q, ENNReal.ofReal (1 / (4 * H)) * p.blockWeight k r Q ≤ θ₁f Q Hc := by
    by_contra hcon
    push_neg at hcon
    have h1 : θ₁ Hc ≤ ENNReal.ofReal (1 / (4 * H)) := by
      rw [hθ₁apply]
      calc ∑ Q, θ₁f Q Hc ≤ ∑ Q, ENNReal.ofReal (1 / (4 * H)) * p.blockWeight k r Q :=
            Finset.sum_le_sum fun Q _ => (hcon Q).le
        _ = ENNReal.ofReal (1 / (4 * H)) * ∑ Q, p.referenceWeight k r Q := by
            rw [← Finset.mul_sum]
            rfl
        _ ≤ ENNReal.ofReal (1 / (4 * H)) * 1 := by gcongr
        _ = _ := mul_one _
    have h2 : ENNReal.ofReal H⁻¹ ≤ ENNReal.ofReal (1 / (4 * H)) + 2 * ε + ENNReal.ofReal ϑ :=
      calc ENNReal.ofReal H⁻¹ ≤ s.law univ := s.mass_lower
        _ ≤ θ₁ univ + ENNReal.ofReal ϑ := hlaw_univ
        _ ≤ (θ₁ Hc + 2 * ε) + ENNReal.ofReal ϑ := by gcongr
        _ ≤ (ENNReal.ofReal (1 / (4 * H)) + 2 * ε) + ENNReal.ofReal ϑ := by gcongr
    have h3 : ENNReal.ofReal (1 / (4 * H)) + 2 * ε + ENNReal.ofReal ϑ =
        ENNReal.ofReal (1 / (4 * H) + 2 * (1 / (16 * H)) + ϑ) := by
      rw [hε_def, ENNReal.ofReal_add (by positivity) hϑ0.le,
        ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat]
    rw [h3, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    have h4 : 1 / (4 * H) + 2 * (1 / (16 * H)) + ϑ ≤ 7 / (16 * H) := by
      have : 1 / (4 * H) + 2 * (1 / (16 * H)) = 6 / (16 * H) := by field_simp; ring
      rw [this]
      have : 6 / (16 * H) + 1 / (16 * H) = 7 / (16 * H) := by field_simp; ring
      linarith
    have h5 : H⁻¹ = 16 / (16 * H) := by field_simp
    have h6 : (7 : ℝ) / (16 * H) < 16 / (16 * H) := by
      apply div_lt_div_of_pos_right (by norm_num) (by positivity)
    linarith
  obtain ⟨Q, hQ⟩ := hheavy
  -- 5. the consensus law of the heavy block
  let law : Measure (α × ℝ) := (θ₁f Q).restrict Hc
  have hlaw_le : law ≤ θ₁f Q := Measure.restrict_le_self
  have hθ₁f_law : θ₁f Q ≤ s.law := (hθ₁le Q).trans Measure.restrict_le_self
  haveI hfinQ : IsFiniteMeasure (θ₁f Q) := isFiniteMeasure_of_le s.law hθ₁f_law
  haveI hfinlaw : IsFiniteMeasure law := isFiniteMeasure_of_le (θ₁f Q) hlaw_le
  have hlaw_θ₀ : law ≤ θ₀ Q := hlaw_le.trans (hθ₁le Q)
  have hac : law ≪ θ₀ Q := Measure.absolutelyContinuous_of_le hlaw_θ₀
  have hlaw_good : ∀ᵐ ω ∂law, ω ∈ s.agGood := by
    have h0 : law s.agGoodᶜ = 0 :=
      le_antisymm (((hlaw_le _).trans (hθ₁fle Q _)).trans hgood0.le) zero_le
    exact ae_iff.mpr h0
  -- the native state of the block
  set ns := p.nativeState k r Q δb a₁ with hns_def
  have hns_meas : ∀ σ, MeasurableSet (ns ⁻¹' {σ}) := fun σ =>
    (p.measurable_nativeState hb r Q δb a₁) (measurableSet_singleton σ)
  have hboxnull : ∀ σ, σ ∉ agStateBox M → θ₁f Q (ns ⁻¹' {σ}) = 0 := by
    intro σ hσ
    rw [← hθ₁inter]
    refine measure_mono_null ?_ hgood0
    intro ω ⟨hωσ, hωQ⟩ hωg
    obtain ⟨e, he, hωe⟩ := s.agree_mem_evQ.mp hωQ
    obtain ⟨hbox, -, -⟩ := s.agree_good_state hat hNpos hK1 hδb ha hM hωg hωe
    rw [he] at hbox
    exact hσ (hωσ ▸ hbox)
  have hhalf' : ∀ σ : Fin 4 → ℤ, law.real (ns ⁻¹' {σ}) = 0 ∨
      (θ₁f Q).real (ns ⁻¹' {σ}) / 2 ≤ law.real (ns ⁻¹' {σ}) := by
    intro σ
    rw [measureReal_restrict_apply (hns_meas σ)]
    by_cases hσ : σ ∈ agStateBox M
    · have hh := hhalf (some (Q, ⟨σ, hσ⟩))
      rw [hstsome Q ⟨σ, hσ⟩] at hh
      have e1 : θ₁ (Hc ∩ (ns ⁻¹' {σ} ∩ s.agEvQ Q)) = θ₁f Q (ns ⁻¹' {σ} ∩ Hc) := by
        rw [← hθ₁inter]
        congr 1
        ext ω
        simp only [mem_inter_iff]
        tauto
      have e2 : θ₁ (ns ⁻¹' {σ} ∩ s.agEvQ Q) = θ₁f Q (ns ⁻¹' {σ}) := hθ₁inter Q _
      rw [e1, e2] at hh
      have := (half_real_iff (θ₁f Q) (ns ⁻¹' {σ} ∩ Hc) (ns ⁻¹' {σ})).mpr hh
      exact this
    · left
      have h0 := hboxnull σ hσ
      rw [measureReal_eq_zero_iff (measure_ne_top _ _)]
      exact measure_mono_null inter_subset_left h0
  have hcap' : ∀ (σ : Fin 4 → ℤ) (j : ℤ),
      θ₁f Q {ω | ns ω = σ ∧ ⌊p.b k ω.1 3 / δb⌋ = j} ≤
        ENNReal.ofReal Cd * θ₁f Q (ns ⁻¹' {σ}) * p.π k {x | ⌊x / δb⌋ = j} := by
    intro σ j
    exact hθ₁dom Q σ j
  have hdomlaw := half_state_palette_ennreal (θ₁f Q) law ns (fun ω => ⌊p.b k ω.1 3 / δb⌋)
    (fun j => p.π k {x | ⌊x / δb⌋ = j}) Cd hlaw_le hCd hhalf' hcap'
  -- the center
  let center : (Fin 4 → ℤ) → Fin 2 → ℝ := fun σ =>
    if h : σ ∈ agStateBox M then
      match center₀ (some (Q, ⟨σ, h⟩)) with
      | some i => p.agPairAt k r Q ((s.layers 0).G i) (p.agRepTime k r Q δb σ) (p.agRepZ k r Q δb σ)
      | none => 0
    else 0
  refine ⟨{
    block := Q
    law := law
    le_law := hlaw_le.trans hθ₁f_law
    finite := hfinlaw
    support := hac.ae_le (hθ₀supp Q)
    mass_lower := by
      show ENNReal.ofReal (1 / (4 * H)) * p.blockWeight k r Q ≤ (θ₁f Q).restrict Hc univ
      rw [Measure.restrict_apply_univ]
      exact hQ
    domination := by
      intro σ j
      have h := hdomlaw σ j
      calc law {ω | ns ω = σ ∧ ⌊p.b k ω.1 3 / δb⌋ = j} ≤
            ENNReal.ofReal (2 * Cd) * law (ns ⁻¹' {σ}) * p.π k {x | ⌊x / δb⌋ = j} := h
        _ ≤ ENNReal.ofReal C * law {ω | ns ω = σ} * p.π k {x | ⌊x / δb⌋ = j} := by
            gcongr
            exact le_rfl
    center := center
    agree := ?_ }⟩
  -- 6. agreement
  have hHcae : ∀ᵐ ω ∂law, ω ∈ Hc := ae_restrict_mem hHc
  have hevae : ∀ᵐ ω ∂law, ω ∈ s.agEvQ Q := hac.ae_le (hθ₀ev Q)
  filter_upwards [hHcae, hevae, hlaw_good] with ω hωH hωQ hωg
  obtain ⟨e, he, hωe⟩ := s.agree_mem_evQ.mp hωQ
  obtain ⟨hbox, hstω, hentω⟩ := s.agree_good_state hat hNpos hK1 hδb ha hM hωg hωe
  have hRω := hR ω hωH
  have hbox' : ns ω ∈ agStateBox M := by
    rw [hns_def, ← he]
    exact hbox
  have hstω' : st ω = some (Q, ⟨ns ω, hbox'⟩) := by
    rw [hst_def]
    exact s.agree_stF_of_mem hωQ hbox'
  rw [hstω', hentω] at hRω
  have hC_mem : (s.layers 0).C (s.coarse 0 e) = (s.layers 0).C (s.coarse 0 e) := rfl
  refine ⟨s.coarse 0 e, (s.agree_event_data0 hωe).2.2.2.1, ?_⟩
  intro c'
  cases hc : center₀ (some (Q, ⟨ns ω, hbox'⟩)) with
  | none =>
    rw [hc] at hRω
    exact absurd hRω (by simp [agreeRel])
  | some i₀ =>
    rw [hc] at hRω
    have hRω' : ∀ c'' : Fin 2,
        |p.agPairAt k r Q ((s.layers 0).G (s.coarse 0 e)) (p.agRepTime k r Q δb (ns ω))
            (p.agRepZ k r Q δb (ns ω)) c'' -
          p.agPairAt k r Q ((s.layers 0).G i₀) (p.agRepTime k r Q δb (ns ω))
            (p.agRepZ k r Q δb (ns ω)) c''| ≤ E / 2 := hRω
    have hcenter : center (ns ω) = p.agPairAt k r Q ((s.layers 0).G i₀)
        (p.agRepTime k r Q δb (ns ω)) (p.agRepZ k r Q δb (ns ω)) := by
      simp only [center, dif_pos hbox', hc]
    rw [hcenter, agree_transPair_eq_pairAt]
    have hfr := s.agree_pair_freeze hat hN1 hK1 hℓr hm hru hδb hχ1 hfz a₁ hωe (s.coarse 0 e) c'
    rw [he] at hfr
    have h2 := hRω' c'
    calc _ ≤ |p.agPairAt k r Q ((s.layers 0).G (s.coarse 0 e)) ω.2 (p.x k ω.1 ω.2 1) c' -
            p.agPairAt k r Q ((s.layers 0).G (s.coarse 0 e)) (p.agRepTime k r Q δb (ns ω))
              (p.agRepZ k r Q δb (ns ω)) c'| +
          |p.agPairAt k r Q ((s.layers 0).G (s.coarse 0 e)) (p.agRepTime k r Q δb (ns ω))
              (p.agRepZ k r Q δb (ns ω)) c' -
            p.agPairAt k r Q ((s.layers 0).G i₀) (p.agRepTime k r Q δb (ns ω))
              (p.agRepZ k r Q δb (ns ω)) c'| := abs_sub_le _ _ _
      _ ≤ a₁ / 8 + E / 2 := add_le_add hfr h2
      _ ≤ E := by linarith

end ComparedSample

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
