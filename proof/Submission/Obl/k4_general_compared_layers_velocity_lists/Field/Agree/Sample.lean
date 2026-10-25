-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.Sample; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Defs

/-!
# Structural facts about the objects of one compared sample

Membership characterizations and measurability of the parent events `agEvQ`, the block label
`agBlk`, the finite combined state `agStF`, the coarse label `agEntF`, the sources `agSrc` and the agGood
set `agGood`, and the nullity of the complement of `agGood` under the sample law.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

namespace ComparedSample

variable {α : Type} [MeasurableSpace α] {p : Parent α}
variable {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)

theorem agree_mem_evQ {ω : α × ℝ} {Q : Fin (p.n k r)} :
    ω ∈ s.agEvQ Q ↔ ∃ e, s.parent 0 e = Q ∧ ω ∈ s.event 0 e := by
  simp only [agEvQ, mem_iUnion, exists_prop]

theorem agree_measurableSet_evQ (Q : Fin (p.n k r)) : MeasurableSet (s.agEvQ Q) :=
  MeasurableSet.iUnion fun e => MeasurableSet.iUnion fun _ => s.event_measurable 0 e

theorem agree_mem_evQ_of_mem_event {ω : α × ℝ} {e : Fin (s.count 0)} (h : ω ∈ s.event 0 e) :
    ω ∈ s.agEvQ (s.parent 0 e) :=
  (s.agree_mem_evQ).mpr ⟨e, rfl, h⟩

theorem agree_event_eq_of_mem {ω : α × ℝ} {e e' : Fin (s.count 0)} (h : ω ∈ s.event 0 e)
    (h' : ω ∈ s.event 0 e') : e = e' := by
  by_contra hne
  exact Set.disjoint_left.mp (s.event_disjoint 0 hne) h h'

theorem agree_evQ_eq_of_mem {ω : α × ℝ} {Q Q' : Fin (p.n k r)} (h : ω ∈ s.agEvQ Q)
    (h' : ω ∈ s.agEvQ Q') : Q = Q' := by
  obtain ⟨e, he, hω⟩ := (s.agree_mem_evQ).mp h
  obtain ⟨e', he', hω'⟩ := (s.agree_mem_evQ).mp h'
  rw [← he, ← he', s.agree_event_eq_of_mem hω hω']

theorem agree_evQ_disjoint {Q Q' : Fin (p.n k r)} (hQ : Q ≠ Q') : Disjoint (s.agEvQ Q) (s.agEvQ Q') :=
  Set.disjoint_left.mpr fun _ h h' => hQ (s.agree_evQ_eq_of_mem h h')

theorem agree_blk_eq_some_iff {ω : α × ℝ} {Q : Fin (p.n k r)} : s.agBlk ω = some Q ↔ ω ∈ s.agEvQ Q := by
  classical
  unfold agBlk
  by_cases h : ∃ Q, ω ∈ s.agEvQ Q
  · rw [dif_pos h]
    constructor
    · intro hQ
      rw [← Option.some_inj.mp hQ]
      exact Classical.choose_spec h
    · intro hQ
      exact congrArg some (s.agree_evQ_eq_of_mem (Classical.choose_spec h) hQ)
  · rw [dif_neg h]
    simp only [reduceCtorEq, false_iff]
    exact fun hQ => h ⟨Q, hQ⟩

theorem agree_blk_eq_none_iff {ω : α × ℝ} : s.agBlk ω = none ↔ ∀ Q, ω ∉ s.agEvQ Q := by
  constructor
  · intro h Q hQ
    rw [(s.agree_blk_eq_some_iff).mpr hQ] at h
    simp at h
  · intro h
    cases hb : s.agBlk ω with
    | none => rfl
    | some Q => exact absurd ((s.agree_blk_eq_some_iff).mp hb) (h Q)

theorem agree_blk_of_mem_event {ω : α × ℝ} {e : Fin (s.count 0)} (h : ω ∈ s.event 0 e) :
    s.agBlk ω = some (s.parent 0 e) :=
  (s.agree_blk_eq_some_iff).mpr (s.agree_mem_evQ_of_mem_event h)

theorem agree_stF_eq_some_iff {δb δs : ℝ} {M : ℕ} {ω : α × ℝ} {Q : Fin (p.n k r)}
    {σ : {σ : Fin 4 → ℤ // σ ∈ agStateBox M}} :
    s.agStF δb δs M ω = some (Q, σ) ↔ ω ∈ s.agEvQ Q ∧ p.nativeState k r Q δb δs ω = σ.1 := by
  classical
  unfold agStF
  cases hb : s.agBlk ω with
  | none =>
    simp only [Option.bind_none, reduceCtorEq, false_iff, not_and]
    intro hQ
    rw [(s.agree_blk_eq_some_iff).mpr hQ] at hb
    exact absurd hb (by simp)
  | some Q₀ =>
    have hQ₀ : ω ∈ s.agEvQ Q₀ := (s.agree_blk_eq_some_iff).mp hb
    simp only [Option.bind_some]
    by_cases hm : p.nativeState k r Q₀ δb δs ω ∈ agStateBox M
    · rw [dif_pos hm]
      constructor
      · intro heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨h1, h2⟩ := heq
        subst h1
        exact ⟨hQ₀, by rw [← h2]⟩
      · rintro ⟨hQ, hσ⟩
        have hQQ : Q₀ = Q := s.agree_evQ_eq_of_mem hQ₀ hQ
        subst hQQ
        simp only [Option.some.injEq, Prod.mk.injEq, true_and]
        exact Subtype.ext hσ
    · rw [dif_neg hm]
      simp only [reduceCtorEq, false_iff, not_and]
      intro hQ hσ
      have hQQ : Q₀ = Q := s.agree_evQ_eq_of_mem hQ₀ hQ
      subst hQQ
      exact hm (hσ ▸ σ.2)

theorem agree_stF_of_mem {δb δs : ℝ} {M : ℕ} {ω : α × ℝ} {Q : Fin (p.n k r)} (hQ : ω ∈ s.agEvQ Q)
    (hbox : p.nativeState k r Q δb δs ω ∈ agStateBox M) :
    s.agStF δb δs M ω = some (Q, ⟨_, hbox⟩) :=
  (s.agree_stF_eq_some_iff).mpr ⟨hQ, rfl⟩

theorem agree_measurableSet_stF_some (hb : Measurable (p.b k)) (δb δs : ℝ) (M : ℕ)
    (q : Fin (p.n k r) × {σ : Fin 4 → ℤ // σ ∈ agStateBox M}) :
    MeasurableSet (s.agStF δb δs M ⁻¹' {some q}) := by
  obtain ⟨Q, σ⟩ := q
  have heq : s.agStF δb δs M ⁻¹' {some (Q, σ)} =
      s.agEvQ Q ∩ p.nativeState k r Q δb δs ⁻¹' {σ.1} := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff]
    exact s.agree_stF_eq_some_iff
  rw [heq]
  exact (s.agree_measurableSet_evQ Q).inter
    ((p.measurable_nativeState hb r Q δb δs) (measurableSet_singleton _))

theorem agree_measurableSet_stF (hb : Measurable (p.b k)) (δb δs : ℝ) (M : ℕ)
    (q : Option (Fin (p.n k r) × {σ : Fin 4 → ℤ // σ ∈ agStateBox M})) :
    MeasurableSet (s.agStF δb δs M ⁻¹' {q}) := by
  cases q with
  | some q => exact s.agree_measurableSet_stF_some hb δb δs M q
  | none =>
    have heq : s.agStF δb δs M ⁻¹' {none} = (⋃ q, s.agStF δb δs M ⁻¹' {some q})ᶜ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, not_exists]
      constructor
      · intro h q hq
        rw [h] at hq
        simp at hq
      · intro h
        cases hω : s.agStF δb δs M ω with
        | none => rfl
        | some q => exact absurd hω (h q)
    rw [heq]
    exact (MeasurableSet.iUnion fun q => s.agree_measurableSet_stF_some hb δb δs M q).compl

theorem agree_entF_eq_some_iff {ω : α × ℝ} {i : Fin (s.layers 0).count} :
    s.agEntF ω = some i ↔ ω.1 ∈ (s.layers 0).C i := by
  classical
  have hdisj := (s.layer_valid 0).2.2.2.2.1
  unfold agEntF
  by_cases h : ∃ i, ω.1 ∈ (s.layers 0).C i
  · rw [dif_pos h]
    constructor
    · intro hi
      rw [← Option.some_inj.mp hi]
      exact Classical.choose_spec h
    · intro hi
      congr 1
      by_contra hne
      exact Set.disjoint_left.mp (hdisj _ _ hne) (Classical.choose_spec h) hi
  · rw [dif_neg h]
    simp only [reduceCtorEq, false_iff]
    exact fun hi => h ⟨i, hi⟩

theorem agree_measurableSet_entF (i : Option (Fin (s.layers 0).count)) :
    MeasurableSet (s.agEntF ⁻¹' {i}) := by
  have hC := (s.layer_valid 0).2.2.2.1
  have hsome : ∀ i : Fin (s.layers 0).count, MeasurableSet (s.agEntF ⁻¹' {some i}) := by
    intro i
    have heq : s.agEntF ⁻¹' {some i} = Prod.fst ⁻¹' (s.layers 0).C i := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff]
      exact s.agree_entF_eq_some_iff
    rw [heq]
    exact measurable_fst (hC i)
  cases i with
  | some i => exact hsome i
  | none =>
    have heq : s.agEntF ⁻¹' {none} = (⋃ i, s.agEntF ⁻¹' {some i})ᶜ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_compl_iff, mem_iUnion, not_exists]
      constructor
      · intro h q hq
        rw [h] at hq
        simp at hq
      · intro h
        cases hω : s.agEntF ω with
        | none => rfl
        | some q => exact absurd hω (h q)
    rw [heq]
    exact (MeasurableSet.iUnion hsome).compl

theorem agree_measurableSet_good (hb : Measurable (p.b k)) : MeasurableSet s.agGood := by
  refine (MeasurableSet.iUnion fun e => s.event_measurable 0 e).inter ?_
  exact measurableSet_le ((p.measurable_signal hb).abs) measurable_const

theorem agree_measurableSet_src (δb : ℝ) (e : Fin (s.count 0)) (c : ℤ) :
    MeasurableSet (s.agSrc δb e c) := by
  refine (s.event_measurable 0 e).inter ?_
  exact measurableSet_eq_fun (((p.measurable_tauN k r _).div_const δb).floor) measurable_const

theorem agree_law_le_mu (hbase : p.Basic) : s.law ≤ p.μ k :=
  s.le_rho.trans (hbase k).2.2.2.2.1

theorem agree_law_good_compl (hbase : p.Basic) : s.law s.agGoodᶜ = 0 := by
  have hcov := s.event_cover 0
  have hsig : ∀ᵐ ω ∂p.μ k, |p.signal k ω.1 ω.2| ≤ p.K k := by
    filter_upwards [(hbase k).2.2.2.2.2.2.2.2.2, Basic.ae_unit p hbase k] with ω hω ht
    exact (hω.1 ω.2 ht).1
  have hsig' : ∀ᵐ ω ∂s.law, |p.signal k ω.1 ω.2| ≤ p.K k :=
    (Measure.absolutelyContinuous_of_le (s.agree_law_le_mu hbase)).ae_le hsig
  have : ∀ᵐ ω ∂s.law, ω ∈ s.agGood := by
    filter_upwards [hcov, hsig'] with ω hω hs
    exact ⟨mem_iUnion.mpr hω, hs⟩
  exact ae_iff.mp this

theorem agree_isFiniteMeasure_law (hbase : p.Basic) : IsFiniteMeasure s.law := by
  have := Basic.finite_mu p hbase k
  exact isFiniteMeasure_of_le (p.μ k) (s.agree_law_le_mu hbase)

end ComparedSample

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
