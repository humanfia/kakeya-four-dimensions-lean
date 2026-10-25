import Submission.Obl.k4_scalar_pair_atlas_assembly.Interface
set_option autoImplicit false
namespace Submission.Obl.k4_scalar_pair_atlas_assembly
open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
noncomputable section

/-- Candidate atlas before discarding the finitely many zero-mass charts. -/
structure Candidate (p : Code) (B : ℕ) (r b h ε : ℝ) (k T : ℕ)
    (β : Type) [Fintype β] where
  world : β → Fin (W p k)
  block : β → Fin (2 ^ T)
  assigned : β → Set (ℕ × (Fin 5 → ℝ))
  selected : β → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)
  u : β → ℝ
  v : β → ℝ
  J : β → ℝ
  poly : β → MvPolynomial (Fin 2) ℝ
  lists : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset β
  time : (2 : ℝ) ^ T ≤ N p k ^ h
  count : (Fintype.card β : ℝ) ≤ N p k ^ (B : ℝ)
  measurable : ∀ i, MeasurableSet (assigned i) ∧ MeasurableSet (selected i)
  disjoint : ∀ i i', i ≠ i' → world i = world i' → block i = block i' →
    Disjoint (assigned i) (assigned i')
  subset : ∀ i, selected i ⊆ E p k (world i) ∩ (assigned i ×ˢ I T (block i))
  bounds : ∀ i, 0 < J i ∧ (J i)⁻¹ ≤ N p k ^ (B : ℝ) ∧
    J i ≤ N p k ^ ε / (2 : ℝ) ^ T ∧ |u i| + |v i| ≤ N p k ^ ε ∧
    (poly i).totalDegree ≤ 2 ∧ (∀ a, |(poly i).coeff a| ≤ N p k ^ (B : ℝ)) ∧
    (∀ l ∈ assigned i, (l.1 : ℝ) ≤ N p k ^ (B : ℝ) ∧ ∀ e, |l.2 e| ≤ N p k ^ ε) ∧
    (∀ z : ℕ, Format 5 (N p k ^ (B : ℝ)) B {a | (z, a) ∈ assigned i}) ∧
    (∀ z : ℕ, Format 6 (N p k ^ (B : ℝ)) B
      {a | ((z, fun e : Fin 5 => a e.castSucc), a 5) ∈ selected i}) ∧
    (∀ l ∈ assigned i, ∀ t ∈ I T (block i),
      |y l t - u i - t * v i| ≤ N p k ^ ε * J i ∧
      |x l t - MvPolynomial.eval ![t, y l t] (poly i)| ≤ N p k ^ ε * N p k ^ (-r))
  list_card : ∀ a z, ((lists a z).card : ℝ) ≤ N p k ^ ε
  list_measurable : ∀ a i, MeasurableSet {z | i ∈ lists a z}
  recovers : ∀ i, mu p k (world i) {q | q ∈ selected i ∧
    i ∉ lists (world i) ((![q.2, y q.1 q.2] : Fin 2 → ℝ),
      (⌊x q.1 q.2 / (N p k ^ (-b))⌋ : ℤ))} = 0
  mass : ENNReal.ofReal (N p k ^ (-ε)) ≤ ∑ a : Fin (W p k),
    ENNReal.ofReal (ω p k a) * mu p k a {q | ∃ i, world i = a ∧ q ∈ selected i}

lemma positive_label_union {α β ι : Type*} [MeasurableSpace α] [Fintype β]
    (μ : ι → Measure α) (γ : β → ι) (C : β → Set α) (w : ι) :
    μ w {q | ∃ i : β, γ i = w ∧ q ∈ C i} =
      μ w {q | ∃ i : {i : β // 0 < μ (γ i) (C i)}, γ i = w ∧ q ∈ C i} := by
  classical
  have hz (i : β) : μ w {q | γ i = w ∧ q ∈ C i ∧ μ (γ i) (C i) = 0} = 0 := by
    by_cases hw : γ i = w
    · by_cases h0 : μ w (C i) = 0
      · simp [hw, h0]
      · simp [hw, h0]
    · simp [hw]
  apply measure_congr
  have hh : ∀ᵐ q ∂μ w, q ∉ ⋃ i, {q | γ i = w ∧ q ∈ C i ∧ μ (γ i) (C i) = 0} := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using measure_iUnion_null hz
  filter_upwards [hh] with q hq
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hq
  apply propext
  constructor
  · rintro ⟨i, hi, hqi⟩
    have hp : 0 < μ (γ i) (C i) := bot_lt_iff_ne_bot.mpr fun h0 => hq i ⟨hi, hqi, h0⟩
    exact ⟨⟨i, hp⟩, hi, hqi⟩
  · rintro ⟨i, hi, hqi⟩
    exact ⟨i.val, hi, hqi⟩

/-- Enumerate precisely the positive-mass labels. All list and format bounds survive. -/
theorem Candidate.to_chart {p : Code} {B : ℕ} {r b h ε : ℝ} {k T : ℕ}
    {β : Type} [Fintype β] (s : Candidate p B r b h ε k T β) :
    Chart p B r b h ε false k := by
  classical
  let βp := {i : β // 0 < mu p k (s.world i) (s.selected i)}
  let n := Fintype.card βp
  let e : βp ≃ Fin n := Fintype.equivFin βp
  let a : Fin n → β := fun i => (e.symm i).val
  let Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n) :=
    fun w z => ((s.lists w z).subtype (fun i => 0 < mu p k (s.world i) (s.selected i))).map
      e.toEmbedding
  have hmem (w z i) : i ∈ Λ w z ↔ a i ∈ s.lists w z := by
    simp [Λ, a]
    exact Finset.mem_subtype
  refine ⟨T, n, s.world ∘ a, s.block ∘ a, s.assigned ∘ a, s.selected ∘ a,
    s.u ∘ a, s.v ∘ a, s.J ∘ a, s.poly ∘ a, Λ, ?_⟩
  have hainj : Function.Injective a := Subtype.val_injective.comp e.symm.injective
  refine ⟨s.time, ?_, (fun i => s.measurable (a i)),
    (fun i i' hne hw hj => s.disjoint (a i) (a i') (fun heq => hne (hainj heq)) hw hj),
    (fun i => s.subset (a i)), ?_, ?_, ?_, ?_, ?_⟩
  · have hc : n ≤ Fintype.card β := Fintype.card_subtype_le _
    exact (Nat.cast_le.mpr hc).trans s.count
  · intro i
    refine ⟨(e.symm i).property, ?_⟩
    simpa using s.bounds (a i)
  · intro w z
    have hc : (Λ w z).card ≤ (s.lists w z).card :=
      Finset.card_le_card_of_injOn a
        (fun i hi => (hmem w z i).mp hi) hainj.injOn
    exact (Nat.cast_le.mpr hc).trans (s.list_card w z)
  · intro w i
    have hh : {z | i ∈ Λ w z} = {z | a i ∈ s.lists w z} := by
      ext z
      simp only [hmem]
    rw [hh]
    exact s.list_measurable w (a i)
  · intro i
    have hh : {q | q ∈ (s.selected ∘ a) i ∧
      i ∉ Λ ((s.world ∘ a) i) ((![q.2, y q.1 q.2] : Fin 2 → ℝ),
        (⌊x q.1 q.2 / (N p k ^ (-b))⌋ : ℤ))} =
      {q | q ∈ s.selected (a i) ∧
      a i ∉ s.lists (s.world (a i)) ((![q.2, y q.1 q.2] : Fin 2 → ℝ),
        (⌊x q.1 q.2 / (N p k ^ (-b))⌋ : ℤ))} := by
      ext q
      simp only [hmem, Function.comp_apply]
    rw [hh]
    exact s.recovers (a i)
  · convert s.mass using 1
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    rw [positive_label_union (mu p k) s.world s.selected w]
    congr 1
    ext q
    simp only [mem_ofPred_eq, Function.comp_apply]
    constructor
    · rintro ⟨i, hi, hq⟩
      exact ⟨e.symm i, hi, hq⟩
    · rintro ⟨i, hi, hq⟩
      exact ⟨e i, by simpa [a] using hi, by simpa [a] using hq⟩

end
end Submission.Obl.k4_scalar_pair_atlas_assembly
