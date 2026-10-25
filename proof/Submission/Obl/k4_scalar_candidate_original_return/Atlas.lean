import Submission.Obl.k4_scalar_candidate_original_return.Defs
import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Lists

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set

/-- An original atlas certificate permits null selected pieces. The final
constructor removes those labels without altering any other bound. -/
structure AtlasCertificate (p : Code) (k B : ℕ) (r b h ε : ℝ) where
  data : Layer (W p k)
  time_bound : (2 : ℝ) ^ data.T ≤ N p k ^ h
  size_bound : (data.n : ℝ) ≤ N p k ^ (B : ℝ)
  measurable : ∀ i, MeasurableSet (data.prior i) ∧ MeasurableSet (data.selected i)
  disjoint : ∀ i i', i ≠ i' → data.world i = data.world i' → data.time i = data.time i' →
    Disjoint (data.prior i) (data.prior i')
  selected_subset : ∀ i, data.selected i ⊆ E p k (data.world i) ∩
    (data.prior i ×ˢ I data.T (data.time i))
  geometry : ∀ i, 0 < data.width i ∧ (data.width i)⁻¹ ≤ N p k ^ (B : ℝ) ∧
    data.width i ≤ N p k ^ ε / (2 : ℝ) ^ data.T ∧
    |data.u i| + |data.v i| ≤ N p k ^ ε ∧ (data.poly i).totalDegree ≤ 2 ∧
    (∀ a, |(data.poly i).coeff a| ≤ N p k ^ (B : ℝ)) ∧
    (∀ l ∈ data.prior i, (l.1 : ℝ) ≤ N p k ^ (B : ℝ) ∧ ∀ e, |l.2 e| ≤ N p k ^ ε) ∧
    (∀ z : ℕ, Format 5 (N p k ^ (B : ℝ)) B {a | (z, a) ∈ data.prior i}) ∧
    (∀ z : ℕ, Format 6 (N p k ^ (B : ℝ)) B
      {a | ((z, fun e : Fin 5 => a e.castSucc), a 5) ∈ data.selected i}) ∧
    (∀ l ∈ data.prior i, ∀ t ∈ I data.T (data.time i),
      |y l t - data.u i - t * data.v i| ≤ N p k ^ ε * data.width i ∧
      |x l t - MvPolynomial.eval ![t, y l t] (data.poly i)| ≤ N p k ^ ε * N p k ^ (-r))
  list_card : ∀ a z, ((data.lists a z).card : ℝ) ≤ N p k ^ ε
  list_measurable : ∀ a i, MeasurableSet {z | i ∈ data.lists a z}
  list_success : ∀ i, mu p k (data.world i) {q | q ∈ data.selected i ∧
    i ∉ data.lists (data.world i) ((![q.2, y q.1 q.2] : Fin 2 → ℝ),
      (⌊x q.1 q.2 / (N p k ^ (-b))⌋ : ℤ))} = 0
  mass : ENNReal.ofReal (N p k ^ (-ε)) ≤
    ∑ a, ENNReal.ofReal (ω p k a) * mu p k a {q | ∃ i, data.world i = a ∧ q ∈ data.selected i}

/-- Null label deletion preserves an arbitrary finite world's union mass. -/
lemma positive_labels_union_mass {α : Type*} [MeasurableSpace α] {w n : ℕ}
    (μ : Fin w → Measure α) (γ : Fin n → Fin w) (C : Fin n → Set α) (a : Fin w) :
    μ a {q | ∃ i, γ i = a ∧ q ∈ C i} =
      μ a {q | ∃ i, 0 < μ (γ i) (C i) ∧ γ i = a ∧ q ∈ C i} := by
  classical
  let bad : Set α := {q | ∃ i, ¬0 < μ (γ i) (C i) ∧ γ i = a ∧ q ∈ C i}
  have hnull (i : Fin n) : μ a {q | ¬0 < μ (γ i) (C i) ∧ γ i = a ∧ q ∈ C i} = 0 := by
    by_cases hγ : γ i = a
    · by_cases hpos : 0 < μ (γ i) (C i)
      · simp [hpos]
      · have hzero : μ (γ i) (C i) = 0 := le_antisymm (not_lt.mp hpos) bot_le
        have hzero' : μ a (C i) = 0 := by simpa only [hγ] using hzero
        simpa [hγ, hzero'] using hzero' 
    · simp [hγ]
  have hbad : μ a bad = 0 := by
    have heq : bad = ⋃ i, {q | ¬0 < μ (γ i) (C i) ∧ γ i = a ∧ q ∈ C i} := by
      ext q
      simp [bad]
    rw [heq]
    exact measure_iUnion_null hnull
  apply le_antisymm
  · calc
      _ ≤ μ a ({q | ∃ i, 0 < μ (γ i) (C i) ∧ γ i = a ∧ q ∈ C i} ∪ bad) := by
        apply measure_mono
        rintro q ⟨i, hγ, hq⟩
        by_cases hpos : 0 < μ (γ i) (C i)
        · exact Or.inl ⟨i, hpos, hγ, hq⟩
        · exact Or.inr ⟨i, hpos, hγ, hq⟩
      _ ≤ μ a {q | ∃ i, 0 < μ (γ i) (C i) ∧ γ i = a ∧ q ∈ C i} + μ a bad :=
        measure_union_le _ _
      _ = _ := by rw [hbad, add_zero]
  · exact measure_mono (by rintro q ⟨i, _, hγ, hq⟩; exact ⟨i, hγ, hq⟩)

/-- Assemble a literal false-flag chart, removing every zero-mass output label. -/
theorem AtlasCertificate.chart {p : Code} {k B : ℕ} {r b h ε : ℝ}
    (c : AtlasCertificate p k B r b h ε) : Chart p B r b h ε false k := by
  classical
  let a := c.data
  let F : Finset (Fin a.n) := Finset.univ.filter (fun i => 0 < mu p k (a.world i) (a.selected i))
  let e : Fin F.card ≃ F := F.equivFin.symm
  let ei : Fin F.card → Fin a.n := fun i => e i
  have hei : Function.Injective ei := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  let Λ : Fin (W p k) → (Base × ℤ) → Finset (Fin F.card) :=
    fun g z => Finset.univ.filter (fun i => ei i ∈ a.lists g z)
  have hpositive (i : Fin F.card) : 0 < mu p k (a.world (ei i)) (a.selected (ei i)) := by
    exact (Finset.mem_filter.mp (e i).property).2
  have hmass : ENNReal.ofReal (N p k ^ (-ε)) ≤
      ∑ g, ENNReal.ofReal (ω p k g) *
        mu p k g {q | ∃ i : Fin F.card, a.world (ei i) = g ∧ q ∈ a.selected (ei i)} := by
    apply c.mass.trans
    apply Finset.sum_le_sum
    intro g _
    apply mul_le_mul_of_nonneg_left _ zero_le
    rw [positive_labels_union_mass (mu p k) a.world a.selected g]
    apply measure_mono
    rintro q ⟨i, hpos, hγ, hq⟩
    have hi : i ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
    refine ⟨e.symm ⟨i, hi⟩, ?_, ?_⟩
    · simpa only [ei, Equiv.apply_symm_apply] using hγ
    · simpa only [ei, Equiv.apply_symm_apply] using hq
  refine ⟨a.T, F.card, fun i => a.world (ei i), fun i => a.time (ei i),
    fun i => a.prior (ei i), fun i => a.selected (ei i), fun i => a.u (ei i),
    fun i => a.v (ei i), fun i => a.width (ei i), fun i => a.poly (ei i), Λ, ?_⟩
  refine ⟨c.time_bound, ?_, (fun i => c.measurable (ei i)), ?_,
    (fun i => c.selected_subset (ei i)), ?_, ?_, ?_, ?_, hmass⟩
  · exact (Nat.cast_le.mpr (by simpa using F.card_le_univ)).trans c.size_bound
  · intro i i' hii hγ hj
    exact c.disjoint (ei i) (ei i') (fun heq => hii (hei heq)) hγ hj
  · intro i
    rcases c.geometry (ei i) with
      ⟨hJ, hinv, hup, hctr, hdeg, hcoef, hA, hAf, hCf, hfit⟩
    exact ⟨hpositive i, hJ, hinv, hup, hctr, hdeg, hcoef, hA, hAf, hCf, hfit, by simp⟩
  · intro g z
    have hcard := k4_scalar_true_atlas_terminal_lists.reindexed_list_card ei hei (a.lists g z)
    exact (Nat.cast_le.mpr hcard).trans (c.list_card g z)
  · intro g i
    simpa only [Λ, Finset.mem_filter, Finset.mem_univ, true_and] using c.list_measurable g (ei i)
  · intro i
    simpa only [Λ, Finset.mem_filter, Finset.mem_univ, true_and] using c.list_success (ei i)

end Submission.Obl.k4_scalar_candidate_original_return
