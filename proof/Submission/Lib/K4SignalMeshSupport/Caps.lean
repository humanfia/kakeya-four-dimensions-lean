/-
Adapted from: here:o222 (session x0774), SignalGroupCap.lean, commit 1823dd94.
-/
import Submission.Lib.K4QuadraticSublevel

/-! Recover original base caps by summing stable native signal bins. -/

namespace Submission.Lib.K4SignalMeshSupport

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The arbitrary original condition can include a fixed palette bin. No
normalization or neighboring-palette comparison occurs in the summation. -/
theorem base_cap_of_stable_signal_groups {Ω β ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (cell : Ω → β) (signal : Ω → ℝ) (condition : Ω → Prop)
    (E : ι → Set Ω) {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M)
    (hosc : ∀ i p, p ∈ E i → ∀ p', p' ∈ E i → cell p = cell p' →
      |signal p - signal p'| ≤ M * a)
    (B : β → ℝ≥0∞)
    (hcap : ∀ (q : β) (j : ℤ), μ {p | cell p = q ∧ ⌊signal p / a⌋ = j ∧ condition p} ≤ B q)
    (q : β) :
    μ {p | cell p = q ∧ (∃ i, p ∈ E i) ∧ condition p} ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * (2 * M + 2)) * B q := by
  classical
  have hgroup (i : ι) :
      μ {p | cell p = q ∧ p ∈ E i ∧ condition p} ≤ ENNReal.ofReal (2 * M + 2) * B q := by
    let S : Set ℝ := {x | ∃ p, cell p = q ∧ p ∈ E i ∧ signal p = x}
    have hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ M * a := by
      rintro x ⟨p, hpq, hp, rfl⟩ y ⟨p', hp'q, hp', rfl⟩
      rw [Real.dist_eq]
      exact hosc i p hp p' hp' (hpq.trans hp'q.symm)
    obtain ⟨hfin, hcard⟩ := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      S (mul_nonneg hM ha.le) ha 0 hdiam
    let F := hfin.toFinset
    have hF : (F.card : ℝ) ≤ 2 * M + 2 := by
      have heq : 2 * (M * a) / a + 2 = 2 * M + 2 := by field_simp
      simpa only [F, Set.ncard_eq_toFinset_card _ hfin, heq] using hcard
    have hsub : {p | cell p = q ∧ p ∈ E i ∧ condition p} ⊆
        ⋃ j ∈ F, {p | cell p = q ∧ ⌊signal p / a⌋ = j ∧ condition p} := by
      intro p hp
      have hj : ⌊signal p / a⌋ ∈ F := by
        apply hfin.mem_toFinset.mpr
        exact ⟨signal p, ⟨p, hp.1, hp.2.1, rfl⟩, by simp⟩
      exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨hj, hp.1, rfl, hp.2.2⟩⟩
    calc
      _ ≤ μ (⋃ j ∈ F, {p | cell p = q ∧ ⌊signal p / a⌋ = j ∧ condition p}) := measure_mono hsub
      _ ≤ ∑ j ∈ F, μ {p | cell p = q ∧ ⌊signal p / a⌋ = j ∧ condition p} :=
        measure_biUnion_finset_le F _
      _ ≤ ∑ _j ∈ F, B q := Finset.sum_le_sum (fun j hj => hcap q j)
      _ = ENNReal.ofReal (F.card : ℝ) * B q := by simp
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hF) le_rfl
  have hsub : {p | cell p = q ∧ (∃ i, p ∈ E i) ∧ condition p} ⊆
      ⋃ i, {p | cell p = q ∧ p ∈ E i ∧ condition p} := by
    rintro p ⟨hpq, ⟨i, hi⟩, hc⟩
    exact mem_iUnion.mpr ⟨i, hpq, hi, hc⟩
  calc
    _ ≤ μ (⋃ i, {p | cell p = q ∧ p ∈ E i ∧ condition p}) := measure_mono hsub
    _ ≤ ∑ i, μ {p | cell p = q ∧ p ∈ E i ∧ condition p} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (2 * M + 2) * B q :=
      Finset.sum_le_sum (fun i hi => hgroup i)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
      ring

end

end Submission.Lib.K4SignalMeshSupport
