-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.GreedyGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-! Ported from o152, session x0449, commit 067fcb7.
Finite extraction from the local grain construction in WZ Lemma 8.2, Step 4.
The uniform positive mass of each new piece ensures termination even when the
same tube contributes to many different pieces.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set
open scoped ENNReal

/-- A bounded sum cannot keep increasing by a fixed positive amount. -/
theorem finite_greedy_of_mass_increment {α : Type*} [DecidableEq α] (w : α → ℝ)
    (P : Finset α → Prop) {q B t : ℝ} (hq : 0 < q) (hzero : P ∅)
    (hbound : ∀ s, P s → (∑ a ∈ s, w a) ≤ B)
    (hstep : ∀ s, P s → (∑ a ∈ s, w a) < t →
      ∃ a, a ∉ s ∧ P (insert a s) ∧ q ≤ w a) :
    ∃ s, P s ∧ t ≤ ∑ a ∈ s, w a := by
  classical
  by_contra h
  have hlt : ∀ s, P s → (∑ a ∈ s, w a) < t := by
    intro s hs
    exact lt_of_not_ge (fun ht => h ⟨s, hs, ht⟩)
  have grow : ∀ k : ℕ, ∃ s, P s ∧ (k : ℝ) * q ≤ ∑ a ∈ s, w a := by
    intro k
    induction k with
    | zero => exact ⟨∅, hzero, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs, hmass⟩ := ih
      obtain ⟨a, ha, hnew, hqmass⟩ := hstep s hs (hlt s hs)
      refine ⟨insert a s, hnew, ?_⟩
      rw [Finset.sum_insert ha, Nat.cast_add, Nat.cast_one]
      nlinarith
  obtain ⟨k, hk⟩ := exists_nat_gt (B / q)
  obtain ⟨s, hs, hmass⟩ := grow k
  have hbig : B < (k : ℝ) * q := (div_lt_iff₀ hq).mp hk
  linarith [hbound s hs]

/-- If every residual shading of at least half the initial mass contains a good
piece of uniformly positive mass, finitely many pieces capture half the mass.
They are disjoint separately on each tube; physical overlap across tubes is allowed.
All geometry of a piece is recorded in the predicate `Good`.
-/
theorem finite_greedy_shading_extraction {X ι α : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (Y : ι → Set X) (W : α → ι → Set X) (Good : α → Prop)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYfin : ∀ i, μ (Y i) ≠ ∞)
    {q : ℝ} (hq : 0 < q)
    (hselect : ∀ R : ι → Set X, (∀ i, MeasurableSet (R i)) → (∀ i, R i ⊆ Y i) →
      (∑ i, μ.real (Y i)) / 2 ≤ ∑ i, μ.real (R i) →
      ∃ a, Good a ∧ (∀ i, MeasurableSet (W a i) ∧ W a i ⊆ R i) ∧
        q ≤ ∑ i, μ.real (W a i)) :
    ∃ s : Finset α,
      (∀ a ∈ s, Good a ∧ ∀ i, MeasurableSet (W a i) ∧ W a i ⊆ Y i) ∧
      (∀ i, PairwiseDisjoint (s : Set α) (fun a => W a i)) ∧
      (∑ i, μ.real (Y i)) / 2 ≤ ∑ i, μ.real (⋃ a ∈ s, W a i) := by
  classical
  let U (s : Finset α) (i : ι) : Set X := ⋃ a ∈ s, W a i
  let P (s : Finset α) : Prop :=
    (∀ a ∈ s, Good a ∧ ∀ i, MeasurableSet (W a i) ∧ W a i ⊆ Y i) ∧
    ∀ i, PairwiseDisjoint (s : Set α) (fun a => W a i)
  have hsub : ∀ s, P s → ∀ i, U s i ⊆ Y i := by
    intro s hs i p hp
    obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.mp hp
    exact ((hs.1 a ha).2 i).2 hpa
  have hmeas : ∀ s, P s → ∀ i, MeasurableSet (U s i) := by
    intro s hs i
    exact Finset.measurableSet_biUnion s (fun a ha => ((hs.1 a ha).2 i).1)
  have hmass : ∀ s, P s → (∑ a ∈ s, ∑ i, μ.real (W a i)) = ∑ i, μ.real (U s i) := by
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact (measureReal_biUnion_finset (hs.2 i)
      (fun a ha => ((hs.1 a ha).2 i).1)
      (fun a ha => measure_ne_top_of_subset ((hs.1 a ha).2 i).2 (hYfin i))).symm
  have hbound : ∀ s, P s → (∑ a ∈ s, ∑ i, μ.real (W a i)) ≤ ∑ i, μ.real (Y i) := by
    intro s hs
    rw [hmass s hs]
    exact Finset.sum_le_sum (fun i _ => measureReal_mono (hsub s hs i) (hYfin i))
  have hzero : P ∅ := by simp [P, Set.PairwiseDisjoint, Set.Pairwise]
  have hstep : ∀ s, P s → (∑ a ∈ s, ∑ i, μ.real (W a i)) < (∑ i, μ.real (Y i)) / 2 →
      ∃ a, a ∉ s ∧ P (insert a s) ∧ q ≤ ∑ i, μ.real (W a i) := by
    intro s hs hsmall
    let R : ι → Set X := fun i => Y i \ U s i
    have hRm : ∀ i, MeasurableSet (R i) := fun i => (hYm i).diff (hmeas s hs i)
    have hRsub : ∀ i, R i ⊆ Y i := fun _ => sdiff_subset
    have hbalance : (∑ i, μ.real (R i)) + (∑ i, μ.real (U s i)) = ∑ i, μ.real (Y i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have heq : Y i ∩ U s i = U s i := inter_eq_right.mpr (hsub s hs i)
      simpa only [R, heq] using measureReal_sdiff_add_inter (μ := μ) (s := Y i) (hmeas s hs i) (hYfin i)
    obtain ⟨a, haGood, haW, hamass⟩ := hselect R hRm hRsub (by rw [hmass s hs] at hsmall; linarith)
    have hnew : a ∉ s := by
      intro ha
      have hempty : ∀ i, W a i = ∅ := by
        intro i
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact ((haW i).2 hp).2 (mem_iUnion₂.mpr ⟨a, ha, hp⟩)
      simp only [hempty, measureReal_empty, Finset.sum_const_zero] at hamass
      linarith
    have hdisj : ∀ i b, b ∈ s → Disjoint (W a i) (W b i) := by
      intro i b hb
      apply Set.disjoint_left.mpr
      intro p hpa hpb
      exact ((haW i).2 hpa).2 (mem_iUnion₂.mpr ⟨b, hb, hpb⟩)
    refine ⟨a, hnew, ⟨?_, ?_⟩, hamass⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact ⟨haGood, fun i => ⟨(haW i).1, (haW i).2.trans (hRsub i)⟩⟩
      · exact hs.1 b hb
    · intro i b hb c hc hbc
      rcases Finset.mem_insert.mp hb with hba | hbs
      · rcases Finset.mem_insert.mp hc with hca | hcs
        · exact (hbc (hba.trans hca.symm)).elim
        · simpa only [hba] using hdisj i c hcs
      · rcases Finset.mem_insert.mp hc with hca | hcs
        · simpa only [hca] using (hdisj i b hbs).symm
        · exact hs.2 i hbs hcs hbc
  obtain ⟨s, hs, hlarge⟩ := finite_greedy_of_mass_increment
    (fun a => ∑ i, μ.real (W a i)) P hq hzero hbound hstep
  exact ⟨s, hs.1, hs.2, by simpa only [hmass s hs] using hlarge⟩

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
