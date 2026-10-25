-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Regularize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Dyadic regularization of nested cell populations

Generic combinatorics for the balance clause of the frozen `S`. Points `i ∈ S` carry, at each
level `k`, a cell `κ k i`; levels are nested (equal cells at a finer level are equal at every
coarser level). Processing the levels from fine to coarse and keeping, at each level, the cells
of the most popular dyadic population class, every surviving cell at every level ends up with a
population in a fixed dyadic range `[2^c, 2^(c+1))`, at a cost of a factor `log₂ |S| + 1` per
level. Keeping whole coarse cells keeps whole finer cells, so finer levels stay balanced.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

open Finset

/-- The population of the cell of `i` in `S`. -/
def pop {ι α : Type*} [DecidableEq α] (S : Finset ι) (κ : ι → α) (i : ι) : ℕ :=
  (S.filter (fun j => κ j = κ i)).card

lemma pop_pos {ι α : Type*} [DecidableEq α] {S : Finset ι} {κ : ι → α} {i : ι} (hi : i ∈ S) :
    0 < pop S κ i :=
  Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, rfl⟩⟩

lemma pop_le {ι α : Type*} [DecidableEq α] (S : Finset ι) (κ : ι → α) (i : ι) :
    pop S κ i ≤ S.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- One level: keep the cells of the most popular dyadic population class. -/
theorem dyadic_class_refine {ι α : Type*} [DecidableEq ι] [DecidableEq α] (S : Finset ι)
    (hS : S.Nonempty) (κ : ι → α) :
    ∃ S' ⊆ S, S'.Nonempty ∧ (S.card : ℝ) ≤ ((Nat.log 2 S.card : ℝ) + 1) * S'.card ∧
      (∀ i ∈ S', ∀ j ∈ S, κ j = κ i → j ∈ S') ∧
      ∃ c : ℕ, ∀ i ∈ S', 2 ^ c ≤ pop S' κ i ∧ pop S' κ i < 2 ^ (c + 1) := by
  classical
  let cls : ι → ℕ := fun i => Nat.log 2 (pop S κ i)
  let t : Finset ℕ := Finset.range (Nat.log 2 S.card + 1)
  have hmaps : ∀ i ∈ S, cls i ∈ t := by
    intro i _
    simp only [t, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right (pop_le S κ i))
  have ht : t.Nonempty := ⟨0, by simp [t]⟩
  have htcard : (t.card : ℝ) = (Nat.log 2 S.card : ℝ) + 1 := by
    simp [t]
  have htpos : (0 : ℝ) < t.card := by rw [htcard]; positivity
  obtain ⟨c, -, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps ht
    (b := (S.card : ℝ) / t.card) (by
      rw [nsmul_eq_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ htpos.ne'])
  set S' := S.filter (fun i => cls i = c) with hS'def
  -- whole cells are kept
  have hwhole : ∀ i ∈ S', ∀ j ∈ S, κ j = κ i → j ∈ S' := by
    intro i hi j hj hji
    have hpop : pop S κ j = pop S κ i := by
      unfold pop; rw [hji]
    refine Finset.mem_filter.2 ⟨hj, ?_⟩
    have := (Finset.mem_filter.1 hi).2
    simp only [cls] at this ⊢
    rw [hpop]; exact this
  -- populations in `S'` equal populations in `S`
  have hpopeq : ∀ i ∈ S', pop S' κ i = pop S κ i := by
    intro i hi
    unfold pop
    congr 1
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hj, hji⟩; exact ⟨(Finset.mem_filter.1 hj).1, hji⟩
    · rintro ⟨hj, hji⟩; exact ⟨hwhole i hi j hj hji, hji⟩
  refine ⟨S', Finset.filter_subset _ _, ?_, ?_, hwhole, c, fun i hi => ?_⟩
  · -- nonempty: the chosen class has at least `|S|/(log + 1) > 0` points
    rw [← Finset.card_pos]
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.2 hS
    have : (0 : ℝ) < (S.card : ℝ) / t.card := div_pos hSpos htpos
    exact_mod_cast lt_of_lt_of_le this hc
  · rw [htcard] at hc
    rw [div_le_iff₀ (by positivity)] at hc
    linarith
  · rw [hpopeq i hi]
    have hcls : Nat.log 2 (pop S κ i) = c := (Finset.mem_filter.1 hi).2
    have hpos := pop_pos (κ := κ) (Finset.mem_filter.1 hi).1
    constructor
    · rw [← hcls]; exact Nat.pow_log_le_self 2 hpos.ne'
    · rw [← hcls]; exact Nat.lt_pow_succ_log_self (by norm_num) _

/-- Keeping whole cells of a coarser level keeps the populations of the finer cells. -/
lemma pop_eq_of_whole {ι α : Type*} [DecidableEq α] {S S' : Finset ι} (hS' : S' ⊆ S)
    (κ : ι → α) (hwhole : ∀ i ∈ S', ∀ j ∈ S, κ j = κ i → j ∈ S') {i : ι} (hi : i ∈ S') :
    pop S' κ i = pop S κ i := by
  unfold pop
  congr 1
  ext j
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hj, hji⟩; exact ⟨hS' hj, hji⟩
  · rintro ⟨hj, hji⟩; exact ⟨hwhole i hi j hj hji, hji⟩

/-- All levels: process the levels `0, 1, …, N-1` (fine to coarse). Nesting: equal cells at
level `j` are equal at every level `k ≥ j`. The result has, at every level, populations within a
factor `2`. -/
theorem dyadic_regularize {ι α : Type*} [DecidableEq ι] [DecidableEq α] (N : ℕ)
    (κ : ℕ → ι → α) (hnest : ∀ j k, j ≤ k → ∀ i i', κ j i = κ j i' → κ k i = κ k i')
    (S : Finset ι) (hS : S.Nonempty) :
    ∃ S' ⊆ S, S'.Nonempty ∧ (S.card : ℝ) ≤ ((Nat.log 2 S.card : ℝ) + 1) ^ N * S'.card ∧
      ∀ k < N, ∃ c : ℕ, ∀ i ∈ S', 2 ^ c ≤ pop S' (κ k) i ∧ pop S' (κ k) i < 2 ^ (c + 1) := by
  induction N with
  | zero =>
    exact ⟨S, subset_rfl, hS, by simp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨S₁, hS₁S, hS₁ne, hS₁card, hbal⟩ := ih
    obtain ⟨S₂, hS₂S₁, hS₂ne, hS₂card, hwhole, c, hc⟩ := dyadic_class_refine S₁ hS₁ne (κ N)
    refine ⟨S₂, hS₂S₁.trans hS₁S, hS₂ne, ?_, fun k hk => ?_⟩
    · have hlog : (Nat.log 2 S₁.card : ℝ) ≤ Nat.log 2 S.card := by
        exact_mod_cast Nat.log_mono_right (Finset.card_le_card hS₁S)
      have h0 : (0 : ℝ) ≤ Nat.log 2 S₁.card := Nat.cast_nonneg _
      calc (S.card : ℝ) ≤ ((Nat.log 2 S.card : ℝ) + 1) ^ N * S₁.card := hS₁card
        _ ≤ ((Nat.log 2 S.card : ℝ) + 1) ^ N * (((Nat.log 2 S₁.card : ℝ) + 1) * S₂.card) := by
            gcongr
        _ ≤ ((Nat.log 2 S.card : ℝ) + 1) ^ N * (((Nat.log 2 S.card : ℝ) + 1) * S₂.card) := by
            gcongr
        _ = ((Nat.log 2 S.card : ℝ) + 1) ^ (N + 1) * S₂.card := by ring
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · -- a finer level: whole level-`N` cells are whole level-`k` cells
        obtain ⟨c', hc'⟩ := hbal k hk'
        refine ⟨c', fun i hi => ?_⟩
        have hwk : ∀ i ∈ S₂, ∀ j ∈ S₁, κ k j = κ k i → j ∈ S₂ := fun i hi j hj hji =>
          hwhole i hi j hj (hnest k N hk'.le j i hji)
        rw [pop_eq_of_whole hS₂S₁ (κ k) hwk hi]
        exact hc' i (hS₂S₁ hi)
      · exact ⟨c, hc⟩

/-- The fibre of the cell of `i` at level `κ` inside `S`. -/
def fibre {ι α : Type*} [DecidableEq α] (S : Finset ι) (κ : ι → α) (i : ι) : Finset ι :=
  S.filter (fun j => κ j = κ i)

/-- Keeping whole cells of a coarser level keeps the fibres of the finer levels. -/
lemma fibre_eq_of_whole {ι α : Type*} [DecidableEq α] {S S' : Finset ι} (hS' : S' ⊆ S)
    (κ : ι → α) (hwhole : ∀ i ∈ S', ∀ j ∈ S, κ j = κ i → j ∈ S') {i : ι} (hi : i ∈ S') :
    fibre S' κ i = fibre S κ i := by
  unfold fibre
  ext j
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hj, hji⟩; exact ⟨hS' hj, hji⟩
  · rintro ⟨hj, hji⟩; exact ⟨hwhole i hi j hj hji, hji⟩

/-- A fine-to-coarse pass that removes bad cells. `good k F` is a property of a fibre `F` at
level `k`. At each level `k < N`, either the members of bad cells make up at least half of the
current set (returned: level `k`, the current set and its bad part), or they are removed. At the
end every cell at every level is good, and at least `2^(-N)` of the set is kept. -/
theorem good_pass {ι α : Type*} [DecidableEq ι] [DecidableEq α] (N : ℕ)
    (κ : ℕ → ι → α) (hnest : ∀ j k, j ≤ k → ∀ i i', κ j i = κ j i' → κ k i = κ k i')
    (good : ℕ → Finset ι → Prop) (S : Finset ι) :
    (∃ k < N, ∃ S' ⊆ S, ∃ B ⊆ S', S'.card ≤ 2 * B.card ∧ (S.card : ℝ) ≤ 2 ^ N * S'.card ∧
        ∀ i ∈ B, ¬ good k (fibre S' (κ k) i)) ∨
      (∃ S' ⊆ S, (S.card : ℝ) ≤ 2 ^ N * S'.card ∧
        ∀ k < N, ∀ i ∈ S', good k (fibre S' (κ k) i)) := by
  classical
  induction N with
  | zero =>
    right
    exact ⟨S, subset_rfl, by simp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ N ih =>
    rcases ih with ⟨k, hk, S', hS'S, B, hBS', hB, hcard, hbad⟩ | ⟨S₁, hS₁S, hcard₁, hgood₁⟩
    · left
      refine ⟨k, by omega, S', hS'S, B, hBS', hB, ?_, hbad⟩
      calc (S.card : ℝ) ≤ 2 ^ N * S'.card := hcard
        _ ≤ 2 ^ (N + 1) * S'.card := by
            gcongr
            · norm_num
            · omega
    · -- level `N`: the bad members of `S₁`
      set B := S₁.filter (fun i => ¬ good N (fibre S₁ (κ N) i)) with hBdef
      by_cases hhalf : S₁.card ≤ 2 * B.card
      · left
        refine ⟨N, by omega, S₁, hS₁S, B, Finset.filter_subset _ _, hhalf, ?_, fun i hi => ?_⟩
        · calc (S.card : ℝ) ≤ 2 ^ N * S₁.card := hcard₁
            _ ≤ 2 ^ (N + 1) * S₁.card := by
                gcongr
                · norm_num
                · omega
        · exact (Finset.mem_filter.1 hi).2
      · right
        push Not at hhalf
        set S₂ := S₁.filter (fun i => good N (fibre S₁ (κ N) i)) with hS₂def
        have hsplit : S₁.card = S₂.card + B.card := by
          rw [hS₂def, hBdef]
          exact (Finset.card_filter_add_card_filter_not _).symm
        -- whole level-`N` cells are kept
        have hwholeN : ∀ i ∈ S₂, ∀ j ∈ S₁, κ N j = κ N i → j ∈ S₂ := by
          intro i hi j hj hji
          refine Finset.mem_filter.2 ⟨hj, ?_⟩
          have : fibre S₁ (κ N) j = fibre S₁ (κ N) i := by
            unfold fibre; rw [hji]
          rw [this]
          exact (Finset.mem_filter.1 hi).2
        refine ⟨S₂, (Finset.filter_subset _ _).trans hS₁S, ?_, fun k hk i hi => ?_⟩
        · have h2 : (S₁.card : ℝ) ≤ 2 * S₂.card := by
            have : S₁.card ≤ 2 * S₂.card := by omega
            exact_mod_cast this
          calc (S.card : ℝ) ≤ 2 ^ N * S₁.card := hcard₁
            _ ≤ 2 ^ N * (2 * S₂.card) := by gcongr
            _ = 2 ^ (N + 1) * S₂.card := by ring
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
          · have hwk : ∀ i ∈ S₂, ∀ j ∈ S₁, κ k j = κ k i → j ∈ S₂ := fun i hi j hj hji =>
              hwholeN i hi j hj (hnest k N hk'.le j i hji)
            rw [fibre_eq_of_whole (Finset.filter_subset _ _) (κ k) hwk hi]
            exact hgood₁ k hk' i ((Finset.filter_subset _ _) hi)
          · rw [fibre_eq_of_whole (Finset.filter_subset _ _) (κ k) hwholeN hi]
            exact (Finset.mem_filter.1 hi).2

/-- The members of `S` whose cell has population below `t` are at most `#cells · t`. -/
lemma card_small_cells_le {ι α : Type*} [DecidableEq ι] [DecidableEq α] (S : Finset ι)
    (κ : ι → α) (t : ℕ) :
    (S.filter (fun i => pop S κ i < t)).card ≤ (S.image κ).card * t := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := κ) (t := S.image κ)
    (fun i hi => Finset.mem_image_of_mem κ (Finset.mem_filter.1 hi).1)]
  calc ∑ c ∈ S.image κ, ((S.filter (fun i => pop S κ i < t)).filter (fun i => κ i = c)).card
      ≤ ∑ _c ∈ S.image κ, t := by
        apply Finset.sum_le_sum
        intro c hc
        obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hc
        by_cases hsmall : pop S κ i₀ < t
        · -- all members of the cell, fewer than `t`
          calc ((S.filter (fun i => pop S κ i < t)).filter (fun i => κ i = κ i₀)).card
              ≤ (S.filter (fun i => κ i = κ i₀)).card := by
                apply Finset.card_le_card
                intro i hi
                simp only [Finset.mem_filter] at hi ⊢
                exact ⟨hi.1.1, hi.2⟩
            _ ≤ t := hsmall.le
        · -- no member of the cell is small
          have : (S.filter (fun i => pop S κ i < t)).filter (fun i => κ i = κ i₀) = ∅ := by
            ext i
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            rintro ⟨hiS, hsm⟩ hci
            have hpop : pop S κ i = pop S κ i₀ := by unfold pop; rw [hci]
            rw [hpop] at hsm
            exact hsmall hsm
          rw [this, Finset.card_empty]
          exact Nat.zero_le _
    _ = (S.image κ).card * t := by rw [Finset.sum_const, smul_eq_mul]

/-- Cleanup, fine to coarse: remove the cells whose population is below the threshold `t k`.
Every surviving cell at every level `k < N` has population at least `t k`, and the removed
members number at most `Σ_k #cells_k(S) · t k`. -/
theorem threshold_prune {ι α : Type*} [DecidableEq ι] [DecidableEq α] (N : ℕ)
    (κ : ℕ → ι → α) (hnest : ∀ j k, j ≤ k → ∀ i i', κ j i = κ j i' → κ k i = κ k i')
    (t : ℕ → ℕ) (S : Finset ι) :
    ∃ S' ⊆ S, (∀ k < N, ∀ i ∈ S', t k ≤ pop S' (κ k) i) ∧
      S.card ≤ S'.card + ∑ k ∈ Finset.range N, (S.image (κ k)).card * t k := by
  classical
  induction N with
  | zero => exact ⟨S, subset_rfl, fun k hk => absurd hk (Nat.not_lt_zero _), by simp⟩
  | succ N ih =>
    obtain ⟨S₁, hS₁S, hS₁, hcard₁⟩ := ih
    set S₂ := S₁.filter (fun i => t N ≤ pop S₁ (κ N) i) with hS₂def
    have hwholeN : ∀ i ∈ S₂, ∀ j ∈ S₁, κ N j = κ N i → j ∈ S₂ := by
      intro i hi j hj hji
      refine Finset.mem_filter.2 ⟨hj, ?_⟩
      have : pop S₁ (κ N) j = pop S₁ (κ N) i := by unfold pop; rw [hji]
      rw [this]
      exact (Finset.mem_filter.1 hi).2
    have hS₂S₁ : S₂ ⊆ S₁ := Finset.filter_subset _ _
    refine ⟨S₂, hS₂S₁.trans hS₁S, fun k hk i hi => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · have hwk : ∀ i ∈ S₂, ∀ j ∈ S₁, κ k j = κ k i → j ∈ S₂ := fun i hi j hj hji =>
          hwholeN i hi j hj (hnest k N hk'.le j i hji)
        rw [pop_eq_of_whole hS₂S₁ (κ k) hwk hi]
        exact hS₁ k hk' i (hS₂S₁ hi)
      · rw [pop_eq_of_whole hS₂S₁ (κ k) hwholeN hi]
        exact (Finset.mem_filter.1 hi).2
    · have hsplit : S₁.card = S₂.card + (S₁.filter (fun i => ¬ t N ≤ pop S₁ (κ N) i)).card :=
        (Finset.card_filter_add_card_filter_not _).symm
      have hsmall : (S₁.filter (fun i => ¬ t N ≤ pop S₁ (κ N) i)).card ≤
          (S₁.image (κ N)).card * t N := by
        have := card_small_cells_le S₁ (κ N) (t N)
        simpa only [not_le] using this
      have himg : (S₁.image (κ N)).card ≤ (S.image (κ N)).card :=
        Finset.card_le_card (Finset.image_subset_image hS₁S)
      rw [Finset.sum_range_succ]
      have : (S₁.image (κ N)).card * t N ≤ (S.image (κ N)).card * t N :=
        Nat.mul_le_mul_right _ himg
      omega

open Classical in
/-- One level of per-cell refinements. `flat F` marks the fibres without a good refinement;
`sub F` is the chosen refinement of a non-flat fibre (`sub F ⊆ F`, `|F| ≤ L |sub F|`). Either the
members of flat cells make up at least half of `S`, or the union `S'` of the refinements keeps
`|S| ≤ 2 L |S'|`, and inside each cell `S'` is exactly the chosen refinement. -/
theorem cell_refine {ι α : Type*} [DecidableEq ι] [DecidableEq α] (S : Finset ι) (κ : ι → α)
    (L : ℝ) (hL : 1 ≤ L) (flat : Finset ι → Prop) (sub : Finset ι → Finset ι)
    (hsub : ∀ F, ¬ flat F → sub F ⊆ F ∧ (F.card : ℝ) ≤ L * (sub F).card) :
    (S.card ≤ 2 * (S.filter (fun i => flat (fibre S κ i))).card) ∨
    ∃ S' ⊆ S, (S.card : ℝ) ≤ 2 * L * S'.card ∧
      ∀ i ∈ S', ¬ flat (fibre S κ i) ∧ fibre S' κ i = sub (fibre S κ i) := by
  classical
  by_cases hhalf : S.card ≤ 2 * (S.filter (fun i => flat (fibre S κ i))).card
  · exact Or.inl hhalf
  right
  push Not at hhalf
  set G := S.filter (fun i => ¬ flat (fibre S κ i)) with hGdef
  set S' := G.filter (fun i => i ∈ sub (fibre S κ i)) with hS'def
  -- the fibre of `i` in `S` is the fibre of any of its members
  have hfib : ∀ i j, κ j = κ i → fibre S κ j = fibre S κ i := by
    intro i j h; unfold fibre; rw [h]
  have hsplit : S.card = G.card + (S.filter (fun i => flat (fibre S κ i))).card := by
    rw [hGdef, add_comm]
    exact (Finset.card_filter_add_card_filter_not _).symm.trans (by rw [add_comm])
  have hGbig : S.card < 2 * G.card := by omega
  -- inside a non-flat cell, `S'` is the refinement
  have hcell : ∀ i ∈ S', fibre S' κ i = sub (fibre S κ i) := by
    intro i hi
    have hiG : i ∈ G := (Finset.mem_filter.1 hi).1
    have hnf : ¬ flat (fibre S κ i) := (Finset.mem_filter.1 hiG).2
    obtain ⟨hsubF, -⟩ := hsub _ hnf
    ext j
    constructor
    · intro hj
      obtain ⟨hjS', hji⟩ := Finset.mem_filter.1 hj
      have := (Finset.mem_filter.1 hjS').2
      rwa [hfib i j hji] at this
    · intro hj
      have hjF := hsubF hj
      obtain ⟨hjS, hji⟩ := Finset.mem_filter.1 hjF
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hjS, ?_⟩, ?_⟩, hji⟩
      · rw [hfib i j hji]; exact hnf
      · rw [hfib i j hji]; exact hj
  refine ⟨S', (Finset.filter_subset _ _).trans (Finset.filter_subset _ _), ?_, fun i hi =>
    ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).2, hcell i hi⟩⟩
  -- counting cell by cell: `|G ∩ cell| ≤ L |S' ∩ cell|`
  have hcount : (G.card : ℝ) ≤ L * S'.card := by
    have hG : (G.card : ℝ) = ∑ c ∈ G.image κ, ((G.filter (fun i => κ i = c)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := κ) (t := G.image κ)
        (fun i hi => Finset.mem_image_of_mem κ hi)]
      push_cast; rfl
    have hS' : (S'.card : ℝ) = ∑ c ∈ G.image κ, ((S'.filter (fun i => κ i = c)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := κ) (t := G.image κ)
        (fun i hi => Finset.mem_image_of_mem κ (Finset.mem_filter.1 hi).1)]
      push_cast; rfl
    rw [hG, hS', Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hc
    have hnf : ¬ flat (fibre S κ i₀) := (Finset.mem_filter.1 hi₀).2
    obtain ⟨hsubF, hcardF⟩ := hsub _ hnf
    -- `G ∩ cell = fibre S κ i₀` and `S' ∩ cell = sub (fibre S κ i₀)`
    have h1 : G.filter (fun i => κ i = κ i₀) = fibre S κ i₀ := by
      ext j
      constructor
      · intro hj
        obtain ⟨hjG, hji⟩ := Finset.mem_filter.1 hj
        exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hjG).1, hji⟩
      · intro hj
        obtain ⟨hjS, hji⟩ := Finset.mem_filter.1 hj
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hjS, ?_⟩, hji⟩
        rw [hfib i₀ j hji]; exact hnf
    have h2 : S'.filter (fun i => κ i = κ i₀) = sub (fibre S κ i₀) := by
      ext j
      constructor
      · intro hj
        obtain ⟨hjS', hji⟩ := Finset.mem_filter.1 hj
        have := (Finset.mem_filter.1 hjS').2
        rwa [hfib i₀ j hji] at this
      · intro hj
        have hjF := hsubF hj
        obtain ⟨hjS, hji⟩ := Finset.mem_filter.1 hjF
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hjS, ?_⟩, ?_⟩, hji⟩
        · rw [hfib i₀ j hji]; exact hnf
        · rw [hfib i₀ j hji]; exact hj
    rw [h1, h2]
    exact hcardF
  have hGr : (S.card : ℝ) < 2 * G.card := by exact_mod_cast hGbig
  have hL0 : (0 : ℝ) ≤ L := by linarith
  calc (S.card : ℝ) ≤ 2 * G.card := hGr.le
    _ ≤ 2 * (L * S'.card) := by linarith
    _ = 2 * L * S'.card := by ring

open Classical in
/-- Per-cell refinements at all levels. At each level `k < N`, `flat k F` marks fibres without a
good refinement and `sub k F` is the chosen refinement of a non-flat fibre. Either at some level
the flat cells make up at least half of the current set `S'` (returned, with
`|S| ≤ (2L)^N |S'|`), or a set `S'` with `|S| ≤ (2L)^N |S'|` has, at every level, its fibres
inside the chosen refinement of a non-flat fibre. -/
theorem iterate_refine {ι α : Type*} [DecidableEq ι] [DecidableEq α] (N : ℕ) (κ : ℕ → ι → α)
    (L : ℝ) (hL : 1 ≤ L) (flat : ℕ → Finset ι → Prop) (sub : ℕ → Finset ι → Finset ι)
    (hsub : ∀ k F, ¬ flat k F → sub k F ⊆ F ∧ (F.card : ℝ) ≤ L * (sub k F).card)
    (S : Finset ι) :
    (∃ k < N, ∃ S' ⊆ S, (S.card : ℝ) ≤ (2 * L) ^ N * S'.card ∧
        S'.card ≤ 2 * (S'.filter (fun i => flat k (fibre S' (κ k) i))).card) ∨
      (∃ S' ⊆ S, (S.card : ℝ) ≤ (2 * L) ^ N * S'.card ∧
        ∀ k < N, ∀ i ∈ S', ∃ F : Finset ι, ¬ flat k F ∧ fibre S' (κ k) i ⊆ sub k F) := by
  have h2L : (1 : ℝ) ≤ 2 * L := by linarith
  induction N with
  | zero =>
    right
    exact ⟨S, subset_rfl, by simp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ N ih =>
    rcases ih with ⟨k, hk, S', hS'S, hcard, hhalf⟩ | ⟨S₁, hS₁S, hcard₁, hgood₁⟩
    · left
      refine ⟨k, by omega, S', hS'S, ?_, hhalf⟩
      calc (S.card : ℝ) ≤ (2 * L) ^ N * S'.card := hcard
        _ ≤ (2 * L) ^ (N + 1) * S'.card := by
            gcongr
            omega
    · rcases cell_refine S₁ (κ N) L hL (flat N) (sub N) (hsub N) with hhalf | ⟨S₂, hS₂S₁, hcard₂, hS₂⟩
      · left
        refine ⟨N, by omega, S₁, hS₁S, ?_, hhalf⟩
        calc (S.card : ℝ) ≤ (2 * L) ^ N * S₁.card := hcard₁
          _ ≤ (2 * L) ^ (N + 1) * S₁.card := by
              gcongr
              omega
      · right
        refine ⟨S₂, hS₂S₁.trans hS₁S, ?_, fun k hk i hi => ?_⟩
        · calc (S.card : ℝ) ≤ (2 * L) ^ N * S₁.card := hcard₁
            _ ≤ (2 * L) ^ N * (2 * L * S₂.card) := by
                gcongr
            _ = (2 * L) ^ (N + 1) * S₂.card := by ring
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
          · obtain ⟨F, hF, hsubF⟩ := hgood₁ k hk' i (hS₂S₁ hi)
            refine ⟨F, hF, fun j hj => hsubF ?_⟩
            obtain ⟨hjS₂, hji⟩ := Finset.mem_filter.1 hj
            exact Finset.mem_filter.2 ⟨hS₂S₁ hjS₂, hji⟩
          · obtain ⟨hnf, hfib⟩ := hS₂ i hi
            exact ⟨fibre S₁ (κ k) i, hnf, by rw [hfib]⟩

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
