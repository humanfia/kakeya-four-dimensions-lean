-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.Dyadic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.DyadicShading
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.MassSelection

/-!
# Two-fold dyadic pigeonhole (the shape of o162)

For measurable sets `Z i` in any measure space, a finset `S` and an assignment
`f : Fin n → Fin N`:

1. *Common fibre multiplicity.*  Separate the fibres by working in `Fin N × α` with
   the measure `∑_k μ ∘ (k, ·)⁻¹`; o095's `dyadic_shading_refinement` then gives one
   dyadic class `[2^k, 2^(k+1))` of fibre multiplicities keeping a `1/(log₂ n + 1)`
   share of the mass.
2. *Common fibre size.*  One dyadic class of fibre cardinalities keeps another
   `1/(log₂ n + 1)` share (o052's `weighted_level_selection`); the kept fibres are
   reindexed by an injection.
-/

set_option linter.unusedVariables false

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open MeasureTheory Set
open scoped ENNReal

section Dyadic

open scoped Classical

variable {α : Type*} [MeasurableSpace α]

/-- The measure on `Fin N × α` putting a copy of `μ` on every fibre. -/
def fibreMeasure (μ : Measure α) (N : ℕ) : Measure (Fin N × α) :=
  Measure.sum fun k : Fin N => μ.map (fun p => (k, p))

lemma fibreMeasure_apply (μ : Measure α) {N : ℕ} {A : Set (Fin N × α)} (hA : MeasurableSet A) :
    fibreMeasure μ N A = ∑ k : Fin N, μ ((fun p => (k, p)) ⁻¹' A) := by
  rw [fibreMeasure, Measure.sum_apply _ hA, tsum_fintype]
  exact Finset.sum_congr rfl fun k _ => Measure.map_apply measurable_prodMk_left hA

/-- Mass of a set inside one fibre. -/
lemma fibreMeasure_single (μ : Measure α) {N : ℕ} (k₀ : Fin N) {A : Set (Fin N × α)}
    (hA : MeasurableSet A) (hAk : A ⊆ {k₀} ×ˢ univ) :
    fibreMeasure μ N A = μ ((fun p => (k₀, p)) ⁻¹' A) := by
  classical
  rw [fibreMeasure_apply μ hA, Finset.sum_eq_single k₀]
  · intro k _ hk
    have : (fun p => (k, p)) ⁻¹' A = ∅ := by
      ext p
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hp
      have := (hAk hp).1
      simp only [mem_singleton_iff] at this
      exact hk this
    rw [this, measure_empty]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- **Common dyadic fibre multiplicity.** -/
theorem fibre_dyadic_level (μ : Measure α) {n N : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set α) (hZ : ∀ i, MeasurableSet (Z i)) :
    ∃ (k : ℕ) (Z₁ : Fin n → Set α),
      (∀ i, MeasurableSet (Z₁ i) ∧ Z₁ i ⊆ Z i ∧ (i ∉ S → Z₁ i = ∅)) ∧
      ∑ i ∈ S, μ (Z i) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ≥0∞) * ∑ i, μ (Z₁ i) ∧
      ∀ (j : Fin N) (p : α), (∃ i, f i = j ∧ p ∈ Z₁ i) →
        2 ^ k ≤ (Finset.univ.filter fun i => f i = j ∧ p ∈ Z₁ i).card ∧
        (Finset.univ.filter fun i => f i = j ∧ p ∈ Z₁ i).card < 2 ^ (k + 1) := by
  classical
  let Y' : Fin n → Set (Fin N × α) := fun i => if i ∈ S then {f i} ×ˢ Z i else ∅
  have hY' : ∀ i, MeasurableSet (Y' i) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [Y', if_pos hi]
      exact (measurableSet_singleton _).prod (hZ i)
    · simp only [Y', if_neg hi]
      exact MeasurableSet.empty
  have hY'sub : ∀ i, Y' i ⊆ {f i} ×ˢ univ := by
    intro i q hq
    by_cases hi : i ∈ S
    · simp only [Y', if_pos hi] at hq
      exact ⟨hq.1, mem_univ _⟩
    · simp only [Y', if_neg hi] at hq
      exact hq.elim
  obtain ⟨k, Z', -, hZ', hmass, hlevel⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.dyadic_shading_refinement
      (fibreMeasure μ N) Y' hY'
  let Z₁ : Fin n → Set α := fun i => (fun p => (f i, p)) ⁻¹' Z' i
  have hZ'sub : ∀ i, Z' i ⊆ {f i} ×ˢ univ := fun i => (hZ' i).2.trans (hY'sub i)
  have hZ₁m : ∀ i, MeasurableSet (Z₁ i) := fun i => measurable_prodMk_left (hZ' i).1
  have hmassY : ∀ i, fibreMeasure μ N (Y' i) = if i ∈ S then μ (Z i) else 0 := by
    intro i
    by_cases hi : i ∈ S
    · rw [fibreMeasure_single μ (f i) (hY' i) (hY'sub i), if_pos hi]
      congr 1
      ext p
      simp [Y', hi]
    · simp only [Y', if_neg hi, measure_empty]
  have hmassZ : ∀ i, fibreMeasure μ N (Z' i) = μ (Z₁ i) := fun i =>
    fibreMeasure_single μ (f i) (hZ' i).1 (hZ'sub i)
  refine ⟨k, Z₁, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hZ₁m i, ?_, ?_⟩
    · intro p hp
      have h1 := (hZ' i).2 hp
      by_cases hi : i ∈ S
      · simp only [Y', if_pos hi] at h1
        exact h1.2
      · simp only [Y', if_neg hi] at h1
        exact h1.elim
    · intro hi
      ext p
      simp only [Z₁, mem_preimage, mem_empty_iff_false, iff_false]
      intro hp
      have h1 := (hZ' i).2 hp
      simp only [Y', if_neg hi] at h1
      exact h1
  · have h1 : ∑ i ∈ S, μ (Z i) = ∑ i, fibreMeasure μ N (Y' i) := by
      simp_rw [hmassY]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have h2 : ∑ i, fibreMeasure μ N (Z' i) = ∑ i, μ (Z₁ i) :=
      Finset.sum_congr rfl fun i _ => hmassZ i
    rw [h1, ← h2]
    simpa [Fintype.card_fin] using hmass
  · intro j p hp
    obtain ⟨i, hij, hpi⟩ := hp
    have hmem : (j, p) ∈ ⋃ i, Z' i := mem_iUnion.mpr ⟨i, by rw [← hij]; exact hpi⟩
    have hset : (Finset.univ.filter fun i => (j, p) ∈ Z' i) =
        Finset.univ.filter fun i => f i = j ∧ p ∈ Z₁ i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Z₁, mem_preimage]
      constructor
      · intro h
        have := (hZ'sub i h).1
        simp only [mem_singleton_iff] at this
        exact ⟨this.symm, by rw [← this]; exact h⟩
      · rintro ⟨h1, h2⟩
        rw [← h1]
        exact h2
    rw [← hset]
    exact hlevel (j, p) hmem

/-- **Two-fold dyadic pigeonhole** (the shape of o162). -/
theorem two_fold_dyadic (μ : Measure α) (n N : ℕ) (S : Finset (Fin n)) (f : Fin n → Fin N)
    (Z : Fin n → Set α) (hZ : ∀ i, MeasurableSet (Z i)) :
    ∃ (N' : ℕ) (ψ : Fin N' → Fin N) (f' : Fin n → Fin N') (S' : Finset (Fin n))
      (Z' : Fin n → Set α) (m : ℝ), Function.Injective ψ ∧
      (∀ k i, i ∈ S' ∧ f' i = k ↔ i ∈ S ∧ f i = ψ k) ∧
      (∀ i, MeasurableSet (Z' i) ∧ Z' i ⊆ Z i ∧ (i ∉ S' → Z' i = ∅)) ∧
      (∀ k k', (Set.ncard {i | i ∈ S' ∧ f' i = k} : ℝ) ≤
        2 * (Set.ncard {i | i ∈ S' ∧ f' i = k'} : ℝ)) ∧
      (∀ k p, (∃ i ∈ S', f' i = k ∧ p ∈ Z' i) →
        (Set.ncard {i | i ∈ S' ∧ f' i = k ∧ p ∈ Z' i} : ℝ) ∈ Set.Icc m (2 * m)) ∧
      ∑ i ∈ S, μ (Z i) ≤ (((Nat.log 2 n + 1) ^ 2 : ℕ) : ℝ≥0∞) * ∑ i ∈ S', μ (Z' i) := by
  obtain ⟨k₁, Z₁, hZ₁, hmass1, hlev1⟩ := fibre_dyadic_level μ S f Z hZ
  set L := Nat.log 2 n with hL
  have hZ₁S : ∑ i, μ (Z₁ i) = ∑ i ∈ S, μ (Z₁ i) := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => by
      rw [(hZ₁ i).2.2 hi, measure_empty])]
  -- the empty family
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨N, id, f, ∅, fun _ => ∅, 0, Function.injective_id, ?_, ?_, ?_, ?_, ?_⟩
    · intro k i
      simp [hS]
    · intro i
      exact ⟨MeasurableSet.empty, empty_subset _, fun _ => rfl⟩
    · intro k k'
      simp
    · rintro k p ⟨i, hi, -⟩
      simp at hi
    · simp [hS]
  -- the fibre sizes
  let F : Fin N → ℕ := fun k => (S.filter (fun i => f i = k)).card
  let FF : Finset (Fin N) := Finset.univ.filter (fun k => 0 < F k)
  let w : Fin N → ℝ≥0∞ := fun k => ∑ i ∈ S.filter (fun i => f i = k), μ (Z₁ i)
  have hFle : ∀ k, F k ≤ n := fun k =>
    ((Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_le_univ S)).trans
      (by simp)
  have hP : ∀ k ∈ FF, ∃ j, j ≤ L ∧ Nat.log 2 (F k) = j :=
    fun k _ => ⟨Nat.log 2 (F k), Nat.log_mono_right (hFle k), rfl⟩
  obtain ⟨j₀, -, G, hGFF, hGlev, hGmass⟩ :=
    WangZahlLot.Obl.wz_normalized_projection_coarse_fine.weighted_level_selection FF w L
      (fun k j => Nat.log 2 (F k) = j) hP
  have hsumFF : ∑ k ∈ FF, w k = ∑ i ∈ S, μ (Z₁ i) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.univ) (g := f)
      (fun i _ => Finset.mem_univ _)]
    rw [← Finset.sum_subset (Finset.subset_univ FF) (fun k _ hk => by
      have hF0 : F k = 0 := by
        by_contra h
        exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero h⟩)
      have : S.filter (fun i => f i = k) = ∅ := Finset.card_eq_zero.mp hF0
      simp only [w, this, Finset.sum_empty])]
  have hmass2 : ∑ i ∈ S, μ (Z i) ≤ ((L + 1 : ℕ) : ℝ≥0∞) * ((L + 1 : ℝ≥0∞) * ∑ k ∈ G, w k) := by
    calc ∑ i ∈ S, μ (Z i) ≤ ((L + 1 : ℕ) : ℝ≥0∞) * ∑ i, μ (Z₁ i) := hmass1
      _ = ((L + 1 : ℕ) : ℝ≥0∞) * ∑ k ∈ FF, w k := by rw [hZ₁S, hsumFF]
      _ ≤ _ := mul_le_mul' le_rfl hGmass
  rcases G.eq_empty_or_nonempty with hG | hG
  · -- no mass at all: keep one whole fibre with empty shadings
    obtain ⟨i₀, hi₀⟩ := hS
    have hzero : ∑ i ∈ S, μ (Z i) = 0 := by
      have := hmass2
      rw [hG, Finset.sum_empty, mul_zero, mul_zero] at this
      exact le_antisymm this zero_le
    refine ⟨1, fun _ => f i₀, fun _ => 0, S.filter (fun i => f i = f i₀), fun _ => ∅, 0,
      fun a b _ => Subsingleton.elim a b, ?_, ?_, ?_, ?_, ?_⟩
    · intro k i
      have hk : k = 0 := Subsingleton.elim _ _
      subst hk
      simp [Finset.mem_filter]
    · intro i
      exact ⟨MeasurableSet.empty, empty_subset _, fun _ => rfl⟩
    · intro k k'
      rw [Subsingleton.elim k k']
      have : (0 : ℝ) ≤ (Set.ncard {i | i ∈ S.filter (fun i => f i = f i₀) ∧ (0 : Fin 1) = k'} : ℝ) :=
        Nat.cast_nonneg _
      linarith
    · rintro k p ⟨i, -, -, hp⟩
      exact hp.elim
    · rw [hzero]
      exact zero_le
  -- the kept fibres, reindexed
  have hGcard : 0 < G.card := Finset.card_pos.mpr hG
  let ψ : Fin G.card → Fin N := fun k' => (G.equivFin.symm k').1
  have hψG : ∀ k', ψ k' ∈ G := fun k' => (G.equivFin.symm k').2
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact G.equivFin.symm.injective (Subtype.ext hab)
  let f' : Fin n → Fin G.card := fun i =>
    if h : f i ∈ G then G.equivFin ⟨f i, h⟩ else ⟨0, hGcard⟩
  have hψf' : ∀ i, f i ∈ G → ψ (f' i) = f i := by
    intro i hi
    simp [ψ, f', hi]
  have hf'eq : ∀ i (hi : f i ∈ G) (k : Fin G.card), f' i = k ↔ f i = ψ k := by
    intro i hi k
    constructor
    · rintro rfl
      exact (hψf' i hi).symm
    · intro h
      apply hψinj
      rw [hψf' i hi, h]
  let S' : Finset (Fin n) := S.filter (fun i => f i ∈ G)
  let Z' : Fin n → Set α := fun i => if f i ∈ G then Z₁ i else ∅
  have hiff : ∀ k i, i ∈ S' ∧ f' i = k ↔ i ∈ S ∧ f i = ψ k := by
    intro k i
    simp only [S', Finset.mem_filter]
    constructor
    · rintro ⟨⟨hiS, hiG⟩, hik⟩
      exact ⟨hiS, (hf'eq i hiG k).mp hik⟩
    · rintro ⟨hiS, hik⟩
      have hiG : f i ∈ G := hik ▸ hψG k
      exact ⟨⟨hiS, hiG⟩, (hf'eq i hiG k).mpr hik⟩
  refine ⟨G.card, ψ, f', S', Z', 2 ^ k₁, hψinj, hiff, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hiG : f i ∈ G
    · simp only [Z', if_pos hiG]
      refine ⟨(hZ₁ i).1, (hZ₁ i).2.1, fun hi => (hZ₁ i).2.2 ?_⟩
      intro hiS
      exact hi (Finset.mem_filter.mpr ⟨hiS, hiG⟩)
    · simp only [Z', if_neg hiG]
      exact ⟨MeasurableSet.empty, empty_subset _, fun _ => by simp⟩
  · -- balanced fibres
    have hfib : ∀ k, (Set.ncard {i | i ∈ S' ∧ f' i = k} : ℝ) = F (ψ k) := by
      intro k
      have hset : {i | i ∈ S' ∧ f' i = k} = ↑(S.filter (fun i => f i = ψ k)) := by
        ext i
        simp only [mem_setOf_eq, Finset.coe_filter]
        exact hiff k i
      rw [hset, Set.ncard_coe_finset]
    have hrange : ∀ k, 2 ^ j₀ ≤ F (ψ k) ∧ F (ψ k) < 2 ^ (j₀ + 1) := by
      intro k
      have hk := hGlev (ψ k) (hψG k)
      have hpos : 0 < F (ψ k) := (Finset.mem_filter.mp (hGFF (hψG k))).2
      rw [← hk]
      exact ⟨Nat.pow_log_le_self 2 hpos.ne', Nat.lt_pow_succ_log_self (by norm_num) _⟩
    intro k k'
    rw [hfib, hfib]
    have h1 := (hrange k).2
    have h2 := (hrange k').1
    have h3 : (F (ψ k) : ℝ) < 2 ^ (j₀ + 1) := by exact_mod_cast h1
    have h4 : ((2 : ℝ) ^ j₀) ≤ F (ψ k') := by exact_mod_cast h2
    rw [pow_succ] at h3
    linarith
  · -- uniform multiplicity
    rintro k p ⟨i, hiS', hik, hpi⟩
    have hiG : f i ∈ G := (Finset.mem_filter.mp hiS').2
    have hset : {i | i ∈ S' ∧ f' i = k ∧ p ∈ Z' i} =
        ↑(Finset.univ.filter fun i => f i = ψ k ∧ p ∈ Z₁ i) := by
      ext j
      simp only [mem_setOf_eq, Finset.coe_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hjS', hjk, hpj⟩
        have hjG : f j ∈ G := (Finset.mem_filter.mp hjS').2
        refine ⟨(hf'eq j hjG k).mp hjk, ?_⟩
        simpa only [Z', if_pos hjG] using hpj
      · rintro ⟨hjk, hpj⟩
        have hjG : f j ∈ G := hjk ▸ hψG k
        have hjS : j ∈ S := by
          by_contra h
          rw [(hZ₁ j).2.2 h] at hpj
          exact hpj
        refine ⟨Finset.mem_filter.mpr ⟨hjS, hjG⟩, (hf'eq j hjG k).mpr hjk, ?_⟩
        simpa only [Z', if_pos hjG] using hpj
    rw [hset, Set.ncard_coe_finset]
    have hpZ₁ : p ∈ Z₁ i := by simpa only [Z', if_pos hiG] using hpi
    have hlev := hlev1 (ψ k) p ⟨i, by rw [← hik]; exact (hψf' i hiG).symm, hpZ₁⟩
    constructor
    · exact_mod_cast hlev.1
    · have : ((Finset.univ.filter fun i => f i = ψ k ∧ p ∈ Z₁ i).card : ℝ) < 2 ^ (k₁ + 1) := by
        exact_mod_cast hlev.2
      rw [pow_succ] at this
      linarith
  · -- the mass
    have hsumG : ∑ k ∈ G, w k = ∑ i ∈ S', μ (Z' i) := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := S') (t := G) (g := f)
        (fun i hi => (Finset.mem_filter.mp hi).2)]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr
      · ext i
        simp only [S', Finset.mem_filter]
        constructor
        · rintro ⟨hiS, hik⟩
          exact ⟨⟨hiS, hik ▸ hk⟩, hik⟩
        · rintro ⟨⟨hiS, -⟩, hik⟩
          exact ⟨hiS, hik⟩
      · intro i hi
        have hiG : f i ∈ G := (Finset.mem_filter.mp hi).2 ▸ hk
        simp only [Z', if_pos hiG]
    rw [← hsumG]
    calc ∑ i ∈ S, μ (Z i) ≤ ((L + 1 : ℕ) : ℝ≥0∞) * ((L + 1 : ℝ≥0∞) * ∑ k ∈ G, w k) := hmass2
      _ = (((L + 1) ^ 2 : ℕ) : ℝ≥0∞) * ∑ k ∈ G, w k := by
          push_cast
          ring

end Dyadic

end WangZahlLot.Obl.wz_broad_grains_improvement
