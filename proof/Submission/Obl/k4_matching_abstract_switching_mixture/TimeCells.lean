import Mathlib

/- Adapted from this LOT tree, o015, session x0051, Submission/Lib/K4TimeCells.lean
   (branch x0051, 2026-10-21; own code of that session, no outside code). The namespace is
   changed and lemmas on arbitrary measurable time sets and normalized cells are added. -/

/-!
# Dyadic time cells for a law on index pairs and times

For a law `μ` on `(Fin n₁ × Fin n₂) × ℝ` concentrated on times in `[0, 1)`, the
weights `cellWeight μ G ω = μ(atom ω)` of the atoms "index pair `(ω.1, ω.2.1)` and
time in the dyadic cell `[c / 2^G, (c + 1) / 2^G)`" form a probability weight on the
finite type `Fin n₁ × Fin n₂ × Fin (2 ^ G)`.  Each atom of positive weight meets
any conull set `S`, which gives representatives `cellRep`.  Per-index time
marginals `μ{i, E} ≤ B π_i |E|` become `∑ cellWeight ≤ B π_i |E|` over the cells inside
`E`, and the dyadic interval of a time at any coarser level `H ≤ G` is determined by its
cell.  `normCell` is the image of a cell in the normalized time `(t - centre) * 2^H` of a
level-`H` interval.
-/

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open MeasureTheory Finset

variable {n₁ n₂ : ℕ}

/-- The dyadic cell `[c / 2^G, (c + 1) / 2^G)`. -/
def cellSet (G c : ℕ) : Set ℝ := Set.Ico ((c : ℝ) / 2 ^ G) (((c : ℝ) + 1) / 2 ^ G)

lemma mem_cellSet_iff {G c : ℕ} {t : ℝ} : t ∈ cellSet G c ↔ ⌊t * 2 ^ G⌋ = (c : ℤ) := by
  have h2 : (0 : ℝ) < 2 ^ G := by positivity
  rw [cellSet, Set.mem_Ico, Int.floor_eq_iff, div_le_iff₀ h2, lt_div_iff₀ h2]
  push_cast
  rfl

/-- At a coarser level `H ≤ G` the dyadic interval index is determined by the cell. -/
lemma floor_mul_pow_of_mem_cellSet {G c : ℕ} {t : ℝ} (ht : t ∈ cellSet G c) {H : ℕ}
    (hH : H ≤ G) : ⌊t * 2 ^ H⌋ = ((c / 2 ^ (G - H) : ℕ) : ℤ) := by
  rw [mem_cellSet_iff] at ht
  have : t * 2 ^ H = t * 2 ^ G / ((2 ^ (G - H) : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ^ G = 2 ^ H * 2 ^ (G - H) := by
      rw [← pow_add, Nat.add_sub_cancel' hH]
    push_cast
    rw [h2]
    field_simp
  rw [this, Int.floor_div_natCast, ht]
  push_cast
  rfl

/-- Two times in the same cell lie in the same dyadic interval of every coarser level. -/
lemma floor_eq_of_floor_eq {G H : ℕ} (hH : H ≤ G) {s t : ℝ}
    (h : ⌊s * 2 ^ G⌋ = ⌊t * 2 ^ G⌋) : ⌊s * 2 ^ H⌋ = ⌊t * 2 ^ H⌋ := by
  have h2 : (2 : ℝ) ^ G = 2 ^ H * 2 ^ (G - H) := by rw [← pow_add, Nat.add_sub_cancel' hH]
  have e : ∀ x : ℝ, x * 2 ^ H = x * 2 ^ G / ((2 ^ (G - H) : ℕ) : ℝ) := by
    intro x; push_cast; rw [h2]; field_simp
  rw [e s, e t, Int.floor_div_natCast, Int.floor_div_natCast, h]

/-- The atom of an index pair and a time cell. -/
def atomSet (G : ℕ) (ω : Fin n₁ × Fin n₂ × Fin (2 ^ G)) : Set ((Fin n₁ × Fin n₂) × ℝ) :=
  {p | p.1 = (ω.1, ω.2.1) ∧ p.2 ∈ cellSet G ω.2.2}

lemma measurableSet_cellSet (G c : ℕ) : MeasurableSet (cellSet G c) := measurableSet_Ico

lemma volume_cellSet (G c : ℕ) : volume (cellSet G c) = ENNReal.ofReal (1 / 2 ^ G) := by
  rw [cellSet, Real.volume_Ico]; congr 1; ring

lemma measurableSet_atomSet (G : ℕ) (ω : Fin n₁ × Fin n₂ × Fin (2 ^ G)) :
    MeasurableSet (atomSet G ω) := by
  have : atomSet G ω = ({(ω.1, ω.2.1)} : Set (Fin n₁ × Fin n₂)) ×ˢ cellSet G ω.2.2 := by
    ext p; simp [atomSet]
  rw [this]
  exact (measurableSet_singleton _).prod (measurableSet_cellSet G _)

lemma cellSet_disjoint (G : ℕ) {c c' : ℕ} (hne : c ≠ c') :
    Disjoint (cellSet G c) (cellSet G c') := by
  rw [Set.disjoint_left]
  intro t h h'
  rw [mem_cellSet_iff] at h h'
  exact hne (by exact_mod_cast h.symm.trans h')

lemma atomSet_disjoint (G : ℕ) {ω ω' : Fin n₁ × Fin n₂ × Fin (2 ^ G)} (hne : ω ≠ ω') :
    Disjoint (atomSet G ω) (atomSet G ω') := by
  rw [Set.disjoint_left]
  rintro p ⟨h1, h2⟩ ⟨h1', h2'⟩
  rw [mem_cellSet_iff] at h2 h2'
  apply hne
  have e1 : (ω.1, ω.2.1) = (ω'.1, ω'.2.1) := h1.symm.trans h1'
  have e2 : (ω.2.2 : ℕ) = ω'.2.2 := by exact_mod_cast h2.symm.trans h2'
  rcases ω with ⟨a, b, c⟩
  rcases ω' with ⟨a', b', c'⟩
  simp only [Prod.mk.injEq] at e1
  simp only [e1.1, e1.2, Prod.mk.injEq, true_and]
  exact Fin.ext e2

/-- The atoms cover exactly the times in `[0, 1)`. -/
lemma iUnion_atomSet (G : ℕ) :
    (⋃ ω ∈ (univ : Finset (Fin n₁ × Fin n₂ × Fin (2 ^ G))), atomSet G ω)
      = {p : (Fin n₁ × Fin n₂) × ℝ | p.2 ∈ Set.Ico (0 : ℝ) 1} := by
  ext p
  simp only [mem_univ, Set.iUnion_true, Set.mem_iUnion, Set.mem_ofPred_eq, atomSet]
  constructor
  · rintro ⟨ω, -, hc⟩
    rw [cellSet, Set.mem_Ico] at hc
    have h2 : (0 : ℝ) < 2 ^ G := by positivity
    have hc' : (ω.2.2 : ℝ) + 1 ≤ 2 ^ G := by exact_mod_cast ω.2.2.isLt
    refine ⟨le_trans (div_nonneg (Nat.cast_nonneg _) h2.le) hc.1, lt_of_lt_of_le hc.2 ?_⟩
    rw [div_le_one h2]; exact hc'
  · rintro ⟨h0, h1⟩
    have h2 : (0 : ℝ) < 2 ^ G := by positivity
    set c := ⌊p.2 * 2 ^ G⌋₊ with hc
    have hlt : c < 2 ^ G := by
      rw [hc, Nat.floor_lt (mul_nonneg h0 h2.le)]
      push_cast
      calc p.2 * 2 ^ G < 1 * 2 ^ G := mul_lt_mul_of_pos_right h1 h2
        _ = 2 ^ G := one_mul _
    refine ⟨(p.1.1, p.1.2, ⟨c, hlt⟩), rfl, ?_⟩
    rw [mem_cellSet_iff]
    simp only
    rw [hc, Int.natCast_floor_eq_floor (mul_nonneg h0 h2.le)]

/-- The weight of an atom. -/
noncomputable def cellWeight (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) (G : ℕ)
    (ω : Fin n₁ × Fin n₂ × Fin (2 ^ G)) : ℝ :=
  (μ (atomSet G ω)).toReal

lemma cellWeight_nonneg (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) (G : ℕ) (ω) :
    0 ≤ cellWeight μ G ω := ENNReal.toReal_nonneg

lemma sum_measure_atomSet (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) (G : ℕ) :
    ∑ ω, μ (atomSet G ω) = μ {p | p.2 ∈ Set.Ico (0 : ℝ) 1} := by
  rw [← iUnion_atomSet G, measure_biUnion_finset]
  · intro ω _ ω' _ hne; exact atomSet_disjoint G hne
  · intro ω _; exact measurableSet_atomSet G ω

/-- A law concentrated on a set `S` of times in `[0, 1)` gives a probability weight. -/
lemma sum_cellWeight (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) [IsProbabilityMeasure μ] (G : ℕ)
    {S : Set ((Fin n₁ × Fin n₂) × ℝ)} (hS : μ Sᶜ = 0) (hSt : ∀ p ∈ S, p.2 ∈ Set.Ico (0 : ℝ) 1) :
    ∑ ω, cellWeight μ G ω = 1 := by
  unfold cellWeight
  rw [← ENNReal.toReal_sum (fun ω _ => measure_ne_top μ _), sum_measure_atomSet]
  have h1 : μ {p : (Fin n₁ × Fin n₂) × ℝ | p.2 ∈ Set.Ico (0 : ℝ) 1} = 1 := by
    apply le_antisymm prob_le_one
    calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
      _ = μ S := by
          rw [← measure_inter_conull (s := Set.univ) hS, Set.univ_inter]
      _ ≤ _ := measure_mono fun p hp => hSt p hp
  rw [h1, ENNReal.toReal_one]

/-- An atom of positive weight meets every conull set. -/
lemma nonempty_atomSet_inter {μ : Measure ((Fin n₁ × Fin n₂) × ℝ)} {G : ℕ}
    {S : Set ((Fin n₁ × Fin n₂) × ℝ)} (hS : μ Sᶜ = 0) {ω : Fin n₁ × Fin n₂ × Fin (2 ^ G)}
    (hω : 0 < cellWeight μ G ω) : (atomSet G ω ∩ S).Nonempty := by
  apply nonempty_of_measure_ne_zero (μ := μ)
  rw [measure_inter_conull hS]
  intro h0
  rw [cellWeight, h0, ENNReal.toReal_zero] at hω
  exact lt_irrefl 0 hω

open Classical in
/-- A representative event of a cell: a point of `S` in its atom when the atom has positive
weight, and the base point `x₀` otherwise. -/
noncomputable def cellRep (G : ℕ) (S : Set ((Fin n₁ × Fin n₂) × ℝ)) (x₀ : (Fin n₁ × Fin n₂) × ℝ)
    (ω : Fin n₁ × Fin n₂ × Fin (2 ^ G)) : (Fin n₁ × Fin n₂) × ℝ :=
  if h : (atomSet G ω ∩ S).Nonempty then h.some else x₀

lemma cellRep_mem {G : ℕ} {S : Set ((Fin n₁ × Fin n₂) × ℝ)} {x₀ : (Fin n₁ × Fin n₂) × ℝ}
    (hx₀ : x₀ ∈ S) (ω : Fin n₁ × Fin n₂ × Fin (2 ^ G)) : cellRep G S x₀ ω ∈ S := by
  unfold cellRep
  split_ifs with h
  · exact h.some_mem.2
  · exact hx₀

lemma cellRep_mem_atomSet {μ : Measure ((Fin n₁ × Fin n₂) × ℝ)} {G : ℕ}
    {S : Set ((Fin n₁ × Fin n₂) × ℝ)} (hS : μ Sᶜ = 0) (x₀ : (Fin n₁ × Fin n₂) × ℝ)
    {ω : Fin n₁ × Fin n₂ × Fin (2 ^ G)} (hω : 0 < cellWeight μ G ω) :
    cellRep G S x₀ ω ∈ atomSet G ω := by
  unfold cellRep
  rw [dif_pos (nonempty_atomSet_inter hS hω)]
  exact (nonempty_atomSet_inter hS hω).some_mem.1

/-- The atoms of a fixed first index and of cells inside a measurable time set `E` have total
mass at most `μ{p.1.1 = i, p.2 ∈ E}`. -/
lemma sum_measure_atomSet_fst_le (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) (G : ℕ)
    (s : Finset (Fin n₁ × Fin n₂ × Fin (2 ^ G))) (i : Fin n₁) {E : Set ℝ}
    (hs : ∀ ω ∈ s, ω.1 = i ∧ cellSet G ω.2.2 ⊆ E) :
    ∑ ω ∈ s, μ (atomSet G ω) ≤ μ {p | p.1.1 = i ∧ p.2 ∈ E} := by
  rw [← measure_biUnion_finset (fun ω _ ω' _ hne => atomSet_disjoint G hne)
    (fun ω _ => measurableSet_atomSet G ω)]
  refine measure_mono (Set.iUnion₂_subset fun ω hω p hp => ?_)
  obtain ⟨h1, h2⟩ := hs ω hω
  refine ⟨?_, h2 hp.2⟩
  rw [hp.1, ← h1]

/-- The atoms of a fixed second index and of cells inside a measurable time set `E` have
total mass at most `μ{p.1.2 = i, p.2 ∈ E}`. -/
lemma sum_measure_atomSet_snd_le (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) (G : ℕ)
    (s : Finset (Fin n₁ × Fin n₂ × Fin (2 ^ G))) (i : Fin n₂) {E : Set ℝ}
    (hs : ∀ ω ∈ s, ω.2.1 = i ∧ cellSet G ω.2.2 ⊆ E) :
    ∑ ω ∈ s, μ (atomSet G ω) ≤ μ {p | p.1.2 = i ∧ p.2 ∈ E} := by
  rw [← measure_biUnion_finset (fun ω _ ω' _ hne => atomSet_disjoint G hne)
    (fun ω _ => measurableSet_atomSet G ω)]
  refine measure_mono (Set.iUnion₂_subset fun ω hω p hp => ?_)
  obtain ⟨h1, h2⟩ := hs ω hω
  refine ⟨?_, h2 hp.2⟩
  rw [hp.1, ← h1]

/-- Per-index time marginals bound the weights of the cells of one first index inside a
measurable time set of finite volume. -/
lemma sum_cellWeight_fst_le_of_subset (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) [IsFiniteMeasure μ]
    (G : ℕ) {B : ℝ} {π₁ : Fin n₁ → ℝ} (hB : 0 ≤ B) (hπ : ∀ i, 0 ≤ π₁ i)
    (hm : ∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E →
      μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₁ i) * volume E)
    (s : Finset (Fin n₁ × Fin n₂ × Fin (2 ^ G))) (i : Fin n₁) {E : Set ℝ}
    (hE : MeasurableSet E) (hEf : volume E ≠ ⊤)
    (hs : ∀ ω ∈ s, ω.1 = i ∧ cellSet G ω.2.2 ⊆ E) :
    ∑ ω ∈ s, cellWeight μ G ω ≤ B * π₁ i * (volume E).toReal := by
  unfold cellWeight
  rw [← ENNReal.toReal_sum (fun ω _ => measure_ne_top μ _)]
  have h := (sum_measure_atomSet_fst_le μ G s i hs).trans (hm i E hE)
  have hne : ENNReal.ofReal (B * π₁ i) * volume E ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEf
  calc (∑ ω ∈ s, μ (atomSet G ω)).toReal
      ≤ (ENNReal.ofReal (B * π₁ i) * volume E).toReal := ENNReal.toReal_mono hne h
    _ = B * π₁ i * (volume E).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hB (hπ i))]

/-- Per-index time marginals bound the weights of the cells of one second index inside a
measurable time set of finite volume. -/
lemma sum_cellWeight_snd_le_of_subset (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) [IsFiniteMeasure μ]
    (G : ℕ) {B : ℝ} {π₂ : Fin n₂ → ℝ} (hB : 0 ≤ B) (hπ : ∀ i, 0 ≤ π₂ i)
    (hm : ∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E →
      μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₂ i) * volume E)
    (s : Finset (Fin n₁ × Fin n₂ × Fin (2 ^ G))) (i : Fin n₂) {E : Set ℝ}
    (hE : MeasurableSet E) (hEf : volume E ≠ ⊤)
    (hs : ∀ ω ∈ s, ω.2.1 = i ∧ cellSet G ω.2.2 ⊆ E) :
    ∑ ω ∈ s, cellWeight μ G ω ≤ B * π₂ i * (volume E).toReal := by
  unfold cellWeight
  rw [← ENNReal.toReal_sum (fun ω _ => measure_ne_top μ _)]
  have h := (sum_measure_atomSet_snd_le μ G s i hs).trans (hm i E hE)
  have hne : ENNReal.ofReal (B * π₂ i) * volume E ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hEf
  calc (∑ ω ∈ s, μ (atomSet G ω)).toReal
      ≤ (ENNReal.ofReal (B * π₂ i) * volume E).toReal := ENNReal.toReal_mono hne h
    _ = B * π₂ i * (volume E).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hB (hπ i))]

/-- Per-index time marginals become per-cell bounds (first index). -/
lemma sum_cellWeight_fst_le (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) [IsFiniteMeasure μ] (G : ℕ)
    {B : ℝ} {π₁ : Fin n₁ → ℝ} (hB : 0 ≤ B) (hπ : ∀ i, 0 ≤ π₁ i)
    (hm : ∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E →
      μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₁ i) * volume E)
    (i : Fin n₁) (c : Fin (2 ^ G)) :
    ∑ i₂ : Fin n₂, cellWeight μ G (i, i₂, c) ≤ B * π₁ i / 2 ^ G := by
  have h := sum_cellWeight_fst_le_of_subset μ G hB hπ hm
    ((univ : Finset (Fin n₂)).image fun i₂ => (i, i₂, c)) i (measurableSet_cellSet G c)
    (by rw [volume_cellSet]; exact ENNReal.ofReal_ne_top)
    (fun ω hω => by
      rw [mem_image] at hω
      obtain ⟨i₂, -, rfl⟩ := hω
      exact ⟨rfl, subset_rfl⟩)
  rw [sum_image (fun a _ b _ hab => by simpa using hab), volume_cellSet,
    ENNReal.toReal_ofReal (by positivity)] at h
  calc ∑ i₂ : Fin n₂, cellWeight μ G (i, i₂, c) ≤ B * π₁ i * (1 / 2 ^ G) := h
    _ = B * π₁ i / 2 ^ G := by ring

/-- Per-index time marginals become per-cell bounds (second index). -/
lemma sum_cellWeight_snd_le (μ : Measure ((Fin n₁ × Fin n₂) × ℝ)) [IsFiniteMeasure μ] (G : ℕ)
    {B : ℝ} {π₂ : Fin n₂ → ℝ} (hB : 0 ≤ B) (hπ : ∀ i, 0 ≤ π₂ i)
    (hm : ∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E →
      μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (B * π₂ i) * volume E)
    (i : Fin n₂) (c : Fin (2 ^ G)) :
    ∑ i₁ : Fin n₁, cellWeight μ G (i₁, i, c) ≤ B * π₂ i / 2 ^ G := by
  have h := sum_cellWeight_snd_le_of_subset μ G hB hπ hm
    ((univ : Finset (Fin n₁)).image fun i₁ => (i₁, i, c)) i (measurableSet_cellSet G c)
    (by rw [volume_cellSet]; exact ENNReal.ofReal_ne_top)
    (fun ω hω => by
      rw [mem_image] at hω
      obtain ⟨i₁, -, rfl⟩ := hω
      exact ⟨rfl, subset_rfl⟩)
  rw [sum_image (fun a _ b _ hab => by simpa using hab), volume_cellSet,
    ENNReal.toReal_ofReal (by positivity)] at h
  calc ∑ i₁ : Fin n₁, cellWeight μ G (i₁, i, c) ≤ B * π₂ i * (1 / 2 ^ G) := h
    _ = B * π₂ i / 2 ^ G := by ring

/-! ### Normalized cells -/

/-- The image of the cell `[c / 2^G, (c + 1) / 2^G)` under the normalized time
`t ↦ t * 2^H - k - 1/2` of the level-`H` interval of index `k`. -/
def normCell (H G : ℕ) (k : ℤ) (c : ℕ) : Set ℝ :=
  Set.Ico ((c : ℝ) / 2 ^ G * 2 ^ H - k - 1 / 2) (((c : ℝ) + 1) / 2 ^ G * 2 ^ H - k - 1 / 2)

lemma measurableSet_normCell (H G : ℕ) (k : ℤ) (c : ℕ) : MeasurableSet (normCell H G k c) :=
  measurableSet_Ico

lemma volume_normCell (H G : ℕ) (k : ℤ) (c : ℕ) :
    volume (normCell H G k c) = ENNReal.ofReal (2 ^ H / 2 ^ G) := by
  rw [normCell, Real.volume_Ico]; congr 1; ring

/-- The normalized time of a point of a cell lies in the normalized cell. -/
lemma mem_normCell_of_mem_cellSet {H G : ℕ} (k : ℤ) {c : ℕ} {t : ℝ} (ht : t ∈ cellSet G c) :
    t * 2 ^ H - k - 1 / 2 ∈ normCell H G k c := by
  have h2 : (0 : ℝ) < 2 ^ H := by positivity
  rw [cellSet, Set.mem_Ico] at ht
  rw [normCell, Set.mem_Ico]
  constructor
  · have := mul_le_mul_of_nonneg_right ht.1 h2.le
    linarith
  · have := mul_lt_mul_of_pos_right ht.2 h2
    linarith

/-- The normalized time `σ a e = (e.2 - ((⌊a.2 2^H⌋ + 1/2) / 2^H)) * 2^H` of the frozen
statement, written as in the normalized cells. -/
lemma sigma_eq (H : ℕ) (k : ℤ) (t : ℝ) :
    (t - (((k : ℝ) + 1 / 2) / (2 : ℝ) ^ H)) * (2 : ℝ) ^ H = t * 2 ^ H - k - 1 / 2 := by
  have h2 : (2 : ℝ) ^ H ≠ 0 := by positivity
  field_simp
  ring

/-- Two points of one normalized cell are within the cell width. -/
lemma abs_sub_le_of_mem_normCell {H G : ℕ} {k : ℤ} {c : ℕ} {x y : ℝ}
    (hx : x ∈ normCell H G k c) (hy : y ∈ normCell H G k c) : |x - y| ≤ 2 ^ H / 2 ^ G := by
  rw [normCell, Set.mem_Ico] at hx hy
  have e : ((c : ℝ) + 1) / 2 ^ G * 2 ^ H - k - 1 / 2 - ((c : ℝ) / 2 ^ G * 2 ^ H - k - 1 / 2)
      = 2 ^ H / 2 ^ G := by ring
  rw [abs_le]
  constructor <;> linarith

/-- Distinct normalized cells are disjoint. -/
lemma normCell_disjoint (H G : ℕ) (k : ℤ) {c c' : ℕ} (hne : c ≠ c') :
    Disjoint (normCell H G k c) (normCell H G k c') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  -- recover the cell from the normalized time
  have h2 : (0 : ℝ) < 2 ^ H := by positivity
  set t := (x + k + 1 / 2) / 2 ^ H with ht
  have hx_eq : x = t * 2 ^ H - k - 1 / 2 := by rw [ht]; field_simp; ring
  have mem : ∀ {c'' : ℕ}, x ∈ normCell H G k c'' → t ∈ cellSet G c'' := by
    intro c'' h
    rw [normCell, Set.mem_Ico, hx_eq] at h
    rw [cellSet, Set.mem_Ico]
    constructor
    · have := h.1
      have h' : (c'' : ℝ) / 2 ^ G * 2 ^ H ≤ t * 2 ^ H := by linarith
      exact le_of_mul_le_mul_right h' h2
    · have := h.2
      have h' : t * 2 ^ H < ((c'' : ℝ) + 1) / 2 ^ G * 2 ^ H := by linarith
      exact lt_of_mul_lt_mul_right h' h2.le
  exact Set.disjoint_left.mp (cellSet_disjoint G hne) (mem hx) (mem hx')

/-- A cell inside the level-`H` interval of index `k` has its normalized cell inside
`[-1/2, 1/2]`. -/
lemma normCell_subset_Icc {H G : ℕ} (hHG : H ≤ G) {k : ℤ} {c : ℕ}
    (hc : ((c / 2 ^ (G - H) : ℕ) : ℤ) = k) :
    normCell H G k c ⊆ Set.Icc (-(1 / 2)) (1 / 2) := by
  intro x hx
  have h2 : (0 : ℝ) < 2 ^ H := by positivity
  have hG : (2 : ℝ) ^ G = 2 ^ H * 2 ^ (G - H) := by rw [← pow_add, Nat.add_sub_cancel' hHG]
  have hD : (0 : ℕ) < 2 ^ (G - H) := by positivity
  -- `c = k 2^(G-H) + r` with `0 ≤ r < 2^(G-H)`
  have hdiv := Nat.div_add_mod c (2 ^ (G - H))
  have hmod := Nat.mod_lt c hD
  set D := 2 ^ (G - H) with hDdef
  set q := c / D with hq
  set r := c % D with hr
  have hk : (k : ℝ) = (q : ℝ) := by rw [← hc]; push_cast; rfl
  have hcR : (c : ℝ) = (D : ℝ) * q + r := by exact_mod_cast hdiv.symm
  have hDR : (D : ℝ) = 2 ^ (G - H) := by rw [hDdef]; push_cast; rfl
  have hrlt : (r : ℝ) + 1 ≤ D := by exact_mod_cast hmod
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have e1 : (c : ℝ) / 2 ^ G * 2 ^ H - k - 1 / 2 = r / D - 1 / 2 := by
    rw [hG, hcR, hk, ← hDR]; field_simp; ring
  have e2 : ((c : ℝ) + 1) / 2 ^ G * 2 ^ H - k - 1 / 2 = (r + 1) / D - 1 / 2 := by
    rw [hG, hcR, hk, ← hDR]; field_simp; ring
  rw [normCell, Set.mem_Ico, e1, e2] at hx
  have h0 : 0 ≤ (r : ℝ) / D := div_nonneg (Nat.cast_nonneg _) hDpos.le
  have h1 : ((r : ℝ) + 1) / D ≤ 1 := by rw [div_le_one hDpos]; exact hrlt
  constructor <;> linarith [hx.1, hx.2]

end Submission.Obl.k4_matching_abstract_switching_mixture
