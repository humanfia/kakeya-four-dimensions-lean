/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/RowReadyOf.lean.
   Earlier provenance comments in the source are retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.RowField
import Submission.Obl.k4_narrow_projected_row_parents.SmallGeometry

/-!
# Listed parents are row-ready

Construction of the row field of deep labels for a listed parent, the pruning
of (deep label, horizontal cell) states against their full assignments, the
witness velocity bins and the row-option counts.  See `RowField.lean`.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers Submission.Obl.k4_general_parent_projected_layers.PreparedModel Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open PreparedModel
open Submission.Lib.K4ReferencePruning

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Deep labels inside the parent, and containing an incidence. -/
def deepGood (a : PreparedModel α) (k : ℕ) (r r' : ℝ) (Q : Fin (a.n k r))
    (n : Fin (a.n k r')) : Prop :=
  a.A k r' n ⊆ a.A k r Q ∧ a.block k r' n ⊆ a.block k r Q

open Classical in
/-- The predicate selecting a deep label for an incidence (the last index means none). -/
def selP (a : PreparedModel α) (k : ℕ) (r r' : ℝ) (Q : Fin (a.n k r)) (z : α × ℝ) (m : ℕ) :
    Prop :=
  (∃ h : m < a.n k r', deepGood a k r r' Q ⟨m, h⟩ ∧ z.1 ∈ a.B k r' ⟨m, h⟩ ∧
    z.2 ∈ a.block k r' ⟨m, h⟩) ∨ m = a.n k r'

theorem selP_exists (a : PreparedModel α) (k : ℕ) (r r' : ℝ) (Q : Fin (a.n k r))
    (z : α × ℝ) : ∃ m, selP a k r r' Q z m := ⟨a.n k r', Or.inr rfl⟩

open Classical in
/-- The selected deep label of an incidence. -/
def dsel (a : PreparedModel α) (k : ℕ) (r r' : ℝ) (Q : Fin (a.n k r)) (z : α × ℝ) : ℕ :=
  Nat.find (selP_exists a k r r' Q z)

theorem dsel_le (a : PreparedModel α) (k : ℕ) (r r' : ℝ) (Q : Fin (a.n k r)) (z : α × ℝ) :
    dsel a k r r' Q z ≤ a.n k r' := by
  classical
  exact Nat.find_min' _ (Or.inr rfl)

theorem dsel_spec (a : PreparedModel α) (k : ℕ) (r r' : ℝ) (Q : Fin (a.n k r)) (z : α × ℝ)
    (h : dsel a k r r' Q z < a.n k r') :
    deepGood a k r r' Q ⟨_, h⟩ ∧ z.1 ∈ a.B k r' ⟨_, h⟩ ∧ z.2 ∈ a.block k r' ⟨_, h⟩ := by
  classical
  have hs := Nat.find_spec (selP_exists a k r r' Q z)
  rcases hs with ⟨h', hgood⟩ | heq
  · exact hgood
  · exact absurd heq (Nat.ne_of_lt h)

theorem dsel_lt_of (a : PreparedModel α) (k : ℕ) (r r' : ℝ) (Q : Fin (a.n k r)) (z : α × ℝ)
    (n : Fin (a.n k r')) (hn : deepGood a k r r' Q n) (h1 : z.1 ∈ a.B k r' n)
    (h2 : z.2 ∈ a.block k r' n) : dsel a k r r' Q z < a.n k r' := by
  classical
  exact lt_of_le_of_lt (Nat.find_min' _ (Or.inl ⟨n.2, hn, h1, h2⟩)) n.2

theorem measurable_dsel (a : PreparedModel α) (k : ℕ) (r r' : ℝ) (Q : Fin (a.n k r))
    (hBm : ∀ n, MeasurableSet (a.B k r' n)) :
    Measurable (dsel a k r r' Q) := by
  classical
  refine measurable_find (fun z => selP_exists a k r r' Q z) fun m => ?_
  by_cases hm : m < a.n k r'
  · by_cases hg : deepGood a k r r' Q ⟨m, hm⟩
    · have : {z : α × ℝ | selP a k r r' Q z m} =
          (a.B k r' ⟨m, hm⟩ ×ˢ a.block k r' ⟨m, hm⟩) ∪ (if m = a.n k r' then univ else ∅) := by
        ext z
        simp only [selP, mem_setOf_eq, mem_union, mem_prod]
        constructor
        · rintro (⟨h, hg', h1, h2⟩ | heq)
          · left; exact ⟨h1, h2⟩
          · right; simp [heq]
        · rintro (⟨h1, h2⟩ | h)
          · left; exact ⟨hm, hg, h1, h2⟩
          · right; split_ifs at h with heq
            · exact heq
            · exact h.elim
      rw [this]
      refine ((hBm _).prod ?_).union ?_
      · simp only [block]; rw [interval_eq]; exact measurableSet_Icc
      · split_ifs <;> simp
    · have : {z : α × ℝ | selP a k r r' Q z m} = ∅ := by
        ext z
        simp only [selP, mem_setOf_eq, mem_empty_iff_false, iff_false, not_or]
        refine ⟨fun ⟨h, hg', _⟩ => hg hg', fun heq => ?_⟩
        omega
      rw [this]; exact MeasurableSet.empty
  · have : {z : α × ℝ | selP a k r r' Q z m} = if m = a.n k r' then univ else ∅ := by
      ext z
      simp only [selP, mem_setOf_eq]
      constructor
      · rintro (⟨h, _⟩ | heq)
        · exact absurd h hm
        · simp [heq]
      · intro h
        right
        split_ifs at h with heq
        · exact heq
        · exact h.elim
    rw [this]; split_ifs <;> simp

/-- The nine cells adjacent to a cell. -/
def nbhd (c₀ : Fin 2 → ℤ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (c₀ i - 1) (c₀ i + 1)

theorem mem_nbhd {c₀ c : Fin 2 → ℤ} : c ∈ nbhd c₀ ↔ ∀ i, |c i - c₀ i| ≤ 1 := by
  simp only [nbhd, Fintype.mem_piFinset, Finset.mem_Icc]
  refine forall_congr' fun i => ?_
  rw [abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega

theorem card_nbhd (c₀ : Fin 2 → ℤ) : (nbhd c₀).card = 9 := by
  simp only [nbhd, Fintype.card_piFinset, Int.card_Icc, Fin.prod_univ_two]
  have h : ∀ x : ℤ, (x + 1 + 1 - (x - 1)).toNat = 3 := fun x => by omega
  rw [h, h]
  norm_num

/-- The cell of the zoomed corner of a deep label. -/
def cornerCell (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ) (Q : Fin (a.n k r))
    (r' ξ : ℝ) (n : Fin (a.n k r')) : Fin 2 → ℤ :=
  fun i => ⌊deepCorner p a k r Q r' n i / ξ⌋

open Classical in
/-- Reference weight of a (deep label, cell) state: the full deep assignment
times its block length, on the nine cells near its corner. -/
def stWeight (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ) (Q : Fin (a.n k r))
    (r' ξ : ℝ) (s : ℕ × (Fin 2 → ℤ)) : ℝ≥0∞ :=
  if h : s.1 < a.n k r' then
    if deepGood a k r r' Q ⟨s.1, h⟩ ∧ s.2 ∈ nbhd (cornerCell p a k r Q r' ξ ⟨s.1, h⟩) then
      ENNReal.ofReal (a.q k r') * a.nu k (a.A k r' ⟨s.1, h⟩)
    else 0
  else 0

theorem tsum_stWeight_le (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) (r' ξ : ℝ)
    (hAm : ∀ n, MeasurableSet (a.A k r' n))
    (hdisj : ∀ n n', n ≠ n' → a.j k r' n = a.j k r' n' →
      Disjoint (a.A k r' n) (a.A k r' n')) :
    ∑' s, stWeight p a k r Q r' ξ s ≤ 9 * (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r Q)) := by
  classical
  rw [ENNReal.tsum_prod']
  -- the inner sums
  have hinner : ∀ m : ℕ, ∑' c, stWeight p a k r Q r' ξ (m, c) =
      if h : m < a.n k r' then
        (if deepGood a k r r' Q ⟨m, h⟩ then
          9 * (ENNReal.ofReal (a.q k r') * a.nu k (a.A k r' ⟨m, h⟩)) else 0)
      else 0 := by
    intro m
    by_cases hm : m < a.n k r'
    · rw [dif_pos hm]
      by_cases hg : deepGood a k r r' Q ⟨m, hm⟩
      · rw [if_pos hg]
        rw [tsum_eq_sum (s := nbhd (cornerCell p a k r Q r' ξ ⟨m, hm⟩))]
        · rw [Finset.sum_congr rfl (fun c hc => show stWeight p a k r Q r' ξ (m, c) =
              ENNReal.ofReal (a.q k r') * a.nu k (a.A k r' ⟨m, hm⟩) by
            simp only [stWeight, dif_pos hm]; rw [if_pos ⟨hg, hc⟩])]
          rw [Finset.sum_const, card_nbhd, nsmul_eq_mul]; norm_num
        · intro c hc
          simp only [stWeight, dif_pos hm]
          rw [if_neg (fun h => hc h.2)]
      · rw [if_neg hg]
        apply ENNReal.tsum_eq_zero.mpr
        intro c
        simp only [stWeight, dif_pos hm]
        rw [if_neg (fun h => hg h.1)]
    · rw [dif_neg hm]
      apply ENNReal.tsum_eq_zero.mpr
      intro c
      simp only [stWeight, dif_neg hm]
  simp only [hinner]
  rw [tsum_eq_sum (s := Finset.range (a.n k r'))]
  · rw [Finset.sum_range (fun m => if h : m < a.n k r' then
        (if deepGood a k r r' Q ⟨m, h⟩ then
          9 * (ENNReal.ofReal (a.q k r') * a.nu k (a.A k r' ⟨m, h⟩)) else 0) else 0)]
    simp only [Fin.is_lt, dif_pos, Fin.eta]
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    gcongr
    exact sum_inside_prior_le a k r r' Q hAm hdisj _ fun n hn => (Finset.mem_filter.mp hn).2
  · intro m hm
    rw [Finset.mem_range] at hm
    rw [dif_neg hm]

/-- The size bound of the row-ready parent produced from a listed parent. -/
def rowReadyBound (M Kc K : ℝ) : ℝ :=
  2 * M + 3 * (2 * Kc) ^ 2 * (M + 1) +
    Kc ^ 2 * (12 * Kc ^ 2 * (4 + Kc + 3 * (2 * Kc) ^ 2 * (M + 1)) + 2) ^ 2 /
      ((1 / (18 * M * K)) ^ 2 / 2)

set_option maxHeartbeats 4000000 in
/-- **Listed parents are row-ready.** -/
theorem rowReady_of_parentLists (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (k : ℕ)
    {r r' ξ E₁ M Kc : ℝ} (PL : ParentLists p a k r ξ E₁ M)
    (hξ : 0 < ξ) (hξE : ξ ≤ E₁) (hE1 : E₁ ≤ 1) (hM1 : 1 ≤ M) (hKcM : M + 1 ≤ Kc)
    (hξKc : 4 * Kc * ξ ≤ 1)
    (hbm : Measurable (a.b k)) (hρμ : a.rho k ≤ a.mu k) (hμfin : IsFiniteMeasure (a.mu k))
    (hπp : IsProbabilityMeasure (a.pi k)) (hνp : IsProbabilityMeasure (a.nu k))
    (hAm : ∀ n, MeasurableSet (a.A k r' n)) (hBm : ∀ n, MeasurableSet (a.B k r' n))
    (hBA : ∀ n, a.B k r' n ⊆ a.A k r' n)
    (hdisj : ∀ n n', n ≠ n' → a.j k r' n = a.j k r' n' →
      Disjoint (a.A k r' n) (a.A k r' n'))
    (hc1 : ∀ n, |a.c k r' n 1| ≤ p.K k)
    (hplank : ∀ n, ∀ l ∈ a.A k r' n, ∀ t ∈ a.block k r' n,
      |(a.x k l t) 1 - a.c k r' n 0 - t * a.c k r' n 1| ≤ p.K k * a.q k r' ∧
      |a.b k l 4 - a.c k r' n 3 - a.c k r' n 4 * a.b k l 3| ≤ p.K k * narrow p k r')
    (hvel : ∀ n (v₀ : ℤ), a.mu k {z | z.1 ∈ a.B k r' n ∧ z.2 ∈ a.block k r' n ∧
        ⌊a.b k z.1 3 / ξ⌋ = v₀} ≤
      ENNReal.ofReal (p.K k * a.q k r') * a.nu k (a.A k r' n) * a.pi k {w | ⌊w / ξ⌋ = v₀})
    (hcover : a.rho k {z | z ∈ PL.W ∧ ¬ ∃ n, deepGood a k r r' PL.Q n ∧
      z.1 ∈ a.B k r' n ∧ z.2 ∈ a.block k r' n} = 0)
    (hsmall : 2 * p.K k * a.q k r' ≤ ξ * a.q k r) (hsmall' : a.q k r' ≤ ξ * a.q k r)
    (he₁ : p.K k * narrow p k r' / narrow p k r ≤ E₁)
    (hthin : ∀ x : ℝ, a.pi k (Icc (x - 2 / Kc) (x + 2 / Kc)) ≤
      ENNReal.ofReal (1 / (36 * M * p.K k))) :
    Nonempty (RowReady p a k r ξ E₁ (rowReadyBound M Kc (p.K k))) := by
  classical
  -- notation
  obtain ⟨Z, hZ⟩ : ∃ Z : Zoom, Z = parentZoom p a k r PL.Q := ⟨_, rfl⟩
  have hK1 : 1 ≤ p.K k := hp.2.2.1.1 k
  have hKpos : 0 < p.K k := by linarith
  have hq := q_pos a k r
  have hq' := q_pos a k r'
  have hρfin : IsFiniteMeasure (a.rho k) :=
    ⟨lt_of_le_of_lt (hρμ univ) (measure_lt_top _ _)⟩
  set n' := a.n k r' with hn'
  let D : α × ℝ → ℕ := dsel a k r r' PL.Q
  have hDm : Measurable D := measurable_dsel a k r r' PL.Q hBm
  let cell : α × ℝ → Fin 2 → ℤ := fun z => hcell (parentZoom p a k r PL.Q) ξ (a.b k z.1) z.2
  have hcellm : Measurable cell := by
    refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i
    · exact (((measurable_snd.sub_const _).div_const _).div_const ξ).floor
    · exact ((((measurable_coeff_comp (parentZoom p a k r PL.Q) hbm 0).comp measurable_fst).add
        (((measurable_snd.sub_const _).div_const _).mul
          (((measurable_pi_apply 3).comp hbm).comp measurable_fst))).div_const ξ).floor
  let vb : α × ℝ → ℤ := fun z => ⌊a.b k z.1 3 / ξ⌋
  have hvbm : Measurable vb := ((((measurable_pi_apply 3).comp hbm).comp measurable_fst).div_const
    ξ).floor
  let state : α × ℝ → ℕ × (Fin 2 → ℤ) := fun z => (D z, cell z)
  have hstm : Measurable state := hDm.prodMk hcellm
  -- the covered incidences
  let W₃ : Set (α × ℝ) := PL.W ∩ {z | D z < n'}
  have hW₃m : MeasurableSet W₃ :=
    PL.measurable_W.inter (measurableSet_lt hDm measurable_const)
  have hW₃ : a.rho k W₃ = a.rho k PL.W := by
    apply le_antisymm (measure_mono inter_subset_left)
    have hsub : PL.W ⊆ W₃ ∪ {z | z ∈ PL.W ∧ ¬ ∃ n, deepGood a k r r' PL.Q n ∧
        z.1 ∈ a.B k r' n ∧ z.2 ∈ a.block k r' n} := by
      intro z hz
      by_cases h : ∃ n, deepGood a k r r' PL.Q n ∧ z.1 ∈ a.B k r' n ∧ z.2 ∈ a.block k r' n
      · obtain ⟨n, hn, h1, h2⟩ := h
        left; exact ⟨hz, dsel_lt_of a k r r' PL.Q z n hn h1 h2⟩
      · right; exact ⟨hz, h⟩
    calc a.rho k PL.W ≤ a.rho k (W₃ ∪ _) := measure_mono hsub
      _ ≤ a.rho k W₃ + _ := measure_union_le _ _
      _ = a.rho k W₃ := by rw [hcover, add_zero]
  -- selected deep labels of covered incidences
  have hsel : ∀ z ∈ W₃, ∃ h : D z < n', deepGood a k r r' PL.Q ⟨D z, h⟩ ∧
      z.1 ∈ a.B k r' ⟨D z, h⟩ ∧ z.2 ∈ a.block k r' ⟨D z, h⟩ :=
    fun z hz => ⟨hz.2, dsel_spec a k r r' PL.Q z hz.2⟩
  -- the cell of a covered incidence is near the corner of its deep label
  have hnear : ∀ z ∈ W₃, ∀ h : D z < n',
      cell z ∈ nbhd (cornerCell p a k r PL.Q r' ξ ⟨D z, h⟩) := by
    intro z hz h
    obtain ⟨-, hB, hblk⟩ := dsel_spec a k r r' PL.Q z h
    rw [mem_nbhd]
    exact hcell_near_corner p a k r PL.Q r' ⟨D z, h⟩ hξ hsmall hsmall' (hc1 _) hblk
      (hplank _ z.1 (hBA _ hB) z.2 hblk).1
  -- the restricted law and the velocity bins law
  let ρW : Measure (α × ℝ) := (a.rho k).restrict W₃
  haveI : IsFiniteMeasure ρW := inferInstance
  let π' : Measure ℤ := (a.pi k).map fun w => ⌊w / ξ⌋
  have hfl : Measurable fun w : ℝ => ⌊w / ξ⌋ := (measurable_id.div_const ξ).floor
  have hπ'apply : ∀ A : Set ℤ, π' A = a.pi k {w | ⌊w / ξ⌋ ∈ A} := by
    intro A
    rw [Measure.map_apply hfl (Set.to_countable A).measurableSet]
    rfl
  -- the velocity cap of a state
  have hcap : ∀ s (A : Set ℤ), MeasurableSet A →
      ρW {z | state z = s ∧ vb z ∈ A} ≤
        ENNReal.ofReal (p.K k) * stWeight p a k r PL.Q r' ξ s * π' A := by
    intro s A hA
    by_cases hne : ∃ z ∈ W₃, state z = s
    · obtain ⟨z₀, hz₀, hs⟩ := hne
      obtain ⟨h₀, hg₀, -, -⟩ := hsel z₀ hz₀
      have hs1 : s.1 = D z₀ := by rw [← hs]
      have hs2 : s.2 = cell z₀ := by rw [← hs]
      have hw : stWeight p a k r PL.Q r' ξ s =
          ENNReal.ofReal (a.q k r') * a.nu k (a.A k r' ⟨D z₀, h₀⟩) := by
        obtain ⟨s1, s2⟩ := s
        simp only at hs1 hs2
        subst hs1 hs2
        rw [stWeight, dif_pos h₀, if_pos ⟨hg₀, hnear z₀ hz₀ h₀⟩]
      rw [hw]
      -- the state's incidences lie in its deep label
      have hsub : {z | state z = s ∧ vb z ∈ A} ∩ W₃ ⊆ ⋃ v₀ ∈ A,
          {z | z.1 ∈ a.B k r' ⟨D z₀, h₀⟩ ∧ z.2 ∈ a.block k r' ⟨D z₀, h₀⟩ ∧ vb z = v₀} := by
        rintro z ⟨⟨hzs, hzA⟩, hzW⟩
        have hD : D z = D z₀ := by
          have := congrArg Prod.fst hzs; rw [hs1.symm]; exact this
        obtain ⟨h, -, hB, hblk⟩ := hsel z hzW
        refine mem_iUnion₂.mpr ⟨vb z, hzA, ?_, ?_, rfl⟩
        · have e : (⟨D z, h⟩ : Fin n') = ⟨D z₀, h₀⟩ := Fin.ext hD
          rw [← e]; exact hB
        · have e : (⟨D z, h⟩ : Fin n') = ⟨D z₀, h₀⟩ := Fin.ext hD
          rw [← e]; exact hblk
      have hdisjv : (A : Set ℤ).PairwiseDisjoint fun v₀ =>
          {z : α × ℝ | z.1 ∈ a.B k r' ⟨D z₀, h₀⟩ ∧ z.2 ∈ a.block k r' ⟨D z₀, h₀⟩ ∧ vb z = v₀} := by
        intro v hv v' hv' hvv
        simp only [Function.onFun]
        rw [Set.disjoint_left]
        rintro z ⟨-, -, h1⟩ ⟨-, -, h2⟩
        exact hvv (h1.symm.trans h2)
      have hmeasv : ∀ v₀ ∈ A, MeasurableSet
          {z : α × ℝ | z.1 ∈ a.B k r' ⟨D z₀, h₀⟩ ∧ z.2 ∈ a.block k r' ⟨D z₀, h₀⟩ ∧ vb z = v₀} := by
        intro v₀ _
        have hblkm : MeasurableSet (a.block k r' ⟨D z₀, h₀⟩) := by
          simp only [block]; rw [interval_eq]; exact measurableSet_Icc
        exact ((hBm _).preimage measurable_fst).inter
          ((hblkm.preimage measurable_snd).inter (hvbm (measurableSet_singleton v₀)))
      have hdisjπ : (A : Set ℤ).PairwiseDisjoint fun v₀ => {w : ℝ | ⌊w / ξ⌋ = v₀} := by
        intro v hv v' hv' hvv
        simp only [Function.onFun]
        rw [Set.disjoint_left]
        intro w h1 h2
        exact hvv (h1.symm.trans h2)
      calc ρW {z | state z = s ∧ vb z ∈ A}
          = a.rho k ({z | state z = s ∧ vb z ∈ A} ∩ W₃) := Measure.restrict_apply' hW₃m
        _ ≤ a.mu k ({z | state z = s ∧ vb z ∈ A} ∩ W₃) := hρμ _
        _ ≤ a.mu k (⋃ v₀ ∈ A, {z | z.1 ∈ a.B k r' ⟨D z₀, h₀⟩ ∧
              z.2 ∈ a.block k r' ⟨D z₀, h₀⟩ ∧ vb z = v₀}) := measure_mono hsub
        _ = ∑' v₀ : A, a.mu k {z | z.1 ∈ a.B k r' ⟨D z₀, h₀⟩ ∧
              z.2 ∈ a.block k r' ⟨D z₀, h₀⟩ ∧ vb z = v₀} :=
            measure_biUnion (Set.to_countable A) hdisjv hmeasv
        _ ≤ ∑' v₀ : A, ENNReal.ofReal (p.K k * a.q k r') * a.nu k (a.A k r' ⟨D z₀, h₀⟩) *
              a.pi k {w | ⌊w / ξ⌋ = v₀} := ENNReal.tsum_le_tsum fun v₀ => hvel _ v₀
        _ = ENNReal.ofReal (p.K k * a.q k r') * a.nu k (a.A k r' ⟨D z₀, h₀⟩) *
              ∑' v₀ : A, a.pi k {w | ⌊w / ξ⌋ = (v₀ : ℤ)} := ENNReal.tsum_mul_left
        _ = ENNReal.ofReal (p.K k * a.q k r') * a.nu k (a.A k r' ⟨D z₀, h₀⟩) * π' A := by
            rw [hπ'apply]
            congr 1
            rw [← measure_biUnion (Set.to_countable A) hdisjπ
              (fun v₀ _ => hfl (measurableSet_singleton v₀))]
            congr 1
            ext w; simp
        _ = ENNReal.ofReal (p.K k) * (ENNReal.ofReal (a.q k r') *
              a.nu k (a.A k r' ⟨D z₀, h₀⟩)) * π' A := by
            rw [ENNReal.ofReal_mul hKpos.le]; ring
    · have hempty : {z | state z = s ∧ vb z ∈ A} ∩ W₃ = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun z hz => hne ⟨z, hz.2, hz.1.1⟩
      calc ρW {z | state z = s ∧ vb z ∈ A}
          = a.rho k ({z | state z = s ∧ vb z ∈ A} ∩ W₃) := Measure.restrict_apply' hW₃m
        _ = 0 := by rw [hempty, measure_empty]
        _ ≤ _ := zero_le
  -- pruning of light states
  set δ : ℝ≥0∞ := ENNReal.ofReal (1 / (18 * M)) with hδ
  have hδ0 : δ ≠ 0 := by simp [hδ]; positivity
  have hδtop : δ ≠ ⊤ := ENNReal.ofReal_ne_top
  let w := stWeight p a k r PL.Q r' ξ
  let keep := referenceKeep ρW state w δ
  have hkeepm : MeasurableSet keep := measurableSet_referenceKeep ρW state hstm w δ
  let ρ' : Measure (α × ℝ) := ρW.restrict keep
  let pos : Set (α × ℝ) := {z | 0 < ρ' (state ⁻¹' {state z})}
  have hposm : MeasurableSet pos := by
    have : pos = ⋃ s ∈ {s : ℕ × (Fin 2 → ℤ) | 0 < ρ' (state ⁻¹' {s})}, state ⁻¹' {s} := by
      ext z; simp [pos]
    rw [this]
    exact MeasurableSet.biUnion (Set.to_countable _) fun s _ => hstm (measurableSet_singleton s)
  have hposnull : ρ' posᶜ = 0 := by
    have : posᶜ ⊆ ⋃ s ∈ {s : ℕ × (Fin 2 → ℤ) | ρ' (state ⁻¹' {s}) = 0}, state ⁻¹' {s} := by
      intro z hz
      simp only [pos, mem_compl_iff, mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at hz
      exact mem_iUnion₂.mpr ⟨state z, hz, rfl⟩
    refine measure_mono_null this ((measure_biUnion_null_iff (Set.to_countable _)).mpr ?_)
    intro s hs; exact hs
  let Wf : Set (α × ℝ) := W₃ ∩ keep ∩ pos
  have hWfm : MeasurableSet Wf := (hW₃m.inter hkeepm).inter hposm
  have hWfsub : Wf ⊆ PL.W := fun z hz => hz.1.1.1
  -- the mass bound
  have hloss : ρW keepᶜ ≤ δ * (9 * (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r PL.Q))) :=
    (reference_light_mass_le ρW state w δ).trans
      (mul_le_mul_right (tsum_stWeight_le p a k r PL.Q r' ξ hAm hdisj) _)
  have hmassWf : ENNReal.ofReal (a.q k r / (2 * M)) * a.nu k (a.A k r PL.Q) ≤ a.rho k Wf := by
    have h1 : a.rho k Wf = ρ' univ := by
      have e1 : a.rho k Wf = ρW (keep ∩ pos) := by
        rw [Measure.restrict_apply (hkeepm.inter hposm)]
        congr 1; ext z; simp only [Wf, mem_inter_iff]; tauto
      have e2 : ρW (keep ∩ pos) = ρ' pos := by
        rw [Measure.restrict_apply hposm, inter_comm]
      have e3 := measure_inter_conull (μ := ρ') (s := univ) (t := pos) hposnull
      rw [univ_inter] at e3
      rw [e1, e2, e3]
    have h2 : ρ' univ = ρW keep := by rw [Measure.restrict_apply_univ]
    have h3 : ρW univ = a.rho k PL.W := by rw [Measure.restrict_apply_univ, hW₃]
    have h4 : ρW univ ≤ ρW keep + ρW keepᶜ := by
      calc ρW univ = ρW (keep ∪ keepᶜ) := by rw [union_compl_self]
        _ ≤ _ := measure_union_le _ _
    rw [h1, h2]
    have hW := PL.mass
    have hsplit : ENNReal.ofReal (a.q k r / M) * a.nu k (a.A k r PL.Q) =
        ENNReal.ofReal (a.q k r / (2 * M)) * a.nu k (a.A k r PL.Q) +
          δ * (9 * (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r PL.Q))) := by
      rw [hδ, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← add_mul, ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      congr 2; field_simp; ring
    have h5 : ENNReal.ofReal (a.q k r / (2 * M)) * a.nu k (a.A k r PL.Q) +
        δ * (9 * (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r PL.Q))) ≤
        ρW keep + δ * (9 * (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r PL.Q))) := by
      rw [← hsplit]
      exact hW.trans (h3 ▸ h4.trans (add_le_add le_rfl hloss))
    have hfin : δ * (9 * (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r PL.Q))) ≠ ⊤ :=
      ENNReal.mul_ne_top hδtop (ENNReal.mul_ne_top (by simp)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)))
    exact (ENNReal.add_le_add_iff_right hfin).mp h5
  -- witnesses of positive retained states
  have hwitness : ∀ (X : Set (α × ℝ)), MeasurableSet X → 0 < ρ' X →
      ∃ z ∈ X, z ∈ W₃ ∧ z ∈ keep := by
    intro X hX hpos
    by_contra hcon
    push Not at hcon
    have : ρ' X = 0 := by
      simp only [ρ', ρW]
      rw [Measure.restrict_apply hX, Measure.restrict_apply (hX.inter hkeepm)]
      have : X ∩ keep ∩ W₃ = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun z hz => hcon z hz.1.1 hz.2 hz.1.2
      rw [this, measure_empty]
    exact absurd this hpos.ne'
  -- the finite range of velocity bins
  set bins : Finset ℤ := Finset.Icc (-⌈M / ξ⌉ - 1) ⌈M / ξ⌉ with hbins
  have hvb_bins : ∀ z ∈ W₃, vb z ∈ bins := fun z hz =>
    Model.floor_div_mem_Icc hξ (PL.vel_bound z hz.1)
  -- real palette weights of bins
  let πr : ℤ → ℝ := fun b => (a.pi k {w | ⌊w / ξ⌋ = b}).toReal
  have hπ'single : ∀ b : ℤ, π' {b} = a.pi k {w | ⌊w / ξ⌋ = b} := by
    intro b; rw [hπ'apply]; rfl
  -- witness bins of positive retained states
  set θ : ℝ := 1 / (18 * M * p.K k) with hθ
  have hθpos : 0 < θ := by positivity
  have hVw : ∀ st : ℕ × (Fin 2 → ℤ), 0 < ρ' (state ⁻¹' {st}) →
      θ ≤ ∑ b ∈ bins.filter (fun b => 0 < ρ' {z | state z = st ∧ vb z = b}), πr b := by
    intro st hst
    have hwb := WitnessBins.witness_bins ρW state hstm vb hvbm π' w (ENNReal.ofReal (p.K k)) δ
      hδ0 hδtop ENNReal.ofReal_ne_top hcap st hst
    -- the witness bins lie in `bins`
    have hsubV : {b | 0 < ρ' {z | state z = st ∧ vb z = b}} ⊆
        ((bins.filter (fun b => 0 < ρ' {z | state z = st ∧ vb z = b})) : Set ℤ) := by
      intro b hb
      have hmeas : MeasurableSet {z | state z = st ∧ vb z = b} :=
        (hstm (measurableSet_singleton st)).inter (hvbm (measurableSet_singleton b))
      obtain ⟨z, ⟨_, hzb⟩, hzW, -⟩ := hwitness _ hmeas hb
      simp only [Finset.coe_filter, mem_ofPred_eq]
      exact ⟨hzb ▸ hvb_bins z hzW, hb⟩
    have hle := (hwb.trans (measure_mono hsubV))
    rw [← sum_measure_singleton] at hle
    simp only [hπ'single] at hle
    have hfin : ∀ b, a.pi k {w | ⌊w / ξ⌋ = b} ≠ ⊤ := fun b => measure_ne_top _ _
    rw [← ENNReal.toReal_le_toReal (by simp [ENNReal.div_eq_top]; tauto)
      (ENNReal.sum_ne_top.mpr fun b _ => hfin b), ENNReal.toReal_sum (fun b _ => hfin b)] at hle
    convert hle using 1
    rw [hδ, ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal hKpos.le, hθ]
    field_simp
  -- thin palette near a bin
  have hξKc' : ξ ≤ 1 / Kc := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hthinR : ∀ b₁ : ℤ, ∑ b ∈ bins.filter (fun b : ℤ => |(b : ℝ) * ξ - (b₁ : ℝ) * ξ| < 1 / Kc),
      πr b ≤ θ / 2 := by
    intro b₁
    set F := bins.filter (fun b : ℤ => |(b : ℝ) * ξ - (b₁ : ℝ) * ξ| < 1 / Kc)
    have hfin : ∀ b, a.pi k {w | ⌊w / ξ⌋ = b} ≠ ⊤ := fun b => measure_ne_top _ _
    have hunion : ∑ b ∈ F, a.pi k {w | ⌊w / ξ⌋ = b} =
        a.pi k (⋃ b ∈ F, {w | ⌊w / ξ⌋ = b}) := by
      rw [measure_biUnion_finset]
      · intro b _ b' _ hbb
        simp only [Function.onFun]
        rw [Set.disjoint_left]; intro w h1 h2; exact hbb (h1.symm.trans h2)
      · intro b _; exact hfl (measurableSet_singleton b)
    have hsub : (⋃ b ∈ F, {w : ℝ | ⌊w / ξ⌋ = b}) ⊆
        Icc ((b₁ : ℝ) * ξ - 2 / Kc) ((b₁ : ℝ) * ξ + 2 / Kc) := by
      intro w hw
      simp only [mem_iUnion] at hw
      obtain ⟨b, hb, hwb⟩ := hw
      have hbb := (Finset.mem_filter.mp hb).2
      rw [abs_lt] at hbb
      obtain ⟨hb1, hb2⟩ := hbb
      rw [mem_ofPred_eq, Int.floor_eq_iff] at hwb
      have h1 : (b : ℝ) * ξ ≤ w := by rw [le_div_iff₀ hξ] at hwb; linarith [hwb.1]
      have h2 : w < (b : ℝ) * ξ + ξ := by
        have := hwb.2; rw [div_lt_iff₀ hξ] at this; linarith
      have h2K : 2 / Kc = 2 * (1 / Kc) := by ring
      rw [h2K]
      constructor <;> linarith
    calc ∑ b ∈ F, πr b = (∑ b ∈ F, a.pi k {w | ⌊w / ξ⌋ = b}).toReal :=
          (ENNReal.toReal_sum fun b _ => hfin b).symm
      _ = (a.pi k (⋃ b ∈ F, {w | ⌊w / ξ⌋ = b})).toReal := by rw [hunion]
      _ ≤ (a.pi k (Icc ((b₁ : ℝ) * ξ - 2 / Kc) ((b₁ : ℝ) * ξ + 2 / Kc))).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ ≤ 1 / (36 * M * p.K k) := by
          have := hthin ((b₁ : ℝ) * ξ)
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) this
      _ = θ / 2 := by rw [hθ]; field_simp; ring
  -- the rows of positive retained states are bounded
  set Kt : ℝ := 3 * (2 * Kc) ^ 2 * (M + 1) with hKt
  have hrowb : ∀ st : ℕ × (Fin 2 → ℤ), 0 < ρ' (state ⁻¹' {st}) →
      ∃ h : st.1 < n', ∀ i, |deepRow p a k r PL.Q r' ⟨st.1, h⟩ i| ≤ Kt := by
    intro st hst
    have hθle := hVw st hst
    -- a witness bin and a far witness bin
    set Vst := bins.filter (fun b => 0 < ρ' {z | state z = st ∧ vb z = b})
    have hne : Vst.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne, Finset.sum_empty] at hθle
      linarith
    obtain ⟨b₁, hb₁⟩ := hne
    have hfar : ∃ b₂ ∈ Vst, 1 / Kc ≤ |(b₂ : ℝ) * ξ - (b₁ : ℝ) * ξ| := by
      by_contra hcon
      push Not at hcon
      have hsubF : Vst ⊆ bins.filter
          (fun b : ℤ => |(b : ℝ) * ξ - (b₁ : ℝ) * ξ| < 1 / Kc) := by
        intro b hb
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1, hcon b hb⟩
      have := (Finset.sum_le_sum_of_subset_of_nonneg hsubF
        (fun b _ _ => ENNReal.toReal_nonneg)).trans (hthinR b₁)
      linarith
    obtain ⟨b₂, hb₂, hsep⟩ := hfar
    have hmeas : ∀ b : ℤ, MeasurableSet {z | state z = st ∧ vb z = b} := fun b =>
      (hstm (measurableSet_singleton st)).inter (hvbm (measurableSet_singleton b))
    obtain ⟨z₁, ⟨hz₁s, hz₁b⟩, hz₁W, -⟩ := hwitness _ (hmeas b₁) (Finset.mem_filter.mp hb₁).2
    obtain ⟨z₂, ⟨hz₂s, hz₂b⟩, hz₂W, -⟩ := hwitness _ (hmeas b₂) (Finset.mem_filter.mp hb₂).2
    obtain ⟨h₁, -, hB₁, hblk₁⟩ := hsel z₁ hz₁W
    obtain ⟨h₂, -, hB₂, hblk₂⟩ := hsel z₂ hz₂W
    have hD₁ : D z₁ = st.1 := congrArg Prod.fst hz₁s
    have hD₂ : D z₂ = st.1 := congrArg Prod.fst hz₂s
    have hst : st.1 < n' := hD₁ ▸ h₁
    refine ⟨hst, ?_⟩
    have e₁ : (⟨D z₁, h₁⟩ : Fin n') = ⟨st.1, hst⟩ := Fin.ext hD₁
    have e₂ : (⟨D z₂, h₂⟩ : Fin n') = ⟨st.1, hst⟩ := Fin.ext hD₂
    rw [e₁] at hB₁ hblk₁
    rw [e₂] at hB₂ hblk₂
    -- the two evaluations
    have hpred : ∀ z, z ∈ W₃ → z.1 ∈ a.B k r' ⟨st.1, hst⟩ → z.2 ∈ a.block k r' ⟨st.1, hst⟩ →
        |deepRow p a k r PL.Q r' ⟨st.1, hst⟩ 0 + a.b k z.1 3 *
          deepRow p a k r PL.Q r' ⟨st.1, hst⟩ 1| ≤ M + 1 := by
      intro z hzW hzB hzblk
      have h1 := deepRow_predict p hp a k r PL.Q r' ⟨st.1, hst⟩ (a.b k z.1)
        (hplank _ z.1 (hBA _ hzB) z.2 hzblk).2
      have h2 := PL.yv_bound z hzW.1
      have h3 : p.K k * narrow p k r' / narrow p k r ≤ 1 := he₁.trans hE1
      have := abs_sub_abs_le_abs_sub (deepRow p a k r PL.Q r' ⟨st.1, hst⟩ 0 + a.b k z.1 3 *
          deepRow p a k r PL.Q r' ⟨st.1, hst⟩ 1) ((parentZoom p a k r PL.Q).coeff (a.b k z.1) 4)
      linarith
    have hv₁ := PL.vel_bound z₁ hz₁W.1
    have hv₂ := PL.vel_bound z₂ hz₂W.1
    have hvb₁ : ⌊a.b k z₁.1 3 / ξ⌋ = b₁ := hz₁b
    have hvb₂ : ⌊a.b k z₂.1 3 / ξ⌋ = b₂ := hz₂b
    have hbin : ∀ (x : ℝ) (b : ℤ), ⌊x / ξ⌋ = b → |x - (b : ℝ) * ξ| ≤ ξ := by
      intro x b hb
      rw [Int.floor_eq_iff] at hb
      have h1 : (b : ℝ) * ξ ≤ x := by rw [le_div_iff₀ hξ] at hb; linarith [hb.1]
      have h2 : x < ((b : ℝ) + 1) * ξ := by rw [div_lt_iff₀ hξ] at hb; linarith [hb.2]
      rw [abs_le]; constructor <;> nlinarith
    have hK₂ : 1 ≤ 2 * Kc := by linarith
    have hsepv : 1 / (2 * Kc) ≤ |a.b k z₂.1 3 - a.b k z₁.1 3| := by
      have h1 := hbin _ _ hvb₁
      have h2 := hbin _ _ hvb₂
      have hKc0 : 0 < Kc := by linarith
      have hhalf : 1 / (2 * Kc) = 1 / Kc - 1 / (2 * Kc) := by field_simp; ring
      have h2ξ : 2 * ξ ≤ 1 / (2 * Kc) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
      have := abs_sub_abs_le_abs_sub ((b₂ : ℝ) * ξ - (b₁ : ℝ) * ξ)
        ((b₂ : ℝ) * ξ - (b₁ : ℝ) * ξ - (a.b k z₂.1 3 - a.b k z₁.1 3))
      have h3 : |(b₂ : ℝ) * ξ - (b₁ : ℝ) * ξ - (a.b k z₂.1 3 - a.b k z₁.1 3)| ≤ 2 * ξ := by
        have := abs_sub (a.b k z₂.1 3 - (b₂ : ℝ) * ξ) (a.b k z₁.1 3 - (b₁ : ℝ) * ξ)
        rw [show (b₂ : ℝ) * ξ - (b₁ : ℝ) * ξ - (a.b k z₂.1 3 - a.b k z₁.1 3) =
          -((a.b k z₂.1 3 - (b₂ : ℝ) * ξ) - (a.b k z₁.1 3 - (b₁ : ℝ) * ξ)) by ring, abs_neg]
        linarith
      have h4 : (b₂ : ℝ) * ξ - (b₁ : ℝ) * ξ - ((b₂ : ℝ) * ξ - (b₁ : ℝ) * ξ -
          (a.b k z₂.1 3 - a.b k z₁.1 3)) = a.b k z₂.1 3 - a.b k z₁.1 3 := by ring
      rw [h4] at this
      linarith
    obtain ⟨hT0, hT1⟩ := Submission.Obl.k4_finite_row_graph_assembly.row_error_of_two_evaluations
      hK₂ (by linarith) (by linarith) hsepv (hpred z₁ hz₁W hB₁ hblk₁) (hpred z₂ hz₂W hB₂ hblk₂)
    intro i
    fin_cases i
    · exact hT0
    · have : 2 * (2 * Kc) * (M + 1) ≤ Kt := by
        rw [hKt]; nlinarith
      exact hT1.trans this
  -- the row field and the per-cell option counts
  let Trow : ℕ → Fin 2 → ℝ := fun m =>
    if h : m < n' then deepRow p a k r PL.Q r' ⟨m, h⟩ else 0
  set e₁ : ℝ := p.K k * narrow p k r' / narrow p k r with he₁def
  have he₁0 : 0 ≤ e₁ := by
    have := narrow_pos p hp k r'; have := narrow_pos p hp k r; positivity
  have hE₁pos : 0 < E₁ := lt_of_lt_of_le hξ hξE
  have hKt0 : 0 ≤ Kt := by positivity
  have hKc1 : 1 ≤ Kc := by linarith
  let S : (Fin 2 → ℤ) → Finset ℕ := fun c =>
    (Finset.range n').filter fun m => 0 < ρ' (state ⁻¹' {(m, c)})
  let V : (Fin 2 → ℤ) → ℕ → Finset ℤ := fun c m =>
    bins.filter fun b => 0 < ρ' {z | state z = (m, c) ∧ vb z = b}
  have hπ0 : ∀ b, 0 ≤ πr b := fun b => ENNReal.toReal_nonneg
  have hπsum : ∑ b ∈ bins, πr b ≤ 1 := by
    have hfin : ∀ b, a.pi k {w | ⌊w / ξ⌋ = b} ≠ ⊤ := fun b => measure_ne_top _ _
    rw [← ENNReal.toReal_sum fun b _ => hfin b, ← measure_biUnion_finset]
    · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
    · intro b _ b' _ hbb
      simp only [Function.onFun]
      rw [Set.disjoint_left]; intro w h1 h2; exact hbb (h1.symm.trans h2)
    · intro b _; exact hfl (measurableSet_singleton b)
  have hbinsK : ∀ b ∈ bins, |(b : ℝ) * ξ| ≤ Kc := by
    intro b hb
    rw [Finset.mem_Icc] at hb
    have hlo : (-⌈M / ξ⌉ - 1 : ℤ) ≤ b := hb.1
    have hhi : b ≤ ⌈M / ξ⌉ := hb.2
    have h1 : ((-⌈M / ξ⌉ - 1 : ℤ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hlo
    have h2 : (b : ℝ) ≤ (⌈M / ξ⌉ : ℝ) := by exact_mod_cast hhi
    have hc := Int.ceil_lt_add_one (M / ξ)
    push_cast at h1
    have hMξ : M / ξ * ξ = M := div_mul_cancel₀ _ hξ.ne'
    have h3 : (b : ℝ) * ξ ≤ M + ξ := by nlinarith
    have h4 : -(M + 2 * ξ) ≤ (b : ℝ) * ξ := by nlinarith
    rw [abs_le]; constructor <;> nlinarith
  have hcount : ∀ c, (((S c).image fun m => RowOptions.rowBin E₁ (Trow m)).card : ℝ) ≤
      Kc ^ 2 * (12 * Kc ^ 2 * (2 + Kc + Kt * ξ / E₁ + e₁ / E₁ + E₁ / E₁) + 2) ^ 2 /
        (θ ^ 2 / 2) := by
    intro c
    refine RowOptions.row_options_card Trow (PL.L c) πr (fun z => a.b k z.1 3)
      (fun z => (parentZoom p a k r PL.Q).coeff (a.b k z.1) 4) D vb hξ hE₁pos hE₁pos he₁0 hKt0
      hKc1 hθpos bins (S c) (V c) hπ0 hπsum hbinsK
      (fun b _ => (PL.L_card c b).trans (by linarith)) (fun m _ => Finset.filter_subset _ _)
      (fun m hm => hVw (m, c) (Finset.mem_filter.mp hm).2) (fun b₀ _ => hthinR b₀) ?_
    intro m hm b hb
    have hmeas : MeasurableSet {z | state z = (m, c) ∧ vb z = b} :=
      (hstm (measurableSet_singleton _)).inter (hvbm (measurableSet_singleton b))
    obtain ⟨z, ⟨hzs, hzb⟩, hzW, -⟩ := hwitness _ hmeas (Finset.mem_filter.mp hb).2
    obtain ⟨hm', hrb⟩ := hrowb (m, c) (Finset.mem_filter.mp hm).2
    obtain ⟨hD, -, hB, hblk⟩ := hsel z hzW
    have hDz : D z = m := congrArg Prod.fst hzs
    have hcz : cell z = c := congrArg Prod.snd hzs
    have e : (⟨D z, hD⟩ : Fin n') = ⟨m, hm'⟩ := Fin.ext hDz
    rw [e] at hB hblk
    have hTm : Trow m = deepRow p a k r PL.Q r' ⟨m, hm'⟩ := by simp only [Trow, dif_pos hm']
    refine ⟨z, hDz, hzb, ?_, ?_, ?_, ?_⟩
    · have := hzb
      simp only [vb] at this
      rw [Int.floor_eq_iff] at this
      have h1 : (b : ℝ) * ξ ≤ a.b k z.1 3 := by rw [le_div_iff₀ hξ] at this; linarith [this.1]
      have h2 : a.b k z.1 3 < (b : ℝ) * ξ + ξ := by
        have := this.2; rw [div_lt_iff₀ hξ] at this; linarith
      rw [abs_le]; constructor <;> linarith
    · rw [hTm]; exact hrb 1
    · rw [hTm]
      exact deepRow_predict p hp a k r PL.Q r' ⟨m, hm'⟩ (a.b k z.1)
        (hplank _ z.1 (hBA _ hB) z.2 hblk).2
    · have := PL.L_mem z hzW.1
      simp only [cell] at hcz
      rw [hcz] at this
      simpa [vb, hzb] using this
  -- the size bound
  set M' := rowReadyBound M Kc (p.K k) with hM'
  have hFb : Kc ^ 2 * (12 * Kc ^ 2 * (2 + Kc + Kt * ξ / E₁ + e₁ / E₁ + E₁ / E₁) + 2) ^ 2 /
      (θ ^ 2 / 2) ≤ Kc ^ 2 * (12 * Kc ^ 2 * (4 + Kc + Kt) + 2) ^ 2 / (θ ^ 2 / 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have h1 : Kt * ξ / E₁ ≤ Kt := by
      rw [mul_div_assoc]
      exact mul_le_of_le_one_right hKt0 ((div_le_one hE₁pos).mpr hξE)
    have h2 : e₁ / E₁ ≤ 1 := (div_le_one hE₁pos).mpr he₁
    have h3 : E₁ / E₁ = 1 := div_self hE₁pos.ne'
    have hle : 2 + Kc + Kt * ξ / E₁ + e₁ / E₁ + E₁ / E₁ ≤ 4 + Kc + Kt := by linarith
    have hK2 : 0 ≤ 12 * Kc ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hle hK2
    linarith
  have hFbM : Kc ^ 2 * (12 * Kc ^ 2 * (4 + Kc + Kt) + 2) ^ 2 / (θ ^ 2 / 2) ≤ M' := by
    rw [hM', rowReadyBound, ← hKt, ← hθ]
    have : 0 ≤ 2 * M + Kt := by positivity
    linarith
  have hKtM : Kt ≤ M' := by
    rw [hM', rowReadyBound, ← hKt, ← hθ]
    have : 0 ≤ Kc ^ 2 * (12 * Kc ^ 2 * (4 + Kc + Kt) + 2) ^ 2 / (θ ^ 2 / 2) := by positivity
    linarith
  have h2MM : 2 * M ≤ M' := by
    rw [hM', rowReadyBound, ← hKt, ← hθ]
    have : 0 ≤ Kc ^ 2 * (12 * Kc ^ 2 * (4 + Kc + Kt) + 2) ^ 2 / (θ ^ 2 / 2) := by positivity
    linarith
  have hMM : M ≤ M' := by linarith
  have hM'1 : 1 ≤ M' := by linarith
  -- assembling the row-ready parent
  have hTm : Measurable fun z : α × ℝ => Trow (D z) :=
    show Measurable (Trow ∘ D) from measurable_from_top.comp hDm
  refine ⟨{
    Q := PL.Q
    W := Wf
    measurable_W := hWfm
    W_sub := hWfsub.trans PL.W_sub
    measurable_A := PL.measurable_A
    B_sub_A := PL.B_sub_A
    prior_ne := PL.prior_ne
    mass := ?_
    pos_bound := fun z hz => (PL.pos_bound z (hWfsub hz)).trans hMM
    vel_bound := fun z hz => (PL.vel_bound z (hWfsub hz)).trans hMM
    T := fun z => Trow (D z)
    measurable_T := hTm
    T_bound := ?_
    T_predict := ?_
    F := fun c => (S c).image fun m => RowOptions.rowBin E₁ (Trow m)
    F_card := fun c => (hcount c).trans (hFb.trans hFbM)
    T_list := ?_
    joint_cap := ?_ }⟩
  · refine le_trans (mul_le_mul_left ?_ _) hmassWf
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_left hq.le (by positivity) h2MM
  · intro z hz i
    obtain ⟨h, hrb⟩ := hrowb (state z) hz.2
    have hTz : Trow (D z) = deepRow p a k r PL.Q r' ⟨(state z).1, h⟩ := by
      simp only [Trow, state, dif_pos h]
    rw [hTz]; exact (hrb i).trans hKtM
  · intro z hz
    obtain ⟨hD, -, hB, hblk⟩ := hsel z hz.1.1
    have hTz : Trow (D z) = deepRow p a k r PL.Q r' ⟨D z, hD⟩ := by simp only [Trow, dif_pos hD]
    rw [hTz]
    refine (deepRow_predict p hp a k r PL.Q r' ⟨D z, hD⟩ (a.b k z.1)
      (hplank _ z.1 (hBA _ hB) z.2 hblk).2).trans ?_
    calc p.K k * narrow p k r' / narrow p k r ≤ E₁ := he₁
      _ ≤ M' * E₁ := le_mul_of_one_le_left hE₁pos.le hM'1
  · intro z hz
    have hD : D z < n' := hz.1.1.2
    refine Finset.mem_image.mpr ⟨D z, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hD, hz.2⟩
  · intro c v₀
    refine le_trans (measure_mono ?_) ((PL.joint_cap c v₀).trans ?_)
    · rintro z ⟨hzW, hzc, hzv⟩
      exact ⟨hWfsub hzW, hzc, hzv⟩
    · gcongr

end

end Submission.Obl.k4_narrow_projected_row_parents
