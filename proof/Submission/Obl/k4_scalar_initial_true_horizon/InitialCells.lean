import Submission.Obl.k4_scalar_initial_true_horizon.InitialCellDefs
import Submission.Obl.k4_scalar_initial_true_horizon.InitialCollision
import Submission.Obl.k4_scalar_initial_true_horizon.InitialGroup

/-!
# Maximal good cells and the plank cap of bad trajectories

Cells are nested, so the coarsest good cell around each covered trajectory gives a
disjoint family of "maximal good" cells covering every covered trajectory.  A trajectory
with no good cell up to the finest level is bad; every cell containing a bad trajectory is
light, and a plank around any trajectory meets only boundedly many cells of comparable
size.  This gives the one-dimensional plank cap used by the collision estimate.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction (Coeff spatial hidden)

/-- Nesting of the dyadic cell indices. -/
theorem cellIdx_nested {q t₀ : ℝ} {k k' : ℕ} (hk : k' ≤ k) {l l' : Coeff}
    (h : cellIdx q t₀ k l = cellIdx q t₀ k l') : cellIdx q t₀ k' l = cellIdx q t₀ k' l' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [cellIdx] at h1 h2 ⊢
  obtain ⟨d, rfl⟩ : ∃ d, k = k' + d := ⟨k - k', by omega⟩
  have hpow : (2 : ℝ) ^ (k' + d) = 2 ^ k' * 2 ^ d := pow_add _ _ _
  have hfst : ∀ x : ℝ, ⌊x / (q / 2 ^ k')⌋ = ⌊x / (q / 2 ^ (k' + d))⌋ / ((2 ^ d : ℕ) : ℤ) := by
    intro x
    rw [← Int.floor_div_natCast]
    congr 1
    rw [hpow]
    push_cast
    by_cases hq : q = 0
    · simp [hq]
    · field_simp
  have hsnd : ∀ x : ℝ, ⌊x * 2 ^ k'⌋ = ⌊x * 2 ^ (k' + d)⌋ / ((2 ^ d : ℕ) : ℤ) := by
    intro x
    rw [← Int.floor_div_natCast]
    congr 1
    rw [hpow]
    push_cast
    field_simp
  rw [hfst, hfst, h1, hsnd, hsnd, h2]

/-- Maximal good cells of one group: good, at a level at most `kmax`, and without a good
cell at a coarser level around any of their trajectories. -/
def MaxGood (P : Coeff → Prop) (idx : ℕ → Coeff → ℤ × ℤ) (good : ℕ → ℤ × ℤ → Prop)
    (kmax k : ℕ) (c : ℤ × ℤ) : Prop :=
  k ≤ kmax ∧ good k c ∧ ∀ l, P l → idx k l = c → ∀ k' < k, ¬ good k' (idx k' l)

/-- Distinct maximal good cells of a group are disjoint. -/
theorem maxGood_disjoint {P : Coeff → Prop} {idx : ℕ → Coeff → ℤ × ℤ}
    (hnest : ∀ k k' l l', k' ≤ k → idx k l = idx k l' → idx k' l = idx k' l')
    {good : ℕ → ℤ × ℤ → Prop} {kmax k k' : ℕ} {c c' : ℤ × ℤ}
    (h : MaxGood P idx good kmax k c) (h' : MaxGood P idx good kmax k' c')
    (hne : (k, c) ≠ (k', c')) {l : Coeff} (hl : P l) (hlc : idx k l = c)
    (hlc' : idx k' l = c') : False := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact h'.2.2 l hl hlc' k hlt (hlc ▸ h.2.1)
  · subst heq
    exact hne (by rw [← hlc, ← hlc'])
  · exact h.2.2 l hl hlc k' hgt (hlc' ▸ h'.2.1)

/-- Every covered trajectory lies in a maximal good cell. -/
theorem exists_maxGood_of_covered {P : Coeff → Prop} {idx : ℕ → Coeff → ℤ × ℤ}
    (hnest : ∀ k k' l l', k' ≤ k → idx k l = idx k l' → idx k' l = idx k' l')
    {good : ℕ → ℤ × ℤ → Prop} {kmax : ℕ} {l : Coeff} (hl : P l)
    (hcov : ∃ k ≤ kmax, good k (idx k l)) :
    ∃ k c, MaxGood P idx good kmax k c ∧ idx k l = c := by
  classical
  let κ := Nat.find hcov
  have hκ : κ ≤ kmax ∧ good κ (idx κ l) := Nat.find_spec hcov
  refine ⟨κ, idx κ l, ⟨hκ.1, hκ.2, ?_⟩, rfl⟩
  intro l' _ hl' k' hk'
  rw [hnest κ k' l' l hk'.le hl']
  intro hg
  exact Nat.find_min hcov hk' ⟨by omega, hg⟩

theorem measurable_cellIdx (q t₀ : ℝ) (k : ℕ) : Measurable (cellIdx q t₀ k) := by
  unfold cellIdx
  refine Measurable.prodMk ?_ ?_
  · have : Measurable (fun l : Coeff => spatial l t₀ / (q / 2 ^ k)) := by
      unfold spatial; fun_prop
    exact this.floor
  · have : Measurable (fun l : Coeff => l.2 1 * 2 ^ k) := by fun_prop
    exact this.floor

theorem measurable_xBin (aL t₀ : ℝ) : Measurable (xBin aL t₀) := by
  unfold xBin
  have : Measurable (fun l : Coeff => hidden l t₀ / aL) := by
    unfold Submission.Obl.k4_scalar_terminal_chart_packet_extraction.hidden; fun_prop
  exact this.floor

theorem measurableSet_bddTraj (Nb Kb : ℝ) : MeasurableSet {l : Coeff | bddTraj Nb Kb l} := by
  simp only [bddTraj, setOf_and, setOf_forall]
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun e => ?_)
  · exact measurableSet_le (by fun_prop) measurable_const
  · exact measurableSet_le (by fun_prop) measurable_const

theorem measurableSet_cellSet (Nb Kb aL q t₀ : ℝ) (m : ℤ) (k : ℕ) (c : ℤ × ℤ) :
    MeasurableSet (cellSet Nb Kb aL q t₀ m k c) := by
  unfold cellSet
  simp only [setOf_and]
  exact (measurableSet_bddTraj Nb Kb).inter
    ((measurable_xBin aL t₀ (measurableSet_singleton m)).inter
      (measurable_cellIdx q t₀ k (measurableSet_singleton c)))

/-- Card of an integer interval between floors. -/
theorem card_Icc_floor_le {x y : ℝ} (hxy : x ≤ y) :
    ((Finset.Icc ⌊x⌋ ⌊y⌋).card : ℝ) ≤ y - x + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le y
  have h2 := Int.lt_floor_add_one x
  have hnn : 0 ≤ ⌊y⌋ + 1 - ⌊x⌋ := by
    have : ⌊x⌋ ≤ ⌊y⌋ := Int.floor_mono hxy
    omega
  have : ((⌊y⌋ + 1 - ⌊x⌋).toNat : ℝ) = ((⌊y⌋ + 1 - ⌊x⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
  rw [this]
  push_cast
  linarith

/-- The cells of level `k` met by a plank of width `w` around `l₀`. -/
noncomputable def plankBox (q t₀ : ℝ) (k : ℕ) (l₀ : Coeff) (w : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc ⌊(spatial l₀ t₀ - w) / (q / 2 ^ k)⌋ ⌊(spatial l₀ t₀ + w) / (q / 2 ^ k)⌋) ×ˢ
    (Finset.Icc ⌊(l₀.2 1 - 2 * w / q) * 2 ^ k⌋ ⌊(l₀.2 1 + 2 * w / q) * 2 ^ k⌋)

theorem cellIdx_mem_plankBox {q t₀ : ℝ} (hq : 0 < q) (k : ℕ) (l₀ l : Coeff) (w : ℝ)
    (hl : l ∈ plank (fun l : Coeff => l.2 0) (fun l => l.2 1) t₀ q l₀ w) :
    cellIdx q t₀ k l ∈ plankBox q t₀ k l₀ w := by
  have h0 := hl t₀ ⟨le_rfl, by linarith⟩
  have h1 := hl (t₀ + q) ⟨by linarith, le_rfl⟩
  simp only [trace] at h0 h1
  have hb : |spatial l₀ t₀ - spatial l t₀| ≤ w := by simpa [spatial] using h0
  have hs : |l₀.2 1 - l.2 1| ≤ 2 * w / q := by
    rw [le_div_iff₀ hq]
    have : q * (l₀.2 1 - l.2 1) = (l₀.2 0 + (t₀ + q) * l₀.2 1 - (l.2 0 + (t₀ + q) * l.2 1)) -
        (l₀.2 0 + t₀ * l₀.2 1 - (l.2 0 + t₀ * l.2 1)) := by ring
    calc |l₀.2 1 - l.2 1| * q = |q * (l₀.2 1 - l.2 1)| := by
          rw [abs_mul, abs_of_pos hq, mul_comm]
      _ ≤ |l₀.2 0 + (t₀ + q) * l₀.2 1 - (l.2 0 + (t₀ + q) * l.2 1)| +
          |l₀.2 0 + t₀ * l₀.2 1 - (l.2 0 + t₀ * l.2 1)| := by rw [this]; exact abs_sub _ _
      _ ≤ 2 * w := by linarith
  have hw : 0 < q / 2 ^ k := by positivity
  rw [abs_le] at hb hs
  simp only [plankBox, cellIdx, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨Int.floor_mono ?_, Int.floor_mono ?_⟩, ⟨Int.floor_mono ?_, Int.floor_mono ?_⟩⟩
  · exact div_le_div_of_nonneg_right (by linarith) hw.le
  · exact div_le_div_of_nonneg_right (by linarith) hw.le
  · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

theorem card_plankBox_le {q t₀ : ℝ} (hq : 0 < q) (k : ℕ) (l₀ : Coeff) {w : ℝ} (hw : 0 ≤ w) :
    ((plankBox q t₀ k l₀ w).card : ℝ) ≤
      (2 * w / (q / 2 ^ k) + 2) * (4 * w / (q / 2 ^ k) + 2) := by
  have hwk : 0 < q / 2 ^ k := by positivity
  rw [plankBox, Finset.card_product]
  push_cast
  have h1 := card_Icc_floor_le (x := (spatial l₀ t₀ - w) / (q / 2 ^ k))
    (y := (spatial l₀ t₀ + w) / (q / 2 ^ k)) (div_le_div_of_nonneg_right (by linarith) hwk.le)
  have h2w : 0 ≤ 2 * w / q := by positivity
  have h2 := card_Icc_floor_le (x := (l₀.2 1 - 2 * w / q) * 2 ^ k)
    (y := (l₀.2 1 + 2 * w / q) * 2 ^ k)
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have e1 : (spatial l₀ t₀ + w) / (q / 2 ^ k) - (spatial l₀ t₀ - w) / (q / 2 ^ k) + 2 =
      2 * w / (q / 2 ^ k) + 2 := by field_simp; ring
  have e2 : (l₀.2 1 + 2 * w / q) * 2 ^ k - (l₀.2 1 - 2 * w / q) * 2 ^ k + 2 =
      4 * w / (q / 2 ^ k) + 2 := by field_simp; ring
  rw [e1] at h1; rw [e2] at h2
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Trajectories spending at least the fraction `φ₀` of the half-open block in the event. -/
def longTraj (E : Set (Coeff × ℝ)) (t₀ q φ₀ : ℝ) (l : Coeff) : Prop :=
  ENNReal.ofReal (φ₀ * q) ≤ volume {t ∈ Ico t₀ (t₀ + q) | (l, t) ∈ E}

theorem measurableSet_longTraj {E : Set (Coeff × ℝ)} (hE : MeasurableSet E) (t₀ q φ₀ : ℝ) :
    MeasurableSet {l | longTraj E t₀ q φ₀ l} := by
  have hS : MeasurableSet (E ∩ (univ ×ˢ Ico t₀ (t₀ + q))) :=
    hE.inter (MeasurableSet.univ.prod measurableSet_Ico)
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hS
  have heq : {l | longTraj E t₀ q φ₀ l} =
      {l | ENNReal.ofReal (φ₀ * q) ≤ volume (Prod.mk l ⁻¹' (E ∩ (univ ×ˢ Ico t₀ (t₀ + q))))} := by
    ext l
    simp only [longTraj, mem_ofPred_eq]
    congr! 2
    ext t
    simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_prod, mem_univ, true_and]
    tauto
  rw [heq]
  exact measurableSet_le measurable_const hm

/-- Good cells: original incidence mass at least `Φf` times the chart width. -/
def goodCell (μa : Measure (Coeff × ℝ)) (Nb Kb aL q t₀ Φf : ℝ) (m : ℤ) (k : ℕ)
    (c : ℤ × ℤ) : Prop :=
  ENNReal.ofReal (Φf * cellJ q k) ≤ μa (cellSet Nb Kb aL q t₀ m k c ×ˢ Icc t₀ (t₀ + q))

/-- Bad long trajectories of the group `m`: bounded, long, and without good cells. -/
def badLong (μa : Measure (Coeff × ℝ)) (E : Set (Coeff × ℝ)) (Nb Kb aL q t₀ Φf φ₀ : ℝ)
    (m : ℤ) (kmax : ℕ) : Set Coeff :=
  {l | bddTraj Nb Kb l ∧ xBin aL t₀ l = m ∧
    (¬ ∃ k ≤ kmax, goodCell μa Nb Kb aL q t₀ Φf m k (cellIdx q t₀ k l)) ∧
    longTraj E t₀ q φ₀ l}

theorem measurableSet_badLong (μa : Measure (Coeff × ℝ)) {E : Set (Coeff × ℝ)}
    (hE : MeasurableSet E) (Nb Kb aL q t₀ Φf φ₀ : ℝ) (m : ℤ) (kmax : ℕ) :
    MeasurableSet (badLong μa E Nb Kb aL q t₀ Φf φ₀ m kmax) := by
  have hgood : MeasurableSet
      {l | ∃ k ≤ kmax, goodCell μa Nb Kb aL q t₀ Φf m k (cellIdx q t₀ k l)} := by
    have : {l | ∃ k ≤ kmax, goodCell μa Nb Kb aL q t₀ Φf m k (cellIdx q t₀ k l)} =
        ⋃ k ∈ Finset.range (kmax + 1),
          cellIdx q t₀ k ⁻¹' {c | goodCell μa Nb Kb aL q t₀ Φf m k c} := by
      ext l
      simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, mem_preimage, exists_prop,
        Nat.lt_succ_iff]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun k _ =>
      measurable_cellIdx q t₀ k (DiscreteMeasurableSpace.forall_measurableSet _)
  unfold badLong
  simp only [setOf_and]
  exact (measurableSet_bddTraj Nb Kb).inter ((measurable_xBin aL t₀
    (measurableSet_singleton m)).inter (hgood.compl.inter (measurableSet_longTraj hE t₀ q φ₀)))

/-- A cell containing a bad long trajectory is light. -/
theorem badLong_cell_le (ν : Measure Coeff) {E : Set (Coeff × ℝ)} (hE : MeasurableSet E)
    {Nb Kb aL q t₀ Φf φ₀ : ℝ} (hq : 0 < q) (hφ₀ : 0 < φ₀) (m : ℤ) {kmax k : ℕ}
    (hk : k ≤ kmax) (c : ℤ × ℤ) :
    ν (badLong ((ν.prod volume).restrict E) E Nb Kb aL q t₀ Φf φ₀ m kmax ∩
        cellSet Nb Kb aL q t₀ m k c) ≤ ENNReal.ofReal (Φf * cellJ q k / (φ₀ * q)) := by
  set BL := badLong ((ν.prod volume).restrict E) E Nb Kb aL q t₀ Φf φ₀ m kmax with hBL
  rcases (BL ∩ cellSet Nb Kb aL q t₀ m k c).eq_empty_or_nonempty with he | ⟨l, hlB, hlc⟩
  · rw [he, measure_empty]; exact bot_le
  · have hcl : cellIdx q t₀ k l = c := hlc.2.2
    have hnot : ¬ goodCell ((ν.prod volume).restrict E) Nb Kb aL q t₀ Φf m k c := by
      intro hg
      exact hlB.2.2.1 ⟨k, hk, hcl ▸ hg⟩
    have hlt := not_le.mp hnot
    have hmeas : MeasurableSet (BL ∩ cellSet Nb Kb aL q t₀ m k c) :=
      (measurableSet_badLong _ hE _ _ _ _ _ _ _ m kmax).inter (measurableSet_cellSet _ _ _ _ _ m k c)
    have hlong := prior_le_of_long ν E hE _ hmeas (Ico t₀ (t₀ + q)) measurableSet_Ico
      (θ := φ₀ * q) (fun l' hl' => hl'.1.2.2.2)
    have hchain : ENNReal.ofReal (φ₀ * q) * ν (BL ∩ cellSet Nb Kb aL q t₀ m k c) <
        ENNReal.ofReal (Φf * cellJ q k) := by
      refine lt_of_le_of_lt (hlong.trans (measure_mono ?_)) hlt
      exact prod_mono inter_subset_right Ico_subset_Icc_self
    have hpos : 0 < φ₀ * q := mul_pos hφ₀ hq
    rw [ENNReal.ofReal_div_of_pos hpos]
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hpos).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hchain.le

/-- **The plank cap of bad long trajectories** at a level `k ≤ kmax`. -/
theorem badLong_plank_le (ν : Measure Coeff) {E : Set (Coeff × ℝ)} (hE : MeasurableSet E)
    {Nb Kb aL q t₀ Φf φ₀ : ℝ} (hq : 0 < q) (hφ₀ : 0 < φ₀) (hΦf : 0 ≤ Φf) (m : ℤ)
    {kmax k : ℕ} (hk : k ≤ kmax) (l₀ : Coeff) {w : ℝ} (hw : 0 ≤ w) :
    ν (badLong ((ν.prod volume).restrict E) E Nb Kb aL q t₀ Φf φ₀ m kmax ∩
        plank (fun l : Coeff => l.2 0) (fun l => l.2 1) t₀ q l₀ w) ≤
      ENNReal.ofReal ((2 * w / (q / 2 ^ k) + 2) * (4 * w / (q / 2 ^ k) + 2) *
        (Φf * cellJ q k / (φ₀ * q))) := by
  set BL := badLong ((ν.prod volume).restrict E) E Nb Kb aL q t₀ Φf φ₀ m kmax with hBL
  have hsub : BL ∩ plank (fun l : Coeff => l.2 0) (fun l => l.2 1) t₀ q l₀ w ⊆
      ⋃ c ∈ plankBox q t₀ k l₀ w, BL ∩ cellSet Nb Kb aL q t₀ m k c := by
    rintro l ⟨hlB, hlp⟩
    exact mem_biUnion (cellIdx_mem_plankBox hq k l₀ l w hlp) ⟨hlB, hlB.1, hlB.2.1, rfl⟩
  calc ν (BL ∩ plank (fun l : Coeff => l.2 0) (fun l => l.2 1) t₀ q l₀ w)
      ≤ ν (⋃ c ∈ plankBox q t₀ k l₀ w, BL ∩ cellSet Nb Kb aL q t₀ m k c) := measure_mono hsub
    _ ≤ ∑ c ∈ plankBox q t₀ k l₀ w, ν (BL ∩ cellSet Nb Kb aL q t₀ m k c) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ plankBox q t₀ k l₀ w, ENNReal.ofReal (Φf * cellJ q k / (φ₀ * q)) :=
        Finset.sum_le_sum fun c _ => badLong_cell_le ν hE hq hφ₀ m hk c
    _ = (plankBox q t₀ k l₀ w).card * ENNReal.ofReal (Φf * cellJ q k / (φ₀ * q)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((2 * w / (q / 2 ^ k) + 2) * (4 * w / (q / 2 ^ k) + 2) *
          (Φf * cellJ q k / (φ₀ * q))) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (card_plankBox_le hq k l₀ hw)

end Submission.Obl.k4_scalar_initial_true_horizon
