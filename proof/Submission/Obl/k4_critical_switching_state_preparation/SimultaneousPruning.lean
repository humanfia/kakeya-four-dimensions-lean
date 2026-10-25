import Mathlib

/-!
# Simultaneous state and trajectory floors

A finite law `σ₀ = (m.prod volume).withDensity h` on trajectory-time pairs is
restricted, by a decreasing sequence of measurable deletions, to a set on which
every retained switching state keeps a floor against its reference weight and
every retained trajectory keeps a floor on its time-section density against the
reference `m`.  Both floors hold for the FINAL set; the total deletion is paid
by the state budget plus the trajectory budget, regardless of the number of
rounds.  The trajectory space is an arbitrary measurable space.
-/

namespace Submission.Obl.k4_critical_switching_state_preparation.Pruning

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type*} [MeasurableSpace α] {Q : Type*}

/-- The time-section mass of `E` at the trajectory `l`, a density against `m`. -/
def sectionMass (h : α × ℝ → ℝ≥0∞) (E : Set (α × ℝ)) (l : α) : ℝ≥0∞ :=
  ∫⁻ τ, E.indicator h (l, τ)

/-- One simultaneous deletion round. -/
def pruneStep (σ₀ : Measure (α × ℝ)) (h : α × ℝ → ℝ≥0∞) (st : α × ℝ → Q)
    (w : Q → ℝ≥0∞) (lam lam' : ℝ≥0∞) (E : Set (α × ℝ)) : Set (α × ℝ) :=
  E ∩ {p | lam * w (st p) ≤ σ₀ (E ∩ st ⁻¹' {st p})} ∩
    {p | lam' ≤ sectionMass h E p.1}

/-- The decreasing sequence of retained sets. -/
def pruneSeq (σ₀ : Measure (α × ℝ)) (h : α × ℝ → ℝ≥0∞) (st : α × ℝ → Q)
    (w : Q → ℝ≥0∞) (lam lam' : ℝ≥0∞) (E₀ : Set (α × ℝ)) : ℕ → Set (α × ℝ)
  | 0 => E₀
  | n + 1 => pruneStep σ₀ h st w lam lam' (pruneSeq σ₀ h st w lam lam' E₀ n)

theorem measurable_sectionMass {h : α × ℝ → ℝ≥0∞} (hh : Measurable h)
    {E : Set (α × ℝ)} (hE : MeasurableSet E) : Measurable (sectionMass h E) :=
  (hh.indicator hE).lintegral_prod_right'

theorem measurableSet_pruneStep [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (σ₀ : Measure (α × ℝ)) {h : α × ℝ → ℝ≥0∞}
    (hh : Measurable h) {st : α × ℝ → Q} (hst : Measurable st) (w : Q → ℝ≥0∞)
    (lam lam' : ℝ≥0∞) {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    MeasurableSet (pruneStep σ₀ h st w lam lam' E) := by
  refine (hE.inter ?_).inter ?_
  · have : {p : α × ℝ | lam * w (st p) ≤ σ₀ (E ∩ st ⁻¹' {st p})} =
        st ⁻¹' {q | lam * w q ≤ σ₀ (E ∩ st ⁻¹' {q})} := rfl
    rw [this]
    exact hst (Set.to_countable _).measurableSet
  · exact measurable_fst (measurableSet_le measurable_const
      (measurable_sectionMass hh hE))

theorem measurableSet_pruneSeq [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (σ₀ : Measure (α × ℝ)) {h : α × ℝ → ℝ≥0∞}
    (hh : Measurable h) {st : α × ℝ → Q} (hst : Measurable st) (w : Q → ℝ≥0∞)
    (lam lam' : ℝ≥0∞) {E₀ : Set (α × ℝ)} (hE₀ : MeasurableSet E₀) (n : ℕ) :
    MeasurableSet (pruneSeq σ₀ h st w lam lam' E₀ n) := by
  induction n with
  | zero => exact hE₀
  | succ n ih => exact measurableSet_pruneStep σ₀ hh hst w lam lam' ih

theorem pruneSeq_succ_subset (σ₀ : Measure (α × ℝ)) (h : α × ℝ → ℝ≥0∞)
    (st : α × ℝ → Q) (w : Q → ℝ≥0∞) (lam lam' : ℝ≥0∞) (E₀ : Set (α × ℝ)) (n : ℕ) :
    pruneSeq σ₀ h st w lam lam' E₀ (n + 1) ⊆ pruneSeq σ₀ h st w lam lam' E₀ n :=
  fun _ hp => hp.1.1

theorem antitone_pruneSeq (σ₀ : Measure (α × ℝ)) (h : α × ℝ → ℝ≥0∞)
    (st : α × ℝ → Q) (w : Q → ℝ≥0∞) (lam lam' : ℝ≥0∞) (E₀ : Set (α × ℝ)) :
    Antitone (pruneSeq σ₀ h st w lam lam' E₀) :=
  antitone_nat_of_succ_le (pruneSeq_succ_subset σ₀ h st w lam lam' E₀)

/-- Mass of a cylinder piece of `E` over `D`, through the time-section masses. -/
theorem withDensity_inter_fst_preimage (m : Measure α) {h : α × ℝ → ℝ≥0∞}
    (hh : Measurable h) {E : Set (α × ℝ)} (hE : MeasurableSet E) {D : Set α}
    (hD : MeasurableSet D) :
    (m.prod volume).withDensity h (E ∩ Prod.fst ⁻¹' D) =
      ∫⁻ l in D, sectionMass h E l ∂m := by
  have hX : MeasurableSet (E ∩ Prod.fst ⁻¹' D) := hE.inter (measurable_fst hD)
  rw [withDensity_apply _ hX, ← lintegral_indicator hX,
    lintegral_prod _ ((hh.indicator hX).aemeasurable), ← lintegral_indicator hD]
  congr 1
  funext l
  by_cases hl : l ∈ D
  · rw [indicator_of_mem hl]
    unfold sectionMass
    congr 1
    funext τ
    by_cases hp : (l, τ) ∈ E
    · rw [indicator_of_mem (show (l, τ) ∈ E ∩ Prod.fst ⁻¹' D from ⟨hp, hl⟩),
        indicator_of_mem hp]
    · rw [indicator_of_notMem (fun h' => hp h'.1), indicator_of_notMem hp]
  · rw [indicator_of_notMem hl]
    have : ∀ τ : ℝ, (E ∩ Prod.fst ⁻¹' D).indicator h (l, τ) = 0 := fun τ =>
      indicator_of_notMem (fun h' => hl h'.2) _
    simp only [this, lintegral_zero]


section Limit

/-- The retained set: the intersection of all rounds. -/
def pruneLimit (σ₀ : Measure (α × ℝ)) (h : α × ℝ → ℝ≥0∞) (st : α × ℝ → Q)
    (w : Q → ℝ≥0∞) (lam lam' : ℝ≥0∞) (E₀ : Set (α × ℝ)) : Set (α × ℝ) :=
  ⋂ n, pruneSeq σ₀ h st w lam lam' E₀ n

/-- Every deleted point was light, as a state or as a trajectory, at some round
in which it was still present. -/
theorem diff_pruneLimit_subset (σ₀ : Measure (α × ℝ)) (h : α × ℝ → ℝ≥0∞)
    (st : α × ℝ → Q) (w : Q → ℝ≥0∞) (lam lam' : ℝ≥0∞) (E₀ : Set (α × ℝ)) :
    E₀ \ pruneLimit σ₀ h st w lam lam' E₀ ⊆
      {p | ∃ n, p ∈ pruneSeq σ₀ h st w lam lam' E₀ n ∧
          σ₀ (pruneSeq σ₀ h st w lam lam' E₀ n ∩ st ⁻¹' {st p}) < lam * w (st p)} ∪
      {p | ∃ n, p ∈ pruneSeq σ₀ h st w lam lam' E₀ n ∧
          sectionMass h (pruneSeq σ₀ h st w lam lam' E₀ n) p.1 < lam'} := by
  classical
  rintro p ⟨hp0, hpE⟩
  have hex : ∃ n, p ∉ pruneSeq σ₀ h st w lam lam' E₀ n := by
    simpa only [pruneLimit, mem_iInter, not_forall] using hpE
  have hn₀ : p ∉ pruneSeq σ₀ h st w lam lam' E₀ (Nat.find hex) := Nat.find_spec hex
  have hn₀0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hn₀
    exact hn₀ hp0
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn₀0
  have hpk : p ∈ pruneSeq σ₀ h st w lam lam' E₀ k := by
    by_contra hc
    have := Nat.find_min' hex hc
    omega
  rw [hk] at hn₀
  change p ∉ pruneStep σ₀ h st w lam lam' (pruneSeq σ₀ h st w lam lam' E₀ k) at hn₀
  simp only [pruneStep, mem_inter_iff, mem_ofPred_eq, not_and_or, not_le] at hn₀
  rcases hn₀ with (hn | hn) | hn
  · exact absurd hpk hn
  · exact Or.inl ⟨k, hpk, hn⟩
  · exact Or.inr ⟨k, hpk, hn⟩

/-- Each state is charged once, below its threshold. -/
theorem measure_light_states_le [Countable Q] (σ₀ : Measure (α × ℝ)) (h : α × ℝ → ℝ≥0∞)
    (st : α × ℝ → Q) (w : Q → ℝ≥0∞) (lam lam' : ℝ≥0∞) (E₀ : Set (α × ℝ)) :
    σ₀ {p | ∃ n, p ∈ pruneSeq σ₀ h st w lam lam' E₀ n ∧
        σ₀ (pruneSeq σ₀ h st w lam lam' E₀ n ∩ st ⁻¹' {st p}) < lam * w (st p)} ≤
      lam * ∑' q, w q := by
  classical
  set E := pruneSeq σ₀ h st w lam lam' E₀ with hEdef
  have hanti : Antitone E := antitone_pruneSeq σ₀ h st w lam lam' E₀
  let S : Q → Set (α × ℝ) := fun q =>
    {p | st p = q ∧ ∃ n, p ∈ E n ∧ σ₀ (E n ∩ st ⁻¹' {q}) < lam * w q}
  have hsub : {p | ∃ n, p ∈ E n ∧ σ₀ (E n ∩ st ⁻¹' {st p}) < lam * w (st p)} ⊆
      ⋃ q, S q := by
    intro p hp
    exact mem_iUnion.mpr ⟨st p, rfl, hp⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le S).trans ?_)
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun q => ?_
  by_cases hq : ∃ n, σ₀ (E n ∩ st ⁻¹' {q}) < lam * w q
  · have hsub' : S q ⊆ E (Nat.find hq) ∩ st ⁻¹' {q} := by
      rintro p ⟨hpq, n, hpn, hn⟩
      exact ⟨hanti (Nat.find_min' hq hn) hpn, hpq⟩
    exact (measure_mono hsub').trans (Nat.find_spec hq).le
  · have hS : S q = ∅ := by
      ext p
      simp only [S, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      rintro - ⟨n, -, hn⟩
      exact hq ⟨n, hn⟩
    rw [hS, measure_empty]
    exact zero_le

/-- Each trajectory is charged once, below its threshold density. -/
theorem measure_light_trajectories_le [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (m : Measure α) {h : α × ℝ → ℝ≥0∞}
    (hh : Measurable h) (σ₀ : Measure (α × ℝ)) {st : α × ℝ → Q} (hst : Measurable st)
    (w : Q → ℝ≥0∞) (lam lam' : ℝ≥0∞) {E₀ : Set (α × ℝ)} (hE₀ : MeasurableSet E₀) :
    (m.prod volume).withDensity h {p | ∃ n, p ∈ pruneSeq σ₀ h st w lam lam' E₀ n ∧
        sectionMass h (pruneSeq σ₀ h st w lam lam' E₀ n) p.1 < lam'} ≤
      lam' * m univ := by
  classical
  set E := pruneSeq σ₀ h st w lam lam' E₀ with hEdef
  have hanti : Antitone E := antitone_pruneSeq σ₀ h st w lam lam' E₀
  have hEm : ∀ n, MeasurableSet (E n) := measurableSet_pruneSeq σ₀ hh hst w lam lam' hE₀
  let D : ℕ → Set α := fun n =>
    {l | sectionMass h (E n) l < lam'} ∩ ⋂ k, ⋂ (_ : k < n), {l | lam' ≤ sectionMass h (E k) l}
  have hDm : ∀ n, MeasurableSet (D n) := by
    intro n
    refine (measurableSet_lt (measurable_sectionMass hh (hEm n)) measurable_const).inter ?_
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const (measurable_sectionMass hh (hEm k))
  have hDdisj : Pairwise (Function.onFun Disjoint D) := by
    intro n n' hnn'
    refine Set.disjoint_left.mpr fun l hl hl' => ?_
    rcases lt_or_gt_of_ne hnn' with hlt | hlt
    · have h1 : lam' ≤ sectionMass h (E n) l := by
        have := hl'.2
        simp only [mem_iInter] at this
        exact this n hlt
      exact absurd hl.1 (not_lt.mpr h1)
    · have h1 : lam' ≤ sectionMass h (E n') l := by
        have := hl.2
        simp only [mem_iInter] at this
        exact this n' hlt
      exact absurd hl'.1 (not_lt.mpr h1)
  have hsub : {p | ∃ n, p ∈ E n ∧ sectionMass h (E n) p.1 < lam'} ⊆
      ⋃ n, E n ∩ Prod.fst ⁻¹' D n := by
    rintro p ⟨n, hpn, hn⟩
    have hex : ∃ n, sectionMass h (E n) p.1 < lam' := ⟨n, hn⟩
    refine mem_iUnion.mpr ⟨Nat.find hex, hanti (Nat.find_min' hex hn) hpn, Nat.find_spec hex, ?_⟩
    simp only [mem_iInter]
    intro k hk
    exact not_lt.mp (Nat.find_min hex hk)
  calc
    _ ≤ (m.prod volume).withDensity h (⋃ n, E n ∩ Prod.fst ⁻¹' D n) := measure_mono hsub
    _ ≤ ∑' n, (m.prod volume).withDensity h (E n ∩ Prod.fst ⁻¹' D n) := measure_iUnion_le _
    _ = ∑' n, ∫⁻ l in D n, sectionMass h (E n) l ∂m := by
      congr 1
      funext n
      exact withDensity_inter_fst_preimage m hh (hEm n) (hDm n)
    _ ≤ ∑' n, lam' * m (D n) := by
      refine ENNReal.tsum_le_tsum fun n => ?_
      calc
        _ ≤ ∫⁻ _ in D n, lam' ∂m := setLIntegral_mono' (hDm n) fun l hl => hl.1.le
        _ = lam' * m (D n) := setLIntegral_const _ _
    _ = lam' * m (⋃ n, D n) := by rw [ENNReal.tsum_mul_left, measure_iUnion hDdisj hDm]
    _ ≤ lam' * m univ := by gcongr; exact subset_univ _

/-- The state floor survives in the limit, by continuity from above. -/
theorem state_floor_pruneLimit [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (σ₀ : Measure (α × ℝ)) {h : α × ℝ → ℝ≥0∞}
    (hh : Measurable h) {st : α × ℝ → Q} (hst : Measurable st) (w : Q → ℝ≥0∞)
    (lam lam' : ℝ≥0∞) {E₀ : Set (α × ℝ)} (hE₀ : MeasurableSet E₀) (hfin : σ₀ E₀ ≠ ∞)
    {p : α × ℝ} (hp : p ∈ pruneLimit σ₀ h st w lam lam' E₀) :
    lam * w (st p) ≤ σ₀ (pruneLimit σ₀ h st w lam lam' E₀ ∩ st ⁻¹' {st p}) := by
  set E := pruneSeq σ₀ h st w lam lam' E₀ with hEdef
  have hanti : Antitone E := antitone_pruneSeq σ₀ h st w lam lam' E₀
  have hEm : ∀ n, MeasurableSet (E n) := measurableSet_pruneSeq σ₀ hh hst w lam lam' hE₀
  have hE : ∀ n, p ∈ E n := mem_iInter.mp hp
  have hrw : pruneLimit σ₀ h st w lam lam' E₀ ∩ st ⁻¹' {st p} =
      ⋂ n, (E n ∩ st ⁻¹' {st p}) := by
    rw [pruneLimit, iInter_inter]
  rw [hrw, Antitone.measure_iInter]
  · exact le_iInf fun n => (hE (n + 1)).1.2
  · intro i j hij
    exact inter_subset_inter_left _ (hanti hij)
  · intro n
    exact ((hEm n).inter (hst (measurableSet_singleton _))).nullMeasurableSet
  · exact ⟨0, ne_top_of_le_ne_top hfin (measure_mono inter_subset_left)⟩

/-- The trajectory floor survives in the limit, by monotone convergence. -/
theorem trajectory_floor_pruneLimit [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (σ₀ : Measure (α × ℝ)) {h : α × ℝ → ℝ≥0∞}
    (hh : Measurable h) {st : α × ℝ → Q} (hst : Measurable st) (w : Q → ℝ≥0∞)
    (lam lam' : ℝ≥0∞) {E₀ : Set (α × ℝ)} (hE₀ : MeasurableSet E₀)
    (hsec : ∀ l, sectionMass h E₀ l ≠ ∞)
    {p : α × ℝ} (hp : p ∈ pruneLimit σ₀ h st w lam lam' E₀) :
    lam' ≤ sectionMass h (pruneLimit σ₀ h st w lam lam' E₀) p.1 := by
  set E := pruneSeq σ₀ h st w lam lam' E₀ with hEdef
  have hanti : Antitone E := antitone_pruneSeq σ₀ h st w lam lam' E₀
  have hEm : ∀ n, MeasurableSet (E n) := measurableSet_pruneSeq σ₀ hh hst w lam lam' hE₀
  have hE : ∀ n, p ∈ E n := mem_iInter.mp hp
  have hind : ∀ τ : ℝ, (pruneLimit σ₀ h st w lam lam' E₀).indicator h (p.1, τ) =
      ⨅ n, (E n).indicator h (p.1, τ) := by
    intro τ
    by_cases hτ : (p.1, τ) ∈ pruneLimit σ₀ h st w lam lam' E₀
    · rw [indicator_of_mem hτ]
      have : ∀ n, (E n).indicator h (p.1, τ) = h (p.1, τ) := fun n =>
        indicator_of_mem (mem_iInter.mp hτ n) _
      simp only [this, iInf_const]
    · rw [indicator_of_notMem hτ]
      obtain ⟨n, hn⟩ : ∃ n, (p.1, τ) ∉ E n := by
        simpa only [pruneLimit, mem_iInter, not_forall] using hτ
      exact le_antisymm (zero_le) ((iInf_le _ n).trans (indicator_of_notMem hn _).le)
  have hsm : sectionMass h (pruneLimit σ₀ h st w lam lam' E₀) p.1 =
      ∫⁻ τ, ⨅ n, (E n).indicator h (p.1, τ) := by
    unfold sectionMass
    exact lintegral_congr fun τ => hind τ
  rw [hsm, lintegral_iInf]
  · exact le_iInf fun n => (hE (n + 1)).2
  · intro n
    exact (hh.indicator (hEm n)).comp measurable_prodMk_left
  · intro i j hij τ
    exact indicator_le_indicator_of_subset (hanti hij) (fun _ => zero_le) _
  · exact hsec p.1

/-- **Simultaneous floors.** One measurable restriction keeps, for the final
set, the state floors against the fixed reference weights and the trajectory
floors against the fixed reference measure; the loss is the sum of the two
budgets. -/
theorem exists_simultaneous_floors [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (m : Measure α) {h : α × ℝ → ℝ≥0∞}
    (hh : Measurable h) {E₀ : Set (α × ℝ)} (hE₀ : MeasurableSet E₀)
    (hsec : ∀ l, sectionMass h E₀ l ≠ ∞)
    (hfin : (m.prod volume).withDensity h E₀ ≠ ∞)
    {st : α × ℝ → Q} (hst : Measurable st) (w : Q → ℝ≥0∞) (lam lam' : ℝ≥0∞) :
    ∃ E : Set (α × ℝ), MeasurableSet E ∧ E ⊆ E₀ ∧
      (m.prod volume).withDensity h E₀ ≤
        (m.prod volume).withDensity h E + (lam * ∑' q, w q + lam' * m univ) ∧
      (∀ p ∈ E, lam * w (st p) ≤ (m.prod volume).withDensity h (E ∩ st ⁻¹' {st p})) ∧
      (∀ p ∈ E, lam' ≤ sectionMass h E p.1) := by
  set σ₀ := (m.prod volume).withDensity h with hσ₀
  refine ⟨pruneLimit σ₀ h st w lam lam' E₀, ?_, ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.iInter (measurableSet_pruneSeq σ₀ hh hst w lam lam' hE₀)
  · exact iInter_subset _ 0
  · calc
      σ₀ E₀ ≤ σ₀ (E₀ ∩ pruneLimit σ₀ h st w lam lam' E₀) +
          σ₀ (E₀ \ pruneLimit σ₀ h st w lam lam' E₀) := measure_le_inter_add_sdiff _ _ _
      _ ≤ σ₀ (pruneLimit σ₀ h st w lam lam' E₀) + (lam * ∑' q, w q + lam' * m univ) := by
        gcongr
        · exact inter_subset_right
        · refine (measure_mono (diff_pruneLimit_subset σ₀ h st w lam lam' E₀)).trans ?_
          refine (measure_union_le _ _).trans ?_
          gcongr
          · exact measure_light_states_le σ₀ h st w lam lam' E₀
          · exact measure_light_trajectories_le m hh σ₀ hst w lam lam' hE₀
  · intro p hp
    exact state_floor_pruneLimit σ₀ hh hst w lam lam' hE₀ hfin hp
  · intro p hp
    exact trajectory_floor_pruneLimit σ₀ hh hst w lam lam' hE₀ hsec hp

end Limit

section Corollaries

/-- The trajectory marginal of a restriction has the time-section masses as
its density against the reference measure. -/
theorem map_fst_restrict_withDensity (m : Measure α) {h : α × ℝ → ℝ≥0∞}
    (hh : Measurable h) {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    (((m.prod volume).withDensity h).restrict E).map Prod.fst =
      m.withDensity (sectionMass h E) := by
  ext D hD
  rw [Measure.map_apply measurable_fst hD, Measure.restrict_apply (measurable_fst hD),
    withDensity_apply _ hD, inter_comm]
  exact withDensity_inter_fst_preimage m hh hE hD

/-- **Final time ceiling.** A product ceiling against the reference, divided
by the final trajectory floor, gives a product ceiling against the restricted
law's own trajectory marginal. -/
theorem restrict_le_smul_marginal_prod (m : Measure α) {h : α × ℝ → ℝ≥0∞}
    (hh : Measurable h) {C₀ : ℝ≥0∞}
    (hC : (m.prod volume).withDensity h ≤ C₀ • m.prod volume)
    {E : Set (α × ℝ)} (hE : MeasurableSet E) {lam' : ℝ≥0∞} (hl0 : lam' ≠ 0)
    (hltop : lam' ≠ ∞) (hfloor : ∀ p ∈ E, lam' ≤ sectionMass h E p.1) :
    ((m.prod volume).withDensity h).restrict E ≤
      (C₀ / lam') • ((((m.prod volume).withDensity h).restrict E).map Prod.fst).prod
        volume := by
  rw [map_fst_restrict_withDensity m hh hE, Measure.le_iff]
  intro S hS
  rw [Measure.restrict_apply hS, Measure.smul_apply, smul_eq_mul, Measure.prod_apply hS,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_sectionMass hh hE)
      (measurable_measure_prodMk_left hS),
    ← lintegral_const_mul _ ((measurable_sectionMass hh hE).mul
      (measurable_measure_prodMk_left hS))]
  calc
    ((m.prod volume).withDensity h) (S ∩ E) ≤ (C₀ • m.prod volume) (S ∩ E) := hC _
    _ = ∫⁻ l, C₀ * volume (Prod.mk l ⁻¹' (S ∩ E)) ∂m := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.prod_apply (hS.inter hE),
        lintegral_const_mul _ (measurable_measure_prodMk_left (hS.inter hE))]
    _ ≤ _ := by
      refine lintegral_mono fun l => ?_
      simp only [Pi.mul_apply]
      by_cases hne : (Prod.mk l ⁻¹' (S ∩ E)).Nonempty
      · obtain ⟨τ, hτ⟩ := hne
        have hfl : lam' ≤ sectionMass h E l := hfloor (l, τ) hτ.2
        calc
          C₀ * volume (Prod.mk l ⁻¹' (S ∩ E)) ≤ C₀ * volume (Prod.mk l ⁻¹' S) := by
            gcongr
            exact preimage_mono inter_subset_left
          _ = C₀ / lam' * lam' * volume (Prod.mk l ⁻¹' S) := by
            rw [ENNReal.div_mul_cancel hl0 hltop]
          _ ≤ C₀ / lam' * (sectionMass h E l * volume (Prod.mk l ⁻¹' S)) := by
            rw [← mul_assoc]
            gcongr
      · rw [not_nonempty_iff_eq_empty.mp hne, measure_empty, mul_zero]
        exact zero_le

/-- **Final palette ceiling.** A state numerator bounded by its reference
weight becomes a ceiling relative to the state's mass in the restriction, once
every retained state has its floor. -/
theorem restrict_state_cap [MeasurableSpace Q] [MeasurableSingletonClass Q]
    {σ₀ : Measure (α × ℝ)} {E : Set (α × ℝ)} {st : α × ℝ → Q} (hst : Measurable st)
    {w : Q → ℝ≥0∞} {lam : ℝ≥0∞} (hl0 : lam ≠ 0) (hltop : lam ≠ ∞)
    (hfloor : ∀ p ∈ E, lam * w (st p) ≤ σ₀ (E ∩ st ⁻¹' {st p}))
    (q : Q) (X : Set (α × ℝ)) (C c : ℝ≥0∞)
    (hcap : σ₀ {p | st p = q ∧ p ∈ X} ≤ C * w q * c) :
    (σ₀.restrict E) {p | st p = q ∧ p ∈ X} ≤ C / lam * (σ₀.restrict E) (st ⁻¹' {q}) * c := by
  have hmass : (σ₀.restrict E) (st ⁻¹' {q}) = σ₀ (E ∩ st ⁻¹' {q}) := by
    rw [Measure.restrict_apply (hst (measurableSet_singleton q)), inter_comm]
  by_cases hq : (E ∩ st ⁻¹' {q}).Nonempty
  · obtain ⟨p, hpE, hpq⟩ := hq
    have hfl := hfloor p hpE
    rw [show st p = q from hpq] at hfl
    calc
      (σ₀.restrict E) {p | st p = q ∧ p ∈ X} ≤ σ₀ {p | st p = q ∧ p ∈ X} :=
        Measure.restrict_le_self _
      _ ≤ C * w q * c := hcap
      _ = C / lam * (lam * w q) * c := by
        rw [← mul_assoc (C / lam), ENNReal.div_mul_cancel hl0 hltop]
      _ ≤ C / lam * (σ₀.restrict E) (st ⁻¹' {q}) * c := by
        rw [hmass]
        gcongr
  · have h0 : (σ₀.restrict E) (st ⁻¹' {q}) = 0 := by
      rw [hmass, not_nonempty_iff_eq_empty.mp hq, measure_empty]
    calc
      (σ₀.restrict E) {p | st p = q ∧ p ∈ X} ≤ (σ₀.restrict E) (st ⁻¹' {q}) :=
        measure_mono fun p hp => hp.1
      _ = 0 := h0
      _ ≤ _ := zero_le

/-- A finite law dominated by a constant multiple of a product reference has a
measurable density bounded everywhere by that constant. -/
theorem exists_bounded_density (m : Measure α) [SigmaFinite m]
    (σ₀ : Measure (α × ℝ)) [IsFiniteMeasure σ₀] {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (hle : σ₀ ≤ C₀ • m.prod volume) :
    ∃ h : α × ℝ → ℝ≥0∞, Measurable h ∧ (∀ p, h p ≤ C₀) ∧
      (m.prod volume).withDensity h = σ₀ := by
  by_cases hC0 : C₀ = 0
  · refine ⟨fun _ => 0, measurable_const, fun _ => zero_le, ?_⟩
    rw [hC0, zero_smul] at hle
    have h0 : σ₀ = 0 := by
      ext s hs
      simpa using hle s
    rw [h0]
    exact withDensity_zero
  set g := σ₀.rnDeriv (m.prod volume)
  have hac : σ₀ ≪ m.prod volume := Measure.absolutelyContinuous_of_le_smul hle
  have hg : (m.prod volume).withDensity g = σ₀ := Measure.withDensity_rnDeriv_eq _ _ hac
  have hle' : C₀⁻¹ • σ₀ ≤ m.prod volume := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul]
    calc
      C₀⁻¹ * σ₀ s ≤ C₀⁻¹ * (C₀ • m.prod volume) s := mul_le_mul_right (hle s) _
      _ = (m.prod volume) s := by
        rw [Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hC0 hC₀,
          one_mul]
  have h1 : (C₀⁻¹ • σ₀).rnDeriv (m.prod volume) ≤ᵐ[m.prod volume] 1 :=
    Measure.rnDeriv_le_one_of_le hle'
  have h2 : (C₀⁻¹ • σ₀).rnDeriv (m.prod volume) =ᵐ[m.prod volume] C₀⁻¹ • g :=
    Measure.rnDeriv_smul_left_of_ne_top _ _ (ENNReal.inv_ne_top.mpr hC0)
  have hgle : ∀ᵐ p ∂(m.prod volume), g p ≤ C₀ := by
    filter_upwards [h1, h2] with p hp1 hp2
    rw [hp2] at hp1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at hp1
    calc
      g p = C₀ * (C₀⁻¹ * g p) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hC₀, one_mul]
      _ ≤ C₀ * 1 := by gcongr
      _ = C₀ := mul_one _
  refine ⟨fun p => min (g p) C₀, (Measure.measurable_rnDeriv _ _).min measurable_const,
    fun p => min_le_right _ _, ?_⟩
  rw [← hg]
  apply withDensity_congr_ae
  filter_upwards [hgle] with p hp
  exact min_eq_left hp

omit [MeasurableSpace α] in
/-- Bounded densities have finite time sections over a set of finite time
length. -/
theorem sectionMass_le_of_subset {h : α × ℝ → ℝ≥0∞} {C₀ : ℝ≥0∞} (hhC : ∀ p, h p ≤ C₀)
    {E₀ : Set (α × ℝ)} {T : Set ℝ} (hT : MeasurableSet T) (hE₀T : E₀ ⊆ univ ×ˢ T) (l : α) :
    sectionMass h E₀ l ≤ C₀ * volume T := by
  unfold sectionMass
  calc
    ∫⁻ τ, E₀.indicator h (l, τ) ≤ ∫⁻ τ, T.indicator (fun _ => C₀) τ := by
      refine lintegral_mono fun τ => ?_
      by_cases hp : (l, τ) ∈ E₀
      · rw [indicator_of_mem hp, indicator_of_mem (hE₀T hp).2]
        exact hhC _
      · rw [indicator_of_notMem hp]
        exact zero_le
    _ = C₀ * volume T := lintegral_indicator_const hT C₀

end Corollaries

section Packaged

/-- **Prepared law.** From a finite law with a bounded product density against a
finite reference, supported in a set of bounded times, one measurable
restriction and one normalization give a probability law with

* the per-set transport `σ ≤ (σ₀ E)⁻¹ • σ₀` to the ORIGINAL law,
* the time ceiling `C₀ / lam'` against its OWN trajectory marginal,
* the palette ceiling `C / lam` relative to its OWN state masses, for every
  state numerator bounded by `C` times the state's reference weight.

The lost mass is at most `lam * ∑ w + lam' * m univ`. -/
theorem exists_pruned_law [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (m : Measure α) [IsFiniteMeasure m] (σ₀ : Measure (α × ℝ)) [IsFiniteMeasure σ₀]
    {C₀ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hle : σ₀ ≤ C₀ • m.prod volume)
    {E₀ : Set (α × ℝ)} (hE₀ : MeasurableSet E₀) {T : Set ℝ} (hT : MeasurableSet T)
    (hTfin : volume T ≠ ∞) (hE₀T : E₀ ⊆ univ ×ˢ T)
    {st : α × ℝ → Q} (hst : Measurable st) (w : Q → ℝ≥0∞) {lam lam' : ℝ≥0∞}
    (hl0 : lam ≠ 0) (hltop : lam ≠ ∞) (hl0' : lam' ≠ 0) (hltop' : lam' ≠ ∞)
    (hbudget : lam * ∑' q, w q + lam' * m univ < σ₀ E₀) :
    ∃ E : Set (α × ℝ), MeasurableSet E ∧ E ⊆ E₀ ∧
      σ₀ E₀ ≤ σ₀ E + (lam * ∑' q, w q + lam' * m univ) ∧ σ₀ E ≠ 0 ∧
      IsProbabilityMeasure ((σ₀ E)⁻¹ • σ₀.restrict E) ∧
      ((σ₀ E)⁻¹ • σ₀.restrict E) Eᶜ = 0 ∧
      (σ₀ E)⁻¹ • σ₀.restrict E ≤ (σ₀ E)⁻¹ • σ₀ ∧
      (σ₀ E)⁻¹ • σ₀.restrict E ≤
        (C₀ / lam') • (((σ₀ E)⁻¹ • σ₀.restrict E).map Prod.fst).prod volume ∧
      ∀ (q : Q) (X : Set (α × ℝ)) (C c : ℝ≥0∞),
        σ₀ {p | st p = q ∧ p ∈ X} ≤ C * w q * c →
        ((σ₀ E)⁻¹ • σ₀.restrict E) {p | st p = q ∧ p ∈ X} ≤
          C / lam * ((σ₀ E)⁻¹ • σ₀.restrict E) (st ⁻¹' {q}) * c := by
  obtain ⟨h, hh, hhC, hσ⟩ := exists_bounded_density m σ₀ hC₀ hle
  have hsec : ∀ l, sectionMass h E₀ l ≠ ∞ := fun l =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hC₀ hTfin) (sectionMass_le_of_subset hhC hT hE₀T l)
  have hfin : (m.prod volume).withDensity h E₀ ≠ ∞ := by rw [hσ]; exact measure_ne_top _ _
  obtain ⟨E, hEm, hEsub, hmass, hstate, htraj⟩ :=
    exists_simultaneous_floors m hh hE₀ hsec hfin hst w lam lam'
  rw [hσ] at hmass hstate
  have hE0 : σ₀ E ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hmass
    exact absurd hbudget (not_lt.mpr hmass)
  have hEtop : σ₀ E ≠ ∞ := measure_ne_top _ _
  set a := (σ₀ E)⁻¹ with ha
  have hatop : a ≠ ∞ := ENNReal.inv_ne_top.mpr hE0
  have htime : σ₀.restrict E ≤ (C₀ / lam') • ((σ₀.restrict E).map Prod.fst).prod volume := by
    have := restrict_le_smul_marginal_prod m hh (hσ ▸ hle) hEm hl0' hltop' htraj
    rwa [hσ] at this
  refine ⟨E, hEm, hEsub, hmass, hE0, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hE0 hEtop]
  · rw [Measure.smul_apply, Measure.restrict_apply hEm.compl, compl_inter_self, measure_empty,
      smul_zero]
  · rw [Measure.le_iff]
    intro S hS
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    gcongr
    exact Measure.restrict_le_self
  · rw [Measure.map_smul a measurable_fst.aemeasurable, Measure.prod_smul_left, Measure.le_iff]
    intro S hS
    rw [Measure.smul_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    calc
      a * (σ₀.restrict E) S ≤ a * ((C₀ / lam') •
          ((σ₀.restrict E).map Prod.fst).prod volume) S := mul_le_mul_right (htime S) _
      _ = C₀ / lam' * (a * (((σ₀.restrict E).map Prod.fst).prod volume) S) := by
        rw [Measure.smul_apply, smul_eq_mul, mul_left_comm]
  · intro q X C c hcap
    have hst' := restrict_state_cap hst hl0 hltop hstate q X C c hcap
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    calc
      a * (σ₀.restrict E) {p | st p = q ∧ p ∈ X} ≤
          a * (C / lam * (σ₀.restrict E) (st ⁻¹' {q}) * c) := by gcongr
      _ = C / lam * (a * (σ₀.restrict E) (st ⁻¹' {q})) * c := by ring

end Packaged

end

end Submission.Obl.k4_critical_switching_state_preparation.Pruning
