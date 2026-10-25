import Submission.Obl.k4_horizontal_three_traversal_spreading.Law
import Submission.Obl.k4_horizontal_three_traversal_spreading.Discretize
import Submission.Obl.k4_matching_abstract_switching_mixture.Finite

namespace Submission.Obl.k4_horizontal_three_traversal_spreading

open Set MeasureTheory Finset
open scoped ENNReal
open Discretize
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

noncomputable section

namespace Law

variable {α : Type} [MeasurableSpace α] (D : Law α)

def codeRange : Finset ℤ := Finset.Icc (-(⌈D.B / D.h⌉ + 1)) (⌈D.B / D.h⌉ + 1)

def palSet : Finset ℤ := D.codeRange.filter (fun z => |((z : ℝ) + 1 / 2) * D.h| ≤ D.B + D.h)

def armSet : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (![D.codeRange, D.codeRange, D.palSet, D.F.image Prod.fst] : Fin 4 → Finset ℤ)

def code : α → Fin 4 → ℤ := armCode D.h D.Z0 D.Y0 D.vb D.bin

abbrev Event (n T : ℕ) := Fin n × D.armSet × Fin T

def pre {n T : ℕ} (e : D.Event n T) : Set (α × ℝ) :=
  {p | D.state p = e.1.val ∧ D.code p.1 = e.2.1.val ∧ ⌊(T : ℝ) * p.2⌋ = (e.2.2.val : ℤ)}

def weight {n T : ℕ} (e : D.Event n T) : ℝ := (D.σ (D.pre e)).toReal

def mass (n : ℕ) : ℝ := (D.σ {p | D.state p < n}).toReal

def prior (a : D.armSet) : ℝ :=
  ((D.σ.map Prod.fst) {l | D.code l = a.val}).toReal

def palOf (a : D.armSet) : D.palSet :=
  ⟨a.val 2, (Fintype.mem_piFinset.mp a.property) 2⟩

def binOf (a : D.armSet) : ℤ := a.val 3

def velocity (z : D.palSet) : ℝ := ((z.val : ℝ) + 1 / 2) * D.h

def center {T : ℕ} (t : Fin T) : ℝ := ((t.val : ℝ) + 1 / 2) / T

def fine {n T : ℕ} (e : D.Event n T) : Fin n × ℤ := (e.1, D.binOf e.2.1)

/-- The state key also records the invariant bin; this only changes null
pieces, and gives an invariant on every event, including zero-mass ones. -/
def switch (n T : ℕ) :
    SwitchData (D.Event n T) (Fin n × ℤ) Unit D.armSet Unit D.palSet (Fin T) where
  P e := D.weight e / D.mass n
  fine := D.fine
  coarse _ := ()
  Z e := D.palOf e.2.1
  arm e _ := e.2.1
  ival _ := ()
  cell e := e.2.2
  Ψ z _ _ := D.velocity z
  θ := 0

theorem measurable_code (hD : D.Valid) : Measurable D.code :=
  measurable_armCode (D.meas_Z0 hD) (D.meas_Y0 hD) (D.meas_vb hD) hD.meas_bin

theorem measurableSet_pre (hD : D.Valid) {n T : ℕ} (e : D.Event n T) :
    MeasurableSet (D.pre e) := by
  exact (hD.meas_state (measurableSet_singleton _)).inter
    (((D.measurable_code hD).comp measurable_fst) (measurableSet_singleton _) |>.inter
      ((Int.measurable_floor.comp (measurable_snd.const_mul (T : ℝ))) (measurableSet_singleton _)))

theorem pre_disjoint {n T : ℕ} (e e' : D.Event n T) (hne : e ≠ e') :
    Disjoint (D.pre e) (D.pre e') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  apply hne
  exact Prod.ext (Fin.ext (hp.1.symm.trans hp'.1))
    (Prod.ext (Subtype.ext (hp.2.1.symm.trans hp'.2.1))
      (Fin.ext (by exact_mod_cast hp.2.2.symm.trans hp'.2.2)))

/-- A bound on a real number gives a finite range for its floor code. -/
theorem floor_mem_codeRange {x : ℝ} (hD : D.Valid) (hx : |x| ≤ D.B) :
    ⌊x / D.h⌋ ∈ D.codeRange := by
  rw [codeRange, Finset.mem_Icc]
  rw [abs_le] at hx
  constructor
  · rw [Int.le_floor]
    have h1 : -(D.B / D.h) ≤ x / D.h := by
      rw [neg_div']; exact div_le_div_of_nonneg_right hx.1 hD.h_pos.le
    have h2 := Int.le_ceil (D.B / D.h)
    push_cast
    linarith
  · have h1 : x / D.h ≤ D.B / D.h := div_le_div_of_nonneg_right hx.2 hD.h_pos.le
    have h2 : ⌊x / D.h⌋ ≤ ⌈D.B / D.h⌉ :=
      Int.floor_le_ceil (x / D.h) |>.trans (Int.ceil_mono h1)
    omega

theorem code_mem (hD : D.Valid) {p : α × ℝ} (hp : p ∈ D.G)
    (hF : (D.bin p.1, fun i => ⌊D.x p.1 p.2 i / D.ω⌋) ∈ D.F) :
    D.code p.1 ∈ D.armSet := by
  rw [armSet, Fintype.mem_piFinset]
  intro i
  fin_cases i
  · exact D.floor_mem_codeRange hD (D.coeff_bounds hD hp).1
  · exact D.floor_mem_codeRange hD (D.coeff_bounds hD hp).2
  · change D.vb p.1 ∈ D.palSet
    rw [palSet, Finset.mem_filter]
    refine ⟨D.floor_mem_codeRange hD (hD.geometry p hp).2.1, ?_⟩
    have hc : |((D.vb p.1 : ℝ) + 1 / 2) * D.h - D.vel p.1| ≤ D.h / 2 := by
      rw [abs_sub_comm]; exact abs_sub_floor_center hD.h_pos
    calc
      _ ≤ |((D.vb p.1 : ℝ) + 1 / 2) * D.h - D.vel p.1| + |D.vel p.1| :=
        by have hh := abs_sub_abs_le_abs_sub (((D.vb p.1 : ℝ) + 1 / 2) * D.h) (D.vel p.1); linarith
      _ ≤ D.h / 2 + D.B := add_le_add hc (hD.geometry p hp).2.1
      _ ≤ _ := by linarith [hD.h_pos]
  · exact Finset.mem_image.mpr ⟨_, hF, rfl⟩

def Good (p : α × ℝ) : Prop := p ∈ D.G ∧ p.2 < 1 ∧
  (D.bin p.1, fun i => ⌊D.x p.1 p.2 i / D.ω⌋) ∈ D.F

theorem ae_good (hD : D.Valid) : ∀ᵐ p ∂D.σ, D.Good p := by
  filter_upwards [D.ae_mem_G hD, D.ae_time_ne_one hD, hD.support] with p hp hne hF
  exact ⟨hp, lt_of_le_of_ne (hD.geometry p hp).1.2 hne, hF⟩

theorem exists_event (hD : D.Valid) {n T : ℕ} (hT : 0 < T) {p : α × ℝ}
    (hp : D.Good p) (hn : D.state p < n) : ∃ e : D.Event n T, p ∈ D.pre e := by
  have ht0 : 0 ≤ ⌊(T : ℝ) * p.2⌋ := Int.floor_nonneg.mpr
    (mul_nonneg (Nat.cast_nonneg _) (hD.geometry p hp.1).1.1)
  have htT : ⌊(T : ℝ) * p.2⌋ < (T : ℤ) := by
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    have hlt : ((⌊(T : ℝ) * p.2⌋ : ℤ) : ℝ) < T :=
      lt_of_le_of_lt (Int.floor_le _) (by nlinarith [hp.2.1])
    exact_mod_cast hlt
  refine ⟨(⟨D.state p, hn⟩, ⟨D.code p.1, D.code_mem hD hp.1 hp.2.2⟩,
      ⟨⌊(T : ℝ) * p.2⌋.toNat, ?_⟩), rfl, rfl, ?_⟩
  · exact_mod_cast (Int.toNat_lt_toNat (by exact_mod_cast hT) |>.mpr htT)
  · exact (Int.toNat_of_nonneg ht0).symm

/-- Finite event masses retain the original measure units. -/
theorem sum_weight (hD : D.Valid) {n T : ℕ} (hT : 0 < T) :
    ∑ e : D.Event n T, D.weight e = D.mass n := by
  letI := hD.prob_σ
  unfold weight mass
  rw [sum_toReal_measure_eq D.σ Finset.univ D.pre (D.measurableSet_pre hD)
    (fun e _ e' _ hne => D.pre_disjoint e e' hne)]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [D.ae_good hD] with p hp
  apply propext
  simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and, mem_ofPred_eq]
  constructor
  · rintro ⟨e, he⟩
    exact he.1 ▸ e.1.isLt
  · exact D.exists_event hD hT hp

/-- A positive event has a representative satisfying all original geometric
and occupied-cell statements. -/
theorem exists_good_of_weight_pos (hD : D.Valid) {n T : ℕ} {e : D.Event n T}
    (he : 0 < D.weight e) : ∃ p ∈ D.pre e, D.Good p := by
  have hpos : 0 < D.σ (D.pre e) := ENNReal.toReal_pos_iff.mp he |>.1
  by_contra hn
  have hsub : D.pre e ⊆ {p | ¬D.Good p} := by
    intro p hp hg
    exact hn ⟨p, hp, hg⟩
  have hz : D.σ {p | ¬D.Good p} = 0 := ae_iff.mp (D.ae_good hD)
  exact (ne_of_gt hpos) (measure_mono_null hsub hz)

/-- Actual representatives avoid enlarging the occupied-cell table. -/
def point (hD : D.Valid) {n T : ℕ} (e : D.Event n T) : Fin 3 → ℝ :=
  if he : 0 < D.weight e then
    let p := Classical.choose (D.exists_good_of_weight_pos hD he)
    D.x p.1 p.2
  else 0

theorem point_spec (hD : D.Valid) {n T : ℕ} {e : D.Event n T} (he : 0 < D.weight e) :
    ∃ p ∈ D.pre e, D.Good p ∧ D.point hD e = D.x p.1 p.2 := by
  have hp := Classical.choose_spec (D.exists_good_of_weight_pos hD he)
  exact ⟨_, hp.1, hp.2, by simp only [point, dif_pos he]⟩

theorem pre_bin {n T : ℕ} {e : D.Event n T} {p : α × ℝ} (hp : p ∈ D.pre e) :
    D.bin p.1 = D.binOf e.2.1 := congrFun hp.2.1 3

theorem pre_palette {n T : ℕ} {e : D.Event n T} {p : α × ℝ} (hp : p ∈ D.pre e) :
    D.vb p.1 = (D.palOf e.2.1).val := congrFun hp.2.1 2

/-- The finite partition computes every test that is constant on its events. -/
theorem sum_weight_test_eq (hD : D.Valid) {n T : ℕ} (hT : 0 < T)
    (test : D.Event n T → Prop) [DecidablePred test] (pred : α × ℝ → Prop)
    (hcompat : ∀ e p, p ∈ D.pre e → (test e ↔ pred p))
    (hinside : ∀ p, pred p → D.state p < n) :
    ∑ e ∈ Finset.univ.filter test, D.weight e = (D.σ {p | pred p}).toReal := by
  letI := hD.prob_σ
  classical
  unfold weight
  rw [sum_toReal_measure_eq D.σ _ D.pre (D.measurableSet_pre hD)
    (fun e _ e' _ hne => D.pre_disjoint e e' hne)]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [D.ae_good hD] with p hp
  apply propext
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_prop, mem_ofPred_eq]
  constructor
  · rintro ⟨e, ht, he⟩
    exact (hcompat e p he).mp ht
  · intro ht
    obtain ⟨e, he⟩ := D.exists_event hD hT hp (hinside p ht)
    exact ⟨e, (hcompat e p he).mpr ht, he⟩

/-- One-sided transfer needs no cover assertion for the target event. -/
theorem sum_weight_test_le (hD : D.Valid) {n T : ℕ}
    (test : D.Event n T → Prop) [DecidablePred test] (pred : α × ℝ → Prop)
    (hcompat : ∀ e p, test e → p ∈ D.pre e → pred p) :
    ∑ e ∈ Finset.univ.filter test, D.weight e ≤ (D.σ {p | pred p}).toReal := by
  letI := hD.prob_σ
  classical
  unfold weight
  rw [sum_toReal_measure_eq D.σ _ D.pre (D.measurableSet_pre hD)
    (fun e _ e' _ hne => D.pre_disjoint e e' hne)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro p hp
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_prop] at hp
  obtain ⟨e, ht, he⟩ := hp
  exact hcompat e p ht he

theorem fine_weight (hD : D.Valid) {n T : ℕ} (hT : 0 < T) (q : Fin n) (j : ℤ) :
    (∑ e ∈ Finset.univ.filter (fun e : D.Event n T => D.fine e = (q, j)), D.weight e) =
      (D.σ {p | D.state p = q.val ∧ D.bin p.1 = j}).toReal := by
  apply D.sum_weight_test_eq hD hT
  · intro e p hp
    constructor
    · intro he
      exact ⟨hp.1.trans (congrArg (fun k : Fin n × ℤ => k.1.val) he),
        (D.pre_bin hp).trans (congrArg Prod.snd he)⟩
    · rintro ⟨hq, hj⟩
      exact Prod.ext (Fin.ext (hp.1.symm.trans hq)) ((D.pre_bin hp).symm.trans hj)
  · intro p hp
    exact hp.1 ▸ q.isLt

theorem fine_palette_weight_le (hD : D.Valid) {n T : ℕ} (q : Fin n) (j : ℤ)
    (z : D.palSet) :
    (∑ e ∈ Finset.univ.filter (fun e : D.Event n T =>
      D.fine e = (q, j) ∧ D.palOf e.2.1 = z), D.weight e) ≤
        D.L * (D.σ {p | D.state p = q.val ∧ D.bin p.1 = j}).toReal * D.palMass z.val := by
  letI := hD.prob_σ
  letI := hD.prob_π
  have hsum := D.sum_weight_test_le hD
    (fun e : D.Event n T => D.fine e = (q, j) ∧ D.palOf e.2.1 = z)
    (fun p => D.state p = q.val ∧ D.bin p.1 = j ∧ D.vb p.1 = z.val) (by
      intro e p he hp
      exact ⟨hp.1.trans (congrArg (fun k : Fin n × ℤ => k.1.val) he.1),
        (D.pre_bin hp).trans (congrArg Prod.snd he.1),
        (D.pre_palette hp).trans (congrArg Subtype.val he.2)⟩)
  refine hsum.trans ?_
  have hcap := ENNReal.toReal_mono (by finiteness) (D.state_bin_palette hD q.val j z.val)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.L_nonneg, palMass] using hcap

theorem normalized_condKey {Ω Q : Type*} [Fintype Ω] [DecidableEq Q]
    (w : Ω → ℝ) (key : Ω → Q) {M : ℝ} (hM : M ≠ 0) (e er : Ω) :
    condKey (fun e => w e / M) key e er = condKey w key e er := by
  have hm : atomMass (fun e => w e / M) key e = atomMass w key e / M := by
    simp only [atomMass, fiberMass, Finset.sum_div]
  simp only [condKey, hm]
  split_ifs
  · exact div_div_div_cancel_right₀ hM _ _
  · rfl

theorem conditional_palette_of_joint {Ω Q Z : Type*} [Fintype Ω]
    [DecidableEq Q] [DecidableEq Z] (w : Ω → ℝ) (key : Ω → Q) (pal : Ω → Z)
    (hw : ∀ e, 0 ≤ w e) (c : Z → ℝ) (hc : ∀ z, 0 ≤ c z)
    (hcap : ∀ e z, (∑ er ∈ Finset.univ.filter (fun er => key er = key e ∧ pal er = z), w er) ≤
      c z * atomMass w key e) (e : Ω) (z : Z) :
    (∑ er ∈ Finset.univ.filter (fun er => pal er = z), condKey w key e er) ≤ c z := by
  classical
  have hs : (∑ er ∈ Finset.univ.filter (fun er => pal er = z), condKey w key e er) =
      (∑ er ∈ Finset.univ.filter (fun er => key er = key e ∧ pal er = z), w er) /
        atomMass w key e := by
    rw [Finset.sum_div]
    simp only [Finset.sum_filter, condKey]
    apply Finset.sum_congr rfl
    intro er _
    by_cases hk : key er = key e <;> by_cases hz : pal er = z <;> simp [hk, hz]
  rw [hs]
  by_cases hzero : atomMass w key e = 0
  · rw [hzero, div_zero]
    exact hc z
  · have hpos : 0 < atomMass w key e :=
      lt_of_le_of_ne (fiberMass_nonneg hw key (key e)) (Ne.symm hzero)
    exact (div_le_iff₀ hpos).mpr (hcap e z)

theorem switch_palette (hD : D.Valid) {n T : ℕ} (hT : 0 < T)
    (hM : 0 < D.mass n) (e : D.Event n T) (z : D.palSet) :
    (∑ er ∈ Finset.univ.filter (fun er => (D.switch n T).Z er = z),
      condKey (D.switch n T).P (D.switch n T).fine e er) ≤ D.L * D.palMass z.val := by
  change (∑ er ∈ Finset.univ.filter (fun er : D.Event n T => D.palOf er.2.1 = z),
      condKey (fun er => D.weight er / D.mass n) D.fine e er) ≤ _
  simp_rw [normalized_condKey D.weight D.fine hM.ne']
  apply conditional_palette_of_joint D.weight D.fine (fun er => D.palOf er.2.1)
    (fun _ => ENNReal.toReal_nonneg) (fun z => D.L * D.palMass z.val)
    (fun _ => mul_nonneg hD.L_nonneg ENNReal.toReal_nonneg)
  intro e' z'
  have hcap := D.fine_palette_weight_le hD (T := T) e'.1 (D.binOf e'.2.1) z'
  rw [← D.fine_weight hD hT e'.1 (D.binOf e'.2.1)] at hcap
  simpa [atomMass, fiberMass, fine, mul_assoc, mul_comm, mul_left_comm] using hcap

theorem mass_le_one (hD : D.Valid) (n : ℕ) : D.mass n ≤ 1 := by
  letI := hD.prob_σ
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))).trans_eq
    (by simp)

theorem mass_half (hD : D.Valid) {n : ℕ}
    (hn : (1 / 2 : ENNReal) ≤ D.σ {p | D.state p < n}) : 1 / 2 ≤ D.mass n := by
  letI := hD.prob_σ
  have h := ENNReal.toReal_mono (measure_ne_top _ _) hn
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, mass] using h

theorem switch_nonneg {n T : ℕ} (hM : 0 < D.mass n) (e : D.Event n T) :
    0 ≤ (D.switch n T).P e := div_nonneg ENNReal.toReal_nonneg hM.le

theorem switch_pos_weight {n T : ℕ} (hM : 0 < D.mass n) {e : D.Event n T}
    (he : 0 < (D.switch n T).P e) : 0 < D.weight e := by
  change 0 < D.weight e / D.mass n at he
  by_contra hw
  exact (not_le_of_gt he) (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hw) hM.le)

theorem switch_sum (hD : D.Valid) {n T : ℕ} (hT : 0 < T) (hM : 0 < D.mass n) :
    ∑ e, (D.switch n T).P e = 1 := by
  change ∑ e : D.Event n T, D.weight e / D.mass n = 1
  rw [← Finset.sum_div, D.sum_weight hD hT, div_self hM.ne']

theorem sum_prior_le (hD : D.Valid) : ∑ a : D.armSet, D.prior a ≤ 1 := by
  letI := hD.prob_σ
  unfold prior
  rw [sum_toReal_measure_eq (D.σ.map Prod.fst) Finset.univ
    (fun a : D.armSet => {l | D.code l = a.val})
    (fun a => D.measurable_code hD (measurableSet_singleton a.val))]
  · exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))).trans_eq
      (by simp)
  · intro a _ a' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro l hl hl'
    exact hne (Subtype.ext (hl.symm.trans hl'))

theorem time_code_mem {T : ℕ} (hT : 0 < T) {p : α × ℝ} {t : Fin T}
    (ht : ⌊(T : ℝ) * p.2⌋ = (t.val : ℤ)) :
    p.2 ∈ Ico ((t.val : ℝ) / T) (((t.val : ℝ) + 1) / T) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 := Int.floor_le ((T : ℝ) * p.2)
  have h2 := Int.lt_floor_add_one ((T : ℝ) * p.2)
  rw [ht] at h1 h2
  push_cast at h1 h2
  constructor
  · rw [div_le_iff₀ hT']; linarith
  · rw [lt_div_iff₀ hT']; linarith

theorem arm_time_weight_le (hD : D.Valid) {n T : ℕ} (hT : 0 < T)
    (a : D.armSet) (t : Fin T) :
    (∑ e ∈ Finset.univ.filter (fun e : D.Event n T => e.2.1 = a ∧ e.2.2 = t), D.weight e) ≤
      D.L * D.prior a * (1 / T) := by
  letI := hD.prob_σ
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set A : Set α := {l | D.code l = a.val}
  set J : Set ℝ := Ico ((t.val : ℝ) / T) (((t.val : ℝ) + 1) / T)
  have hA : MeasurableSet A := D.measurable_code hD (measurableSet_singleton _)
  have hJ : volume J = ENNReal.ofReal (1 / T) := by
    rw [Real.volume_Ico]
    congr 1
    field_simp
    ring
  have hle := Measure.le_iff.mp hD.density (A ×ˢ J) (hA.prod measurableSet_Ico)
  rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, hJ] at hle
  have hreal := ENNReal.toReal_mono (by finiteness) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD.L_nonneg,
    ENNReal.toReal_ofReal (by positivity)] at hreal
  have hprod : A ×ˢ J = {p : α × ℝ | p.1 ∈ A ∧ p.2 ∈ J} := by
    ext p; simp only [Set.mem_prod, Set.mem_ofPred_eq]
  rw [hprod] at hreal
  have hreal' : (D.σ {p | p.1 ∈ A ∧ p.2 ∈ J}).toReal ≤ D.L * D.prior a * (1 / T) := by
    simpa only [prior, A, mul_assoc] using hreal
  refine (D.sum_weight_test_le hD _ (fun p => p.1 ∈ A ∧ p.2 ∈ J) ?_).trans hreal'
  intro e p he hp
  exact ⟨hp.2.1.trans (congrArg Subtype.val he.1),
    time_code_mem hT (hp.2.2.trans (congrArg (fun s : Fin T => (s.val : ℤ)) he.2))⟩

theorem switch_cell (hD : D.Valid) {n T : ℕ} (hT : 0 < T) (hM : 1 / 2 ≤ D.mass n)
    (κ : Bool) (a : D.armSet) (t : Fin T) :
    fiberMass (D.switch n T).P (fun e => ((D.switch n T).arm e κ, (D.switch n T).cell e)) (a, t) ≤
      D.prior a * (2 * D.L * (1 / T)) := by
  have hMp : 0 < D.mass n := by linarith
  change (∑ e ∈ Finset.univ.filter (fun e : D.Event n T => (e.2.1, e.2.2) = (a, t)),
    D.weight e / D.mass n) ≤ _
  simp only [Prod.mk.injEq]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ hMp).mpr
  have hle := D.arm_time_weight_le hD (n := n) hT a t
  have hnonneg : 0 ≤ D.L * D.prior a * (1 / T) := by
    apply mul_nonneg (mul_nonneg hD.L_nonneg ENNReal.toReal_nonneg)
    positivity
  nlinarith

end Law
end
end Submission.Obl.k4_horizontal_three_traversal_spreading
