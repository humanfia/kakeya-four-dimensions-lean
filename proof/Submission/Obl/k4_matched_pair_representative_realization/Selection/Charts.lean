/- Adapted within this LOT tree from o190/x0633, b469254f8a8d614d595658e7ceb1bb13f4234bd2,
Submission/Obl/k4_pair_bin_atlas_assembly/Charts.lean. Existing provenance comments are retained below. -/
import Submission.Obl.k4_matched_pair_representative_realization.Selection.PairFacts
import Submission.Obl.k4_matched_pair_representative_realization.Selection.Interpolation
import Submission.Obl.k4_matched_pair_representative_realization.Selection.FormatOps

/-!
# Merged bin charts from frozen choices

After the anchor, the representatives, the source bins (coins) and one source time per block
have been fixed, the rough charts are indexed by the used keys `(frame, bin)`.  The chart of
a key keeps the frame of the paired data, uses the representative of the key in model
coordinates (`phys`), and collects the fixed-time sections of all sources with that key,
restricted by finitely many polynomial tests: the representative and its hidden derivative
at the three block nodes, and the hidden discriminant at the frozen source time.  The new
observation list of a world composes the old list with the neighbouring bins of each listed
witness.

The retained frozen incidences `G s` of every source (produced by the averaging steps) lie in
the incidence set of the chart of its key, and sources with the same key have disjoint
sections; hence the chart mass dominates the retained mass.
-/

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open Submission.Obl.k4_quadratic_atlas_normalization MvPolynomial MeasureTheory Set
open scoped ENNReal

/-- The hidden discriminant polynomial in model coordinates. -/
noncomputable def discPoly (R : MvPolynomial (Fin 4) ℝ) : MvPolynomial (Fin 4) ℝ :=
  pderiv (3 : Fin 4) R ^ 2 - 2 * pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R) * R

theorem eval_discPoly (R : MvPolynomial (Fin 4) ℝ) (v : Fin 4 → ℝ) :
    eval v (discPoly R) = (eval v (pderiv (3 : Fin 4) R)) ^ 2 -
      2 * eval v (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R)) * eval v R := by
  simp [discPoly]

theorem totalDegree_discPoly_le (R : MvPolynomial (Fin 4) ℝ) (hR : R.totalDegree ≤ 2) :
    (discPoly R).totalDegree ≤ 2 := by
  have h1 : (pderiv (3 : Fin 4) R).totalDegree ≤ 1 :=
    Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' R _ hR
  have h0 : (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R)).totalDegree ≤ 0 :=
    Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' _ _ h1
  have h2 : (2 : MvPolynomial (Fin 4) ℝ).totalDegree = 0 := by
    rw [← map_ofNat C 2]; exact totalDegree_C _
  have h3 : (2 * pderiv (3 : Fin 4) (pderiv (3 : Fin 4) R)).totalDegree ≤ 0 :=
    (totalDegree_mul _ _).trans (by rw [h2]; simpa using h0)
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_pow _ _).trans (by nlinarith)
  · exact (totalDegree_mul _ _).trans (by omega)

theorem measurable_eval_x (R : MvPolynomial (Fin 4) ℝ) (t : ℝ) :
    Measurable (fun l : Trajectory => eval (x l t) R) := by
  have h : (fun l : Trajectory => eval (x l t) R) =
      (fun v : Fin 6 → ℝ => eval (fun k => eval v (xSub t k)) R) ∘ Prod.snd := by
    funext l
    simp only [Function.comp_apply]
    rw [eval_xSub l.1 l.2 t]
  rw [h]
  refine Measurable.comp ?_ measurable_snd
  exact (continuous_eval R |>.comp (continuous_pi fun k => continuous_eval (xSub t k))).measurable

namespace PairData

variable {Nk : ℝ} {Wk : ℕ} {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ} {L a h : ℝ} {M D : ℕ} {ε : ℝ}

/-- The real time index of a frame. -/
def jr (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε) (b : Fin p.J) : ℝ := ((p.j b : ℕ) : ℝ)

/-- The frozen choices of the assembly at one index: a representative test for every key
`(frame, bin)`, one bin (coin) for every source, the bins neighbouring every witness, and one
source time for every time block. -/
structure Choice (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε) where
  d : ℕ
  R0 : Fin p.J → (Fin d → ℤ) → MvPolynomial (Fin 4) ℝ
  coin : Fin p.m → (Fin d → ℤ)
  nbr : Fin p.m → Finset (Fin d → ℤ)
  t : Fin (2 ^ p.T) → ℝ

variable {p : PairData Nk Wk ωk νk Ek Bk L a h M D ε} (C : p.Choice)

namespace Choice

/-- Chart keys: a frame and a bin. -/
abbrev Key := Fin p.J × (Fin C.d → ℤ)

/-- The representative of a key in model coordinates. -/
noncomputable def R (k : C.Key) : MvPolynomial (Fin 4) ℝ :=
  phys p.T (p.jr k.1) p.κ (p.c k.1) (p.u k.1) (p.Q k.1) (Bk (p.γ k.1)) (C.R0 k.1 k.2)

/-- The frozen source time of the block of a key. -/
def tk (k : C.Key) : ℝ := C.t (p.j k.1)

/-- The representative and its hidden derivative are small at the three block nodes. -/
def nodeOK (a' : ℝ) (k : C.Key) (l : Trajectory) : Prop :=
  ∀ i : Fin 3, |eval (x l (node p.T (p.jr k.1) i)) (C.R k)| ≤ δ Nk L * Nk ^ a' / 8 ∧
    |eval (x l (node p.T (p.jr k.1) i)) (pderiv (3 : Fin 4) (C.R k))| ≤
      Bk (p.γ k.1) * Nk ^ a' / 8

/-- The hidden discriminant of the representative is not small at the frozen source time. -/
def discOK (ρD : ℝ) (k : C.Key) (l : Trajectory) : Prop :=
  Bk (p.γ k.1) ^ 2 * ρD ≤ |eval (x l (C.tk k)) (discPoly (C.R k))|

/-- The trajectories of a chart. -/
def A (a' ρD : ℝ) (k : C.Key) : Set Trajectory :=
  {l | (∃ s, (p.frame s = k.1 ∧ C.coin s = k.2) ∧ (l, C.tk k) ∈ p.S s) ∧
    C.nodeOK a' k l ∧ C.discOK ρD k l}

/-- A listed witness `s'` is compatible with a key if it has the same frame and the key's bin
neighbours one of its bins. -/
def compat (k : C.Key) (s' : Fin p.m) : Prop := p.frame s' = k.1 ∧ k.2 ∈ C.nbr s'

/-- The incidences of a chart. -/
def F (a' ρD : ℝ) (k : C.Key) : Set Incidence :=
  {v | v ∈ Ek (p.γ k.1) ∧ v.1 ∈ C.A a' ρD k ∧ v.2 ∈ tblock p.T (p.jr k.1) ∧
    ∃ s' ∈ p.lst (p.γ k.1) (obs (Bk (p.γ k.1)) (δ Nk L) v), C.compat k s'}

/-- The key of a source. -/
def key (s : Fin p.m) : C.Key := (p.frame s, C.coin s)

/-- The used keys. -/
noncomputable def keys : Finset C.Key := Finset.univ.image C.key

/-- The number of charts. -/
noncomputable def card : ℕ := C.keys.card

/-- The key of a chart index. -/
noncomputable def chartKey (c : Fin C.card) : C.Key := (C.keys.equivFin.symm c).1

theorem chartKey_injective : Function.Injective C.chartKey := by
  intro c c' h
  exact C.keys.equivFin.symm.injective (Subtype.ext h)

theorem chartKey_mem (c : Fin C.card) : C.chartKey c ∈ C.keys := (C.keys.equivFin.symm c).2

/-- The new observation lists. -/
noncomputable def newList (γ₁ : Fin Wk) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    Finset (Fin C.card) := by
  classical
  exact Finset.univ.filter fun c =>
    p.γ (C.chartKey c).1 = γ₁ ∧ ∃ s' ∈ p.lst γ₁ o, C.compat (C.chartKey c) s'

theorem card_le_m : C.card ≤ p.m := by
  unfold card keys
  exact Finset.card_image_le.trans (by simp)

theorem A_disjoint (a' ρD : ℝ) {k k' : C.Key} (hne : k ≠ k') (hγ : p.γ k.1 = p.γ k'.1)
    (hj : p.j k.1 = p.j k'.1) : Disjoint (C.A a' ρD k) (C.A a' ρD k') := by
  rw [Set.disjoint_left]
  rintro l ⟨⟨s, ⟨hs1, hs2⟩, hsS⟩, -⟩ ⟨⟨s', ⟨hs1', hs2'⟩, hsS'⟩, -⟩
  have ht : C.tk k = C.tk k' := by simp only [tk, hj]
  rw [ht] at hsS
  by_cases hss : s = s'
  · subst hss
    exact hne (Prod.ext (hs1.symm.trans hs1') (hs2.symm.trans hs2'))
  · have hd := p.source_disjoint s s' hss (by rw [hs1, hs1', hγ]) (by rw [hs1, hs1', hj])
    exact Set.disjoint_left.mp hd hsS hsS'

theorem newList_card_le {Kn : ℕ} (hnbr : ∀ s', (C.nbr s').card ≤ Kn) (γ₁ : Fin Wk)
    (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
    ((C.newList γ₁ o).card : ℝ) ≤ p.κ * Kn := by
  classical
  have himage : (C.newList γ₁ o).image C.chartKey ⊆
      (p.lst γ₁ o).biUnion (fun s' => (C.nbr s').image (fun β => (p.frame s', β))) := by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
    unfold newList at hc
    obtain ⟨-, s', hs', hfr, hnb⟩ := (Finset.mem_filter.mp hc).2
    exact Finset.mem_biUnion.mpr ⟨s', hs', Finset.mem_image.mpr ⟨_, hnb, Prod.ext hfr rfl⟩⟩
  have hcard : (C.newList γ₁ o).card ≤ (p.lst γ₁ o).card * Kn := by
    rw [← Finset.card_image_of_injective _ C.chartKey_injective]
    refine (Finset.card_le_card himage).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum fun s' _ => Finset.card_image_le.trans (hnbr s')).trans ?_
    simp
  calc ((C.newList γ₁ o).card : ℝ) ≤ ((p.lst γ₁ o).card * Kn : ℕ) := by exact_mod_cast hcard
    _ = ((p.lst γ₁ o).card : ℝ) * Kn := by push_cast; ring
    _ ≤ p.κ * Kn := by gcongr; exact p.list_size γ₁ o


theorem tk_mem (ht : ∀ b : Fin (2 ^ p.T), C.t b ∈ tblock p.T ((b : ℕ) : ℝ)) (k : C.Key) :
    C.tk k ∈ tblock p.T (p.jr k.1) := ht (p.j k.1)

theorem measurableSet_A (a' ρD : ℝ) (k : C.Key) : MeasurableSet (C.A a' ρD k) := by
  have h1 : MeasurableSet {l : Trajectory | ∃ s, (p.frame s = k.1 ∧ C.coin s = k.2) ∧
      (l, C.tk k) ∈ p.S s} := by
    rw [Set.ofPred_exists]
    refine MeasurableSet.iUnion fun s => ?_
    rw [Set.ofPred_and]
    exact (MeasurableSet.const _).inter ((p.sources s).1.preimage (by fun_prop))
  have h2 : MeasurableSet {l : Trajectory | C.nodeOK a' k l} := by
    unfold nodeOK
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter fun i => ?_
    rw [Set.ofPred_and]
    exact (measurableSet_le (measurable_eval_x _ _).abs measurable_const).inter
      (measurableSet_le (measurable_eval_x _ _).abs measurable_const)
  have h3 : MeasurableSet {l : Trajectory | C.discOK ρD k l} :=
    measurableSet_le measurable_const (measurable_eval_x _ _).abs
  have : C.A a' ρD k = {l | ∃ s, (p.frame s = k.1 ∧ C.coin s = k.2) ∧ (l, C.tk k) ∈ p.S s} ∩
      ({l | C.nodeOK a' k l} ∩ {l | C.discOK ρD k l}) := by
    ext l; simp [A]
  rw [this]
  exact h1.inter (h2.inter h3)

theorem measurableSet_F (hEm : ∀ γ, MeasurableSet (Ek γ)) (a' ρD : ℝ) (k : C.Key) :
    MeasurableSet (C.F a' ρD k) := by
  have h4 : MeasurableSet {v : Incidence |
      ∃ s' ∈ p.lst (p.γ k.1) (obs (Bk (p.γ k.1)) (δ Nk L) v), C.compat k s'} := by
    have : {v : Incidence | ∃ s' ∈ p.lst (p.γ k.1) (obs (Bk (p.γ k.1)) (δ Nk L) v),
        C.compat k s'} = ⋃ s', {v | s' ∈ p.lst (p.γ k.1) (obs (Bk (p.γ k.1)) (δ Nk L) v)} ∩
          {_v | C.compat k s'} := by
      ext v; simp
    rw [this]
    exact MeasurableSet.iUnion fun s' =>
      (p.list_format (p.γ k.1) s').1.inter (MeasurableSet.const _)
  have : C.F a' ρD k = Ek (p.γ k.1) ∩ (Prod.fst ⁻¹' C.A a' ρD k ∩
      (Prod.snd ⁻¹' tblock p.T (p.jr k.1) ∩
        {v | ∃ s' ∈ p.lst (p.γ k.1) (obs (Bk (p.γ k.1)) (δ Nk L) v), C.compat k s'})) := by
    ext v; simp only [F, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [this]
  exact (hEm _).inter (((C.measurableSet_A a' ρD k).preimage measurable_fst).inter
    ((measurableSet_Icc.preimage measurable_snd).inter h4))

theorem fmt_A_section {a' ρD : ℝ} (k : C.Key) (hR : (C.R k).totalDegree ≤ 2) (i : ℕ) :
    fmt 6 ((p.m : ℝ) * Nk ^ M + 14) (max D 2) {v | (i, v) ∈ C.A a' ρD k} := by
  have h1 : fmt 6 ((p.m : ℝ) * Nk ^ M) (max D 2)
      {v | ∃ s, (p.frame s = k.1 ∧ C.coin s = k.2) ∧ v ∈ {v | ((i, v), C.tk k) ∈ p.S s}} := by
    have := fmt_iUnion_filter (fun s => {v : Fin 6 → ℝ | ((i, v), C.tk k) ∈ p.S s})
      (fun s => fmt_mono' (fmt_fixed_time (p.S s) i (C.tk k) ((p.sources s).2.1 i)) le_rfl
        (le_max_left D 2)) (fun s => p.frame s = k.1 ∧ C.coin s = k.2)
    simpa only [Fintype.card_fin] using this
  have hd1 : (pderiv (3 : Fin 4) (C.R k)).totalDegree ≤ 2 :=
    (Submission.Lib.K4QuadraticSheets.totalDegree_pderiv_le' (C.R k) _ hR).trans (by norm_num)
  have h2 : fmt 6 (Fintype.card (Fin 3) * (2 + 2)) (max D 2) {v | ∀ i' : Fin 3,
      v ∈ {v : Fin 6 → ℝ | |eval (x (i, v) (node p.T (p.jr k.1) i')) (C.R k)| ≤
        δ Nk L * Nk ^ a' / 8} ∩
      {v : Fin 6 → ℝ | |eval (x (i, v) (node p.T (p.jr k.1) i')) (pderiv (3 : Fin 4) (C.R k))| ≤
        Bk (p.γ k.1) * Nk ^ a' / 8}} := by
    refine fmt_iInter _ fun i' => fmt_inter ?_ ?_
    · exact fmt_trace (fmt_mono' (fmt_abs_le (C.R k) hR _) le_rfl (le_max_right D 2)) i _
    · exact fmt_trace (fmt_mono' (fmt_abs_le _ hd1 _) le_rfl (le_max_right D 2)) i _
  have h3 : fmt 6 2 (max D 2) {v : Fin 6 → ℝ | x (i, v) (C.tk k) ∈
      {z : Fin 4 → ℝ | Bk (p.γ k.1) ^ 2 * ρD ≤ |eval z (discPoly (C.R k))|}} :=
    fmt_trace (fmt_mono' (fmt_le_abs _ (totalDegree_discPoly_le _ hR) _) le_rfl
      (le_max_right D 2)) i _
  have h := fmt_inter h1 (fmt_inter h2 h3)
  refine fmt_mono' (fmt_congr' h ?_) (by simp; norm_num) le_rfl
  ext v
  simp only [A, nodeOK, discOK, Set.mem_inter_iff, Set.mem_ofPred_eq]

theorem fmt_F_section {a' ρD : ℝ} {Me De : ℕ} (k : C.Key) (hR : (C.R k).totalDegree ≤ 2)
    (hEf : ∀ γ i, fmt 7 (Nk ^ Me) De {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ Ek γ})
    (i : ℕ) :
    fmt 7 (Nk ^ Me + (((p.m : ℝ) * Nk ^ M + 14) + (2 + (p.m : ℝ) * Nk ^ M))) (max De (max D 2))
      {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ C.F a' ρD k} := by
  have hE := fmt_mono' (hEf (p.γ k.1) i) le_rfl (le_max_left De (max D 2))
  have hA := fmt_mono' (fmt_cylinder (C.fmt_A_section (a' := a') (ρD := ρD) k hR i)) le_rfl
    (le_max_right De (max D 2))
  have hT := fmt_mono' (fmt_time_mem_Icc (p.jr k.1 / (2 : ℝ) ^ p.T) ((p.jr k.1 + 1) / (2 : ℝ) ^ p.T))
    le_rfl (show 1 ≤ max De (max D 2) by omega)
  have hL : fmt 7 ((p.m : ℝ) * Nk ^ M) (max De (max D 2)) {r : Fin 7 → ℝ | ∃ s', C.compat k s' ∧
      r ∈ {r : Fin 7 → ℝ | s' ∈ p.lst (p.γ k.1) (obs (Bk (p.γ k.1)) (δ Nk L)
        ((i, fun z : Fin 6 => r z.castSucc), r 6))}} := by
    have := fmt_iUnion_filter _ (fun s' => fmt_mono' ((p.list_format (p.γ k.1) s').2 i) le_rfl
      (show D ≤ max De (max D 2) by omega)) (fun s' => C.compat k s')
    simpa only [Fintype.card_fin] using this
  have h := fmt_inter hE (fmt_inter hA (fmt_inter hT hL))
  refine fmt_congr' h ?_
  ext r
  simp only [F, tblock, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3, s', hs', hc⟩
    exact ⟨h1, h2, h3, s', hc, hs'⟩
  · rintro ⟨h1, h2, h3, s', hc, hs'⟩
    exact ⟨h1, h2, h3, s', hs', hc⟩


theorem abs_inv_entry_le (Q : Matrix (Fin 2) (Fin 2) ℝ) (i i' : Fin 2) :
    |Q⁻¹ i i'| ≤ ∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|) := by
  have h1 : |Q i i'| + |Q⁻¹ i i'| ≤ ∑ e' : Fin 2, (|Q i e'| + |Q⁻¹ i e'|) :=
    Finset.single_le_sum (f := fun e' => |Q i e'| + |Q⁻¹ i e'|) (fun _ _ => by positivity)
      (Finset.mem_univ i')
  have h2 : ∑ e' : Fin 2, (|Q i e'| + |Q⁻¹ i e'|) ≤
      ∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|) :=
    Finset.single_le_sum (f := fun e => ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|))
      (fun _ _ => by positivity) (Finset.mem_univ i)
  linarith [abs_nonneg (Q i i')]

/-- Every key gives a rough chart. -/
theorem rough_key (hN : 1 ≤ Nk) {M' D' Me De : ℕ} {κ' a' ρD Z : ℝ} (k : C.Key)
    (hκ' : p.κ ≤ κ') (hM' : M ≤ M')
    (hB : ∀ γ, 0 < Bk γ ∧ Bk γ ≤ Z) (hZM : Nk ^ M ≤ Z) (hZT : (2 : ℝ) ^ p.T ≤ Z)
    (hcoef : 81 * Nk ^ M * (6 * Z ^ 2) ^ 2 ≤ Nk ^ M')
    (hR0 : (C.R0 k.1 k.2).totalDegree ≤ 2 ∧ (∀ e, |(C.R0 k.1 k.2).coeff e| ≤ Nk ^ M) ∧
      |eval (0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (C.R0 k.1 k.2)))| ≤
        (δ Nk L)⁻¹)
    (hρD : (κ' * Nk ^ a')⁻¹ ≤ ρD)
    (ht : ∀ b : Fin (2 ^ p.T), C.t b ∈ tblock p.T ((b : ℕ) : ℝ))
    (hEm : ∀ γ, MeasurableSet (Ek γ))
    (hEf : ∀ γ i, fmt 7 (Nk ^ Me) De
      {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ Ek γ})
    (hbudA : (p.m : ℝ) * Nk ^ M + 14 ≤ Nk ^ M')
    (hbudF : Nk ^ Me + (((p.m : ℝ) * Nk ^ M + 14) + (2 + (p.m : ℝ) * Nk ^ M)) ≤ Nk ^ M')
    (hD' : max De (max D 2) ≤ D') {ex : Prop} (hex : ex) :
    rough Nk M' D' κ' p.T (p.jr k.1) L a' (Bk (p.γ k.1)) (Ek (p.γ k.1)) (p.c k.1) (p.u k.1)
      (p.Q k.1) (C.R k) (C.A a' ρD k) (C.F a' ρD k) ex := by
  obtain ⟨hdet, hcu, hQQ, hQκ⟩ := p.frames k.1
  have hκ1 : 1 ≤ p.κ := p.κ_one
  have hκ'1 : 1 ≤ κ' := hκ1.trans hκ'
  have hNpos : 0 < Nk := lt_of_lt_of_le one_pos hN
  have hNM : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hN hM'
  have hZ1 : 1 ≤ Z := (one_le_pow₀ hN).trans hZM
  obtain ⟨hR0deg, hR0coef, hR0dd⟩ := hR0
  have hRdeg : (C.R k).totalDegree ≤ 2 := (totalDegree_phys_le _).trans hR0deg
  have hBk := hB (p.γ k.1)
  have hq : (0 : ℝ) < 2 ^ p.T := by positivity
  have hδ : 0 < δ Nk L := by unfold δ; positivity
  have hNa : 0 < Nk ^ a' := Real.rpow_pos_of_pos hNpos a'
  refine ⟨hdet, hcu.trans hNM, hQQ.trans hNM, hQκ.trans (by gcongr), hRdeg, ?_,
    C.measurableSet_A a' ρD k, C.measurableSet_F hEm a' ρD k, ?_, ?_, ?_, ?_, hex⟩
  · -- coefficients
    intro e
    have hj : |p.jr k.1| ≤ Z := by
      rw [abs_of_nonneg (by unfold jr; positivity)]
      refine le_trans ?_ hZT
      unfold jr
      have h := (p.j k.1).isLt
      have h' : ((p.j k.1 : ℕ) : ℝ) < ((2 ^ p.T : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      exact h'.le
    have hQinv : ∀ i i', |(p.Q k.1)⁻¹ i i'| ≤ Z :=
      fun i i' => (abs_inv_entry_le _ i i').trans (hQQ.trans hZM)
    have hc : ∀ i, |p.c k.1 i| ≤ Z := fun i => by
      have h := PiLp.norm_apply_le (p.c k.1) i
      rw [Real.norm_eq_abs] at h
      linarith [norm_nonneg (p.u k.1)]
    have hu : ∀ i, |p.u k.1 i| ≤ Z := fun i => by
      have h := PiLp.norm_apply_le (p.u k.1) i
      rw [Real.norm_eq_abs] at h
      linarith [norm_nonneg (p.c k.1)]
    exact (abs_coeff_phys_le _ hR0deg (by positivity) hR0coef hZ1 hκ1 hZT hj hQinv hc hu
      (by rw [abs_of_pos hBk.1]; exact hBk.2) e).trans hcoef
  · -- formats
    intro i
    exact ⟨fmt_mono' (C.fmt_A_section k hRdeg i) hbudA (le_trans (le_max_right _ _) hD'),
      fmt_mono' (C.fmt_F_section k hRdeg hEf i) hbudF hD'⟩
  · -- trajectories of the chart
    rintro l ⟨⟨s, ⟨hs1, hs2⟩, hsS⟩, hnode, -⟩
    obtain ⟨-, hl1, hl2, -, htraj⟩ := (p.sources s).2.2 (l, C.tk k) hsS
    refine ⟨hl1.trans hNM, fun e => (hl2 e).trans hNM, fun t ht' => ⟨?_, ?_, ?_, ?_⟩⟩
    · have ht'' : t ∈ Set.Icc (((p.j (p.frame s) : ℕ) : ℝ) / (2 : ℝ) ^ p.T)
          ((((p.j (p.frame s) : ℕ) : ℝ) + 1) / (2 : ℝ) ^ p.T) := by
        rw [hs1]; exact ht'
      have h := (htraj t ht'').1
      rw [hs1] at h
      exact h.trans hκ'
    · have hb := tblock_bound_of_nodes (quadratic_eval_x (C.R k) hRdeg l)
        (fun i => (hnode i).1) t ht'
      calc _ ≤ 8 * (δ Nk L * Nk ^ a' / 8) := hb
        _ = 1 * δ Nk L * Nk ^ a' := by ring
        _ ≤ κ' * δ Nk L * Nk ^ a' := by gcongr
    · have hd : (pderiv (3 : Fin 4) (C.R k)).totalDegree ≤ 2 :=
        (Submission.Obl.k4_eligibility_sign_description.degree_pderiv_le _ _).trans hRdeg
      have hb := tblock_bound_of_nodes (quadratic_eval_x _ hd l) (fun i => (hnode i).2) t ht'
      calc _ ≤ 8 * (Bk (p.γ k.1) * Nk ^ a' / 8) := hb
        _ = 1 * Bk (p.γ k.1) * Nk ^ a' := by ring
        _ ≤ κ' * Bk (p.γ k.1) * Nk ^ a' := by gcongr; exact hBk.1.le
    · simp only [R]
      rw [eval_pderiv_pderiv_phys, eval_pderiv_pderiv_const _ hR0deg, abs_mul,
        abs_of_nonneg (sq_nonneg _)]
      calc _ ≤ Bk (p.γ k.1) ^ 2 * (δ Nk L)⁻¹ := by gcongr
        _ = 1 * Bk (p.γ k.1) ^ 2 / δ Nk L := by ring
        _ ≤ κ' * Bk (p.γ k.1) ^ 2 / δ Nk L := by gcongr
  · -- incidences of the chart
    rintro q ⟨hE, hA, hT, -⟩
    exact ⟨hE, hA, hT⟩
  · -- discriminant floor at the frozen source time
    rintro l ⟨-, -, hdisc⟩
    refine ⟨C.tk k, C.tk_mem ht k, ?_⟩
    rw [← eval_discPoly]
    refine le_trans ?_ hdisc
    rw [div_eq_mul_inv]
    gcongr


theorem world_eq_of_key {s : Fin p.m} {k : C.Key} (hs : C.key s = k) : p.world s = p.γ k.1 := by
  rw [← hs]; rfl

/-- The retained frozen incidences of the sources of a key are disjoint, and lie in the
incidences of its chart; the chart masses dominate the retained mass. -/
theorem coverage (a' ρD : ℝ) (G : Fin p.m → Set Incidence) (hGm : ∀ s, MeasurableSet (G s))
    (hGF : ∀ s, G s ⊆ C.F a' ρD (C.key s))
    (hGS : ∀ s, ∀ v ∈ G s, (v.1, C.tk (C.key s)) ∈ p.S s) :
    ∑ s, ENNReal.ofReal (ωk (p.world s)) * ((νk (p.world s)).prod volume) (G s) ≤
      ∑ c : Fin C.card, ENNReal.ofReal (ωk (p.γ (C.chartKey c).1)) *
        ((νk (p.γ (C.chartKey c).1)).prod volume) (C.F a' ρD (C.chartKey c)) := by
  classical
  let g : C.Key → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (ωk (p.γ k.1)) * ((νk (p.γ k.1)).prod volume) (C.F a' ρD k)
  have hR : ∑ c : Fin C.card, g (C.chartKey c) = ∑ k ∈ C.keys, g k := by
    rw [← Finset.sum_coe_sort C.keys]
    exact Equiv.sum_comp C.keys.equivFin.symm (fun x => g x.1)
  change _ ≤ ∑ c : Fin C.card, g (C.chartKey c)
  rw [hR, ← Finset.sum_fiberwise_of_maps_to (g := C.key) (t := C.keys)
    (fun s _ => Finset.mem_image_of_mem _ (Finset.mem_univ s))]
  refine Finset.sum_le_sum fun k _ => ?_
  have hdisj : (↑(Finset.univ.filter (fun s => C.key s = k)) : Set (Fin p.m)).PairwiseDisjoint G := by
    intro s hs s' hs' hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs hs'
    rw [Function.onFun, Set.disjoint_left]
    intro v hv hv'
    have h1 := hGS s v hv
    have h2 := hGS s' v hv'
    rw [hs] at h1
    rw [hs'] at h2
    have hfr : p.frame s = p.frame s' := by
      have := congrArg Prod.fst (hs.trans hs'.symm); exact this
    have hd := p.source_disjoint s s' hne (by rw [hfr]) (by rw [hfr])
    exact Set.disjoint_left.mp hd h1 h2
  calc ∑ s ∈ Finset.univ.filter (fun s => C.key s = k),
        ENNReal.ofReal (ωk (p.world s)) * ((νk (p.world s)).prod volume) (G s)
      = ∑ s ∈ Finset.univ.filter (fun s => C.key s = k),
          ENNReal.ofReal (ωk (p.γ k.1)) * ((νk (p.γ k.1)).prod volume) (G s) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [C.world_eq_of_key (Finset.mem_filter.mp hs).2]
    _ = ENNReal.ofReal (ωk (p.γ k.1)) * ∑ s ∈ Finset.univ.filter (fun s => C.key s = k),
          ((νk (p.γ k.1)).prod volume) (G s) := (Finset.mul_sum _ _ _).symm
    _ = ENNReal.ofReal (ωk (p.γ k.1)) * ((νk (p.γ k.1)).prod volume)
          (⋃ s ∈ Finset.univ.filter (fun s => C.key s = k), G s) := by
        rw [measure_biUnion_finset hdisj (fun s _ => hGm s)]
    _ ≤ g k := by
        refine mul_le_mul_right ?_ _
        apply measure_mono
        refine Set.iUnion₂_subset fun s hs => ?_
        have := hGF s
        rwa [(Finset.mem_filter.mp hs).2] at this

/-- **The charts of the frozen choices form a rough system at this index.** -/
theorem roughAt (hN : 1 ≤ Nk) {M' D' Me De Kn : ℕ} {κ' a' ρD Z : ℝ}
    (hKn : p.κ * Kn ≤ κ') (hKn1 : 1 ≤ Kn) (hnbr : ∀ s', (C.nbr s').card ≤ Kn)
    (hM' : M ≤ M')
    (hB : ∀ γ, 0 < Bk γ ∧ Bk γ ≤ Z) (hZM : Nk ^ M ≤ Z) (hZT : (2 : ℝ) ^ p.T ≤ Z)
    (hcoef : 81 * Nk ^ M * (6 * Z ^ 2) ^ 2 ≤ Nk ^ M')
    (hR0 : ∀ k : C.Key, (C.R0 k.1 k.2).totalDegree ≤ 2 ∧
      (∀ e, |(C.R0 k.1 k.2).coeff e| ≤ Nk ^ M) ∧
      |eval (0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (C.R0 k.1 k.2)))| ≤
        (δ Nk L)⁻¹)
    (hρD : (κ' * Nk ^ a')⁻¹ ≤ ρD)
    (ht : ∀ b : Fin (2 ^ p.T), C.t b ∈ tblock p.T ((b : ℕ) : ℝ))
    (hEm : ∀ γ, MeasurableSet (Ek γ))
    (hEf : ∀ γ i, fmt 7 (Nk ^ Me) De
      {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ Ek γ})
    (hbudA : (p.m : ℝ) * Nk ^ M + 14 ≤ Nk ^ M')
    (hbudF : Nk ^ Me + (((p.m : ℝ) * Nk ^ M + 14) + (2 + (p.m : ℝ) * Nk ^ M)) ≤ Nk ^ M')
    (hD' : max De (max D 2) ≤ D')
    (G : Fin p.m → Set Incidence) (hGm : ∀ s, MeasurableSet (G s))
    (hGF : ∀ s, G s ⊆ C.F a' ρD (C.key s))
    (hGS : ∀ s, ∀ v ∈ G s, (v.1, C.tk (C.key s)) ∈ p.S s)
    (hmass : ENNReal.ofReal κ'⁻¹ ≤
      ∑ s, ENNReal.ofReal (ωk (p.world s)) * ((νk (p.world s)).prod volume) (G s)) :
    RoughBody Nk Wk ωk νk Ek Bk L a' M' D' κ' p.T := by
  classical
  have hκ' : p.κ ≤ κ' := by
    have : p.κ * 1 ≤ p.κ * Kn := by
      gcongr
      · linarith [p.κ_one]
      · exact_mod_cast hKn1
    linarith
  have hNM : Nk ^ M ≤ Nk ^ M' := pow_le_pow_right₀ hN hM'
  refine ⟨C.card, fun c => p.γ (C.chartKey c).1, fun c => p.j (C.chartKey c).1,
    fun c => p.c (C.chartKey c).1, fun c => p.u (C.chartKey c).1, fun c => p.Q (C.chartKey c).1,
    fun c => C.R (C.chartKey c), fun c => C.A a' ρD (C.chartKey c),
    fun c => C.F a' ρD (C.chartKey c), C.newList, ?_, ?_, ?_, ?_, ?_⟩
  · calc (C.card : ℝ) ≤ p.m := by exact_mod_cast C.card_le_m
      _ ≤ Nk ^ M := p.source_count
      _ ≤ Nk ^ M' := hNM
  · intro c c' hne hγ hj
    exact C.A_disjoint a' ρD (fun h => hne (C.chartKey_injective h)) hγ hj
  · intro γ₁ o
    exact (C.newList_card_le hnbr γ₁ o).trans hKn
  · intro c
    refine C.rough_key hN (C.chartKey c) hκ' hM' hB hZM hZT hcoef (hR0 _) hρD ht hEm hEf hbudA
      hbudF hD' ?_
    intro q hq
    obtain ⟨-, -, -, s', hs', hc⟩ := hq
    unfold newList
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, s', hs', hc⟩
  · exact hmass.trans (C.coverage a' ρD G hGm hGF hGS)

end Choice
end PairData
end Submission.Obl.k4_matched_pair_representative_realization.Selection
