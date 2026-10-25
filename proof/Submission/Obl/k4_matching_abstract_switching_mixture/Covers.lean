import Submission.Obl.k4_matching_abstract_switching_mixture.Invariant
import Submission.Obl.k4_matching_abstract_switching_mixture.Boxes
import Submission.Obl.k4_matching_abstract_switching_mixture.Endpoint

namespace Submission.Obl.k4_matching_abstract_switching_mixture

open Set MeasureTheory Finset
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite
open Classical
open scoped ENNReal

set_option linter.unusedSectionVars false

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- A supplied deterministic path cover on the finite representative model. -/
structure PathCover (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (s : Ω → ℝ)
    (m : ℕ) (K δ V : ℝ) (a : Ω) where
  A : Finset Sc
  T : Set (ℝ × (Fin m → ℝ))
  start_bound : |s a| ≤ 1
  card_bound : (A.card : ℝ) ≤ K
  control_bound : ∀ e, X.coarse e ∈ A → ∀ c, |X.ctrl e c| ≤ K
  control_gap : ∀ e, X.coarse e ∈ A → 2 / K ≤ |X.ctrl e true - X.ctrl e false|
  measurable : MeasurableSet T
  volume_bound : volume T ≤ ENNReal.ofReal (K * V)
  paths : ∀ (E W : ℕ → Ω) (c : ℕ → Bool), E 0 = a →
    (∀ p, p ≤ m → legalStep X (E p) (W p, c p, E (p + 1))) →
    (∀ p, p ≤ m + 1 → X.coarse (E p) ∈ A) ∧
    (∀ p, p ≤ m → X.coarse (W p) ∈ A) ∧
    ∀ x : ℝ × (Fin m → ℝ), |x.1 - s (E (m + 1))| ≤ δ →
      (∀ p : Fin m, |x.2 p - s (E ((p : ℕ) + 1))| ≤ δ) →
      endpoint (fun p : Fin (m + 1) => X.ctrl (W p) (c p)) (s a) x ∈ T

/-- Applying a cover to the constant continuation of a finite chain. -/
theorem PathCover.chain_data {X : SwitchData Ω Sf Sc Ar Iv Pal Tc} {s : Ω → ℝ}
    {m : ℕ} {K δ V : ℝ} {a : Ω} (C : PathCover X s m K δ V a)
    {l : List (Ω × Bool × Ω)} (hl : Chain (legalStep X) a l) :
    (∀ p, p ≤ m + 1 → X.coarse (arrival a l p) ∈ C.A) ∧
    (∀ p, p ≤ m → X.coarse (refresh a l p) ∈ C.A) ∧
    ∀ x : ℝ × (Fin m → ℝ), |x.1 - s (arrival a l (m + 1))| ≤ δ →
      (∀ p : Fin m, |x.2 p - s (arrival a l ((p : ℕ) + 1))| ≤ δ) →
      endpoint (fun p : Fin (m + 1) => X.ctrl (refresh a l p) (pathColor l p)) (s a) x ∈ C.T := by
  exact C.paths _ _ _ (arrival_zero a l)
    (fun p hp => chain_sequences (legalStep_diag X) hl p)

theorem PathCover.current_mem {X : SwitchData Ω Sf Sc Ar Iv Pal Tc} {s : Ω → ℝ}
    {m : ℕ} {K δ V : ℝ} {a : Ω} (C : PathCover X s m K δ V a)
    {l : List (Ω × Bool × Ω)} (hl : Chain (legalStep X) a l) (hlen : l.length ≤ m + 1) :
    X.coarse (curEvent a l) ∈ C.A := by
  simpa only [arrival_length] using (C.chain_data hl).1 l.length hlen

/-- A fine record keeps its coarse interval throughout the legal path. -/
theorem chain_interval {X : SwitchData Ω Sf Sc Ar Iv Pal Tc}
    (hival : ∀ x y, X.fine x = X.fine y → X.ival x = X.ival y)
    {a : Ω} {l : List (Ω × Bool × Ω)} (hl : Chain (legalStep X) a l) (p : ℕ) :
    X.ival (arrival a l p) = X.ival a := by
  induction l generalizing a p with
  | nil => rfl
  | cons q l ih =>
    cases p with
    | zero => rfl
    | succ p =>
      have hq : X.ival q.2.2 = X.ival a :=
        (congrArg Prod.snd hl.1.2).trans (hival _ _ hl.1.1)
      exact (ih hl.2 p).trans hq

/-- Reading a projected path recovers both its control and arrival-cell coordinates. -/
theorem projection_at (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) {m : ℕ}
    {a : Ω} {l : List (Ω × Bool × Ω)} {U : Fin (m + 1) → ℝ}
    {ts : Fin (m + 1) → Tc} (hproj : X.proj l = List.ofFn (fun p => (U p, ts p)))
    (p : Fin (m + 1)) :
    X.ctrl (refresh a l p) (pathColor l p) = U p ∧
      X.cell (arrival a l ((p : ℕ) + 1)) = ts p := by
  have hlen : l.length = m + 1 := by
    simpa [SwitchData.proj] using congrArg List.length hproj
  have hp : (p : ℕ) < l.length := by simpa [hlen] using p.isLt
  have h := congrArg (fun v : List (ℝ × Tc) => v[p.val]?) hproj
  simp only [SwitchData.proj, List.getElem?_map, List.getElem?_eq_getElem hp,
    Option.map_some, List.getElem?_ofFn, p.isLt, ↓reduceDIte] at h
  have hpair : (X.ctrl l[p.val].1 l[p.val].2.1, X.cell l[p.val].2.2) = (U p, ts p) := by
    simpa using h
  rw [← triple_getElem a l p.val hp] at hpair
  exact Prod.mk.inj hpair

theorem projection_length (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) {m : ℕ}
    {l : List (Ω × Bool × Ω)} {U : Fin (m + 1) → ℝ} {ts : Fin (m + 1) → Tc}
    (hproj : X.proj l = List.ofFn (fun p => (U p, ts p))) : l.length = m + 1 := by
  simpa [SwitchData.proj] using congrArg List.length hproj

/-- The projected controls are the controls at the actual steps. -/
theorem projection_control (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) {m : ℕ}
    {a : Ω} {l : List (Ω × Bool × Ω)} {U : Fin (m + 1) → ℝ} {ts : Fin (m + 1) → Tc}
    (hproj : X.proj l = List.ofFn (fun p => (U p, ts p))) (p : Fin (m + 1))
    (hp : p.val < l.length) : X.ctrl l[p.val].1 l[p.val].2.1 = U p := by
  have ht := congrArg (fun q : Ω × Bool × Ω => X.ctrl q.1 q.2.1)
    (triple_getElem a l p.val hp)
  exact ht.symm.trans (projection_at X (a := a) hproj p).1

/-- Every control sequence of a successful projected path is bounded and has
separated consecutive controls. -/
theorem PathCover.projected_controls {X : SwitchData Ω Sf Sc Ar Iv Pal Tc} {s t : Ω → ℝ}
    {m : ℕ} {K δ V rt : ℝ} {a : Ω} (C : PathCover X s m K δ V a)
    {l : List (Ω × Bool × Ω)} {U : Fin (m + 1) → ℝ} {ts : Fin (m + 1) → Tc}
    (hl : goodPath X t K⁻¹ rt a l)
    (hproj : X.proj l = List.ofFn (fun p => (U p, ts p))) :
    (∀ p, |U p| ≤ K) ∧ (∀ p : Fin m, K⁻¹ ≤ |U p.succ - U p.castSucc|) := by
  have hlen := projection_length X hproj
  constructor
  · intro p
    rw [← (projection_at X (a := a) hproj p).1]
    exact C.control_bound _ ((C.chain_data hl.1).2.1 p (by omega)) _
  · intro p
    have hrel := hl.2.2.1.getElem p.val (by rw [hlen]; omega)
    have h₀ := projection_control X (a := a) hproj p.castSucc (by rw [hlen]; omega)
    have h₁ := projection_control X (a := a) hproj p.succ (by rw [hlen]; omega)
    change K⁻¹ ≤ |X.ctrl l[p.val + 1].1 l[p.val + 1].2.1 - X.ctrl l[p.val].1 l[p.val].2.1| at hrel
    change X.ctrl l[p.val].1 l[p.val].2.1 = U p.castSucc at h₀
    change X.ctrl l[p.val + 1].1 l[p.val + 1].2.1 = U p.succ at h₁
    rw [h₁, h₀] at hrel
    exact hrel

/-- Positive mass and the cell coordinate at a genuine arrival. -/
theorem projected_arrival_pos (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) {s : Ω → ℝ}
    {m : ℕ} {ru rt : ℝ} {a : Ω} {l : List (Ω × Bool × Ω)}
    {U : Fin (m + 1) → ℝ} {ts : Fin (m + 1) → Tc}
    (hl : goodPath X s ru rt a l)
    (hproj : X.proj l = List.ofFn (fun p => (U p, ts p))) (p : Fin (m + 1)) :
    0 < X.P (arrival a l ((p : ℕ) + 1)) := by
  have hp : p.val < l.length := by rw [projection_length X hproj]; exact p.isLt
  have heq := congrArg (fun q : Ω × Bool × Ω => q.2.2) (triple_getElem a l p.val hp)
  change arrival a l (p.val + 1) = l[p.val].2.2 at heq
  rw [heq]
  exact (hl.2.1 l[p.val] (List.getElem_mem hp)).2

/-- Pairwise separation of arrival events survives reading the path as a vector. -/
theorem projected_arrival_separated (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) {t : Ω → ℝ}
    {m : ℕ} {ru rt : ℝ} {a : Ω} {l : List (Ω × Bool × Ω)}
    {U : Fin (m + 1) → ℝ} {ts : Fin (m + 1) → Tc}
    (hl : goodPath X t ru rt a l)
    (hproj : X.proj l = List.ofFn (fun p => (U p, ts p)))
    (p q : Fin (m + 1)) (hpq : p ≠ q) :
    rt ≤ |t (arrival a l ((p : ℕ) + 1)) - t (arrival a l ((q : ℕ) + 1))| := by
  have hp : p.val < l.length := by rw [projection_length X hproj]; exact p.isLt
  have hq : q.val < l.length := by rw [projection_length X hproj]; exact q.isLt
  have heqp := congrArg (fun r : Ω × Bool × Ω => r.2.2) (triple_getElem a l p.val hp)
  have heqq := congrArg (fun r : Ω × Bool × Ω => r.2.2) (triple_getElem a l q.val hq)
  change arrival a l (p.val + 1) = l[p.val].2.2 at heqp
  change arrival a l (q.val + 1) = l[q.val].2.2 at heqq
  rw [heqp, heqq]
  have h := List.pairwise_iff_getElem.mp hl.2.2.2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hpq) with hpq | hqp
  · simpa only [abs_sub_comm] using h p.val q.val hp hq hpq
  · exact h q.val p.val hq hp hqp

/-- A lower bound on a time difference is stable under small independent errors. -/
theorem separated_of_near {u v x y d r e : ℝ}
    (hu : |x - u| ≤ d) (hv : |y - v| ≤ d) (hsep : r ≤ |u - v|)
    (hmargin : e + 2 * d ≤ r) : e ≤ |x - y| := by
  have h₁ := abs_sub_le u x v
  have h₂ := abs_sub_le x y v
  rw [abs_sub_comm u x] at h₁
  linarith

/-- The arrival order reads the internal coordinates first and final time last. -/
def timeCoord {m : ℕ} (x : ℝ × (Fin m → ℝ)) : Fin (m + 1) → ℝ :=
  Fin.lastCases x.1 x.2

@[simp] theorem timeCoord_last {m : ℕ} (x : ℝ × (Fin m → ℝ)) :
    timeCoord x (Fin.last m) = x.1 := by simp [timeCoord]

@[simp] theorem timeCoord_castSucc {m : ℕ} (x : ℝ × (Fin m → ℝ)) (p : Fin m) :
    timeCoord x p.castSucc = x.2 p := by simp [timeCoord]

theorem tupleBox_coord {m : ℕ} {I : Tc → Set ℝ} {ts : Fin (m + 1) → Tc}
    {x : ℝ × (Fin m → ℝ)} (hx : x ∈ tupleBox I ts) (p : Fin (m + 1)) :
    timeCoord x p ∈ I (ts p) := by
  refine Fin.lastCases ?_ (fun q => ?_) p
  · simpa only [timeCoord_last] using hx.1
  · simpa only [timeCoord_castSucc] using Set.mem_pi.mp hx.2 q (mem_univ q)

/-- Every successful projected path contributes its entire product time cell
to the separated endpoint pullback. -/
theorem PathCover.projected_box {X : SwitchData Ω Sf Sc Ar Iv Pal Tc} {s t : Ω → ℝ}
    {m : ℕ} {K δ V rt L d : ℝ} {a : Ω} (C : PathCover X s m K δ V a)
    (I : Tc → Set ℝ)
    (hival : ∀ x y, X.fine x = X.fine y → X.ival x = X.ival y)
    (hshift : ∀ e f, s e - s f = t e - t f)
    (hunit : ∀ e, 0 < X.P e → X.ival e = X.ival a → ∀ y ∈ I (X.cell e), |y| ≤ 1)
    (hclose : ∀ e, 0 < X.P e → ∀ y ∈ I (X.cell e), |y - s e| ≤ d)
    (hdδ : d ≤ δ) (hmargin : L⁻¹ + 2 * d ≤ rt)
    {l : List (Ω × Bool × Ω)} {U : Fin (m + 1) → ℝ} {ts : Fin (m + 1) → Tc}
    (hl : goodPath X t K⁻¹ rt a l)
    (hproj : X.proj l = List.ofFn (fun p => (U p, ts p))) :
    tupleBox I ts ⊆ pullback L U (s a) C.T := by
  intro x hx
  have hpos := projected_arrival_pos X hl hproj
  have hmem (p : Fin (m + 1)) :
      timeCoord x p ∈ I (X.cell (arrival a l (p.val + 1))) := by
    rw [(projection_at X (a := a) hproj p).2]
    exact tupleBox_coord hx p
  have hnear (p : Fin (m + 1)) :
      |timeCoord x p - s (arrival a l (p.val + 1))| ≤ d :=
    hclose _ (hpos p) _ (hmem p)
  have hbound (p : Fin (m + 1)) : |timeCoord x p| ≤ 1 :=
    hunit _ (hpos p) (chain_interval hival hl.1 _) _ (hmem p)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa only [timeCoord_last] using hbound (Fin.last m)
  · intro p
    simpa only [timeCoord_castSucc] using hbound p.castSucc
  · intro p q hpq
    have hsep : rt ≤ |s (arrival a l (p.val + 1)) - s (arrival a l (q.val + 1))| := by
      rw [hshift]
      exact projected_arrival_separated X hl hproj p.castSucc q.castSucc
        (fun h => hpq (by simpa using h))
    have h := separated_of_near (hnear p.castSucc) (hnear q.castSucc) hsep hmargin
    simpa only [timeCoord_castSucc] using h
  · have hu : (fun p : Fin (m + 1) => X.ctrl (refresh a l p) (pathColor l p)) = U := by
      funext p
      exact (projection_at X (a := a) hproj p).1
    have hfinal : |x.1 - s (arrival a l (m + 1))| ≤ d := by
      simpa only [timeCoord_last, Fin.val_last] using hnear (Fin.last m)
    have hinternal (p : Fin m) : |x.2 p - s (arrival a l (p.val + 1))| ≤ d := by
      simpa only [timeCoord_castSucc, Fin.val_castSucc] using hnear p.castSucc
    have hjit := (C.chain_data hl.1).2.2 x (hfinal.trans hdδ)
      (fun p => (hinternal p).trans hdδ)
    rw [hu] at hjit
    exact hjit

/-- Successful projected paths form the terminal test used in the free bound. -/
noncomputable def pathTest (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (t : Ω → ℝ)
    (ru rt : ℝ) (a : Ω) (ls : List (ℝ × Tc)) : ℝ :=
  if ∃ l, goodPath X t ru rt a l ∧ X.proj l = ls then 1 else 0

theorem pathTest_nonneg (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (t : Ω → ℝ)
    (ru rt : ℝ) (a : Ω) (ls : List (ℝ × Tc)) : 0 ≤ pathTest X t ru rt a ls := by
  unfold pathTest
  split_ifs <;> norm_num

theorem pathTest_of_goodPath (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (t : Ω → ℝ)
    (ru rt : ℝ) (a : Ω) (l : List (Ω × Bool × Ω)) (hl : goodPath X t ru rt a l) :
    pathTest X t ru rt a (X.proj l) = 1 := by
  simp [pathTest, show ∃ l', goodPath X t ru rt a l' ∧ X.proj l' = X.proj l from ⟨l, hl, rfl⟩]

theorem positive_timeSum_witness (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (t : Ω → ℝ)
    (ru rt : ℝ) (a : Ω) {m : ℕ} (U : Fin (m + 1) → ℝ)
    (hpos : 0 < timeSum (pathTest X t ru rt a) [] U) :
    ∃ ts : Fin (m + 1) → Tc, ∃ l, goodPath X t ru rt a l ∧
      X.proj l = List.ofFn (fun p => (U p, ts p)) := by
  have hex : ∃ ts : Fin (m + 1) → Tc,
      0 < pathTest X t ru rt a (List.ofFn (fun p => (U p, ts p))) := by
    by_contra! h
    have hh := sum_nonpos (s := univ) (fun ts _ => h ts)
    simpa [timeSum] using (not_lt_of_ge hh hpos)
  obtain ⟨ts, hts⟩ := hex
  unfold pathTest at hts
  split_ifs at hts with h
  · exact ⟨ts, h⟩
  · norm_num at hts

/-- Count-to-volume transfer for the terminal test of the free experiment. -/
theorem PathCover.timeSum_le {X : SwitchData Ω Sf Sc Ar Iv Pal Tc} {s t : Ω → ℝ}
    {m : ℕ} {K δ V rt L d : ℝ} {a : Ω} (C : PathCover X s m K δ V a)
    (I : Tc → Set ℝ) (hIm : ∀ c, MeasurableSet (I c))
    (hId : Pairwise (fun c c' => Disjoint (I c) (I c'))) (hd : 0 < d)
    (hIv : ∀ c, volume (I c) = ENNReal.ofReal d)
    (hival : ∀ x y, X.fine x = X.fine y → X.ival x = X.ival y)
    (hshift : ∀ e f, s e - s f = t e - t f)
    (hunit : ∀ e, 0 < X.P e → X.ival e = X.ival a → ∀ y ∈ I (X.cell e), |y| ≤ 1)
    (hclose : ∀ e, 0 < X.P e → ∀ y ∈ I (X.cell e), |y - s e| ≤ d)
    (hdδ : d ≤ δ) (hmargin : L⁻¹ + 2 * d ≤ rt) (U : Fin (m + 1) → ℝ) :
    timeSum (pathTest X t K⁻¹ rt a) [] U ≤
      (volume (pullback L U (s a) C.T)).toReal / d ^ (m + 1) := by
  have h := tupleBox_count_le I hIm hId hd hIv
    (fun ts => ∃ l, goodPath X t K⁻¹ rt a l ∧
      X.proj l = List.ofFn (fun p => (U p, ts p)))
    (pullback L U (s a) C.T) (volume_pullback_ne_top _ _ _ _) ?_
  · simpa only [timeSum, List.nil_append, pathTest] using h
  · intro ts hts
    obtain ⟨l, hl, hproj⟩ := hts
    exact C.projected_box I hival hshift hunit hclose hdδ hmargin hl hproj

end Submission.Obl.k4_matching_abstract_switching_mixture
