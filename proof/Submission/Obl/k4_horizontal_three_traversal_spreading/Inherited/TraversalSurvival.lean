-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/TraversalSurvival.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/TraversalSurvival.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited.FiniteTraversals

/-! Survival of finite conditional paths under refresh, heavy-line and traversal tests. -/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- A potential charging light trajectories, failed refreshes, failed time tests,
and all later failures under the unrestricted conditional transitions. -/
def finiteTraversalFailure (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (prior : Bool → Ar → ℝ) (lam a b : ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, e => a + b + ∑ er, condKey X.P X.fine e er *
      ((if X.heavy prior lam er false then 0 else 1) +
        ∑ e', condKey X.P (X.armKey false) er e' * finiteTraversalFailure X prior lam a b n e')

theorem finiteTraversalFailure_nonneg
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (lam a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ n e, 0 ≤ finiteTraversalFailure X prior lam a b n e := by
  intro n
  induction n with
  | zero => intro e; rfl
  | succ n ih =>
    intro e
    exact add_nonneg (add_nonneg ha hb) (sum_nonneg fun er _ =>
      mul_nonneg (condKey_nonneg hP X.fine e er)
        (add_nonneg (by split_ifs <;> norm_num) (sum_nonneg fun e' _ =>
          mul_nonneg (condKey_nonneg hP (X.armKey false) er e') (ih e'))))

/-- The path survival estimate permits separate tests on the fresh trajectory
and on the new event. The invariant can depend on the complete past record. -/
theorem finiteTraversalValue_survival
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (lam a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (Q : Ω → List (Pal × Tc) → Prop)
    (R : Ω → List (Pal × Tc) → Ω → Prop)
    (T : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (τ : Ω → List (Pal × Tc) → ℝ)
    (hτ : ∀ e l, Q e l → 1 ≤ τ e l)
    (hQ : ∀ e l er e', Q e l → condKey X.P X.fine e er ≠ 0 →
      X.heavy prior lam er false → R e l er →
      condKey X.P (X.armKey false) er e' ≠ 0 → T e l er e' →
      Q e' (l ++ [(X.Z er, X.cell e')]))
    (hR : ∀ e l, Q e l →
      (∑ er, condKey X.P X.fine e er * (if R e l er then 0 else 1)) ≤ a)
    (hT : ∀ e l er, Q e l → 0 < X.P er → X.heavy prior lam er false → R e l er →
      (∑ e', condKey X.P (X.armKey false) er e' * (if T e l er e' then 0 else 1)) ≤ b) :
    ∀ n e l, Q e l → 0 < X.P e →
      1 - finiteTraversalFailure X prior lam a b n e ≤
        finiteTraversalValue X prior lam (fun e l er e' => R e l er ∧ T e l er e') τ n e l := by
  have hF := finiteTraversalFailure_nonneg X hP prior lam a b ha hb
  intro n
  induction n with
  | zero =>
    intro e l hq _
    simpa only [finiteTraversalFailure, finiteTraversalValue, sub_zero] using hτ e l hq
  | succ n ih =>
    intro e l hq hpos
    have hs : ∑ er, condKey X.P X.fine e er = 1 := sum_condKey_eq_one_of_pos hP _ hpos
    let A : Ω → ℝ := fun er =>
      ∑ e', condKey X.P (X.armKey false) er e' * finiteTraversalFailure X prior lam a b n e'
    have hA : ∀ er, 0 ≤ A er := fun er => sum_nonneg fun e' _ =>
      mul_nonneg (condKey_nonneg hP (X.armKey false) er e') (hF n e')
    have hterm (er : Ω) :
        condKey X.P X.fine e er *
          (1 - (if X.heavy prior lam er false then 0 else 1) -
            (if R e l er then 0 else 1) - b - A er) ≤
        condKey X.P X.fine e er *
          (if X.heavy prior lam er false then
            ∑ e', condKey X.P (X.armKey false) er e' *
              (if R e l er ∧ T e l er e' then
                finiteTraversalValue X prior lam (fun e l er e' => R e l er ∧ T e l er e') τ
                  n e' (l ++ [(X.Z er, X.cell e')]) else 0) else 0) := by
      by_cases hf : condKey X.P X.fine e er = 0
      · simp [hf]
      apply mul_le_mul_of_nonneg_left _ (condKey_nonneg hP X.fine e er)
      have her : 0 < X.P er := condKey_pos_of_ne hP X.fine hf
      by_cases hh : X.heavy prior lam er false
      swap
      · simp only [hh, ite_false]
        have hz : 0 ≤ (if R e l er then (0 : ℝ) else 1) := by split_ifs <;> norm_num
        linarith [hA er]
      by_cases hr : R e l er
      swap
      · simp only [hh, hr, ite_true, ite_false, false_and, mul_zero, sum_const_zero]
        linarith [hA er]
      simp only [hh, hr, ite_true, true_and, sub_zero]
      have hs' : ∑ e', condKey X.P (X.armKey false) er e' = 1 :=
        sum_condKey_eq_one_of_pos hP _ her
      have hinner (e' : Ω) :
          condKey X.P (X.armKey false) er e' *
            (1 - finiteTraversalFailure X prior lam a b n e' - (if T e l er e' then 0 else 1)) ≤
          condKey X.P (X.armKey false) er e' *
            (if T e l er e' then
              finiteTraversalValue X prior lam (fun e l er e' => R e l er ∧ T e l er e') τ
                n e' (l ++ [(X.Z er, X.cell e')]) else 0) := by
        by_cases hl : condKey X.P (X.armKey false) er e' = 0
        · simp [hl]
        apply mul_le_mul_of_nonneg_left _ (condKey_nonneg hP (X.armKey false) er e')
        by_cases ht : T e l er e'
        · simp only [ht, ite_true, sub_zero]
          exact ih e' _ (hQ e l er e' hq hf hh hr hl ht)
            (condKey_pos_of_ne hP (X.armKey false) hl)
        · simp only [ht, ite_false]
          linarith [hF n e']
      have hsum := sum_le_sum (s := univ) fun e' _ => hinner e'
      have hexpand : (∑ e', condKey X.P (X.armKey false) er e' *
          (1 - finiteTraversalFailure X prior lam a b n e' - (if T e l er e' then 0 else 1))) =
          1 - A er - ∑ e', condKey X.P (X.armKey false) er e' *
            (if T e l er e' then 0 else 1) := by
        simp only [mul_sub, sum_sub_distrib, mul_one, hs', A]
      rw [hexpand] at hsum
      linarith [hT e l er hq her hh hr]
    have hsum := sum_le_sum (s := univ) fun er _ => hterm er
    have hexpand : (∑ er, condKey X.P X.fine e er *
        (1 - (if X.heavy prior lam er false then 0 else 1) -
          (if R e l er then 0 else 1) - b - A er)) =
        1 - (∑ er, condKey X.P X.fine e er * (if X.heavy prior lam er false then 0 else 1)) -
          (∑ er, condKey X.P X.fine e er * (if R e l er then 0 else 1)) - b -
          ∑ er, condKey X.P X.fine e er * A er := by
      simp only [mul_sub, sum_sub_distrib, mul_one, ← sum_mul, hs, one_mul]
    rw [hexpand] at hsum
    have hsum' :
        1 - (∑ er, condKey X.P X.fine e er * (if X.heavy prior lam er false then 0 else 1)) -
          (∑ er, condKey X.P X.fine e er * (if R e l er then 0 else 1)) - b -
          ∑ er, condKey X.P X.fine e er * A er ≤
        finiteTraversalValue X prior lam (fun e l er e' => R e l er ∧ T e l er e') τ (n + 1) e l :=
      by
        convert hsum using 1
        rw [finiteTraversalValue]
        apply sum_congr rfl
        intro er _
        congr 1
        split_ifs with hh
        · apply sum_congr rfl
          intro e' _
          congr 1
          split_ifs <;> rfl
        · rfl
    change _ ≤ finiteTraversalValue X prior lam (fun e l er e' => R e l er ∧ T e l er e') τ (n + 1) e l
    rw [finiteTraversalFailure]
    simp only [mul_add, sum_add_distrib]
    change 1 - (a + b + ((∑ er, condKey X.P X.fine e er *
      (if X.heavy prior lam er false then 0 else 1)) +
        ∑ er, condKey X.P X.fine e er * A er)) ≤ _
    linarith only [hsum', hR e l hq]


/-- The accepted conditional stationarity identity, integrated against a test. -/
theorem condKey_stationary_test {γ : Type*} [DecidableEq γ]
    (P : Ω → ℝ) (hP : ∀ e, 0 ≤ P e) (key : Ω → γ) (f : Ω → ℝ) :
    (∑ e, P e * ∑ er, condKey P key e er * f er) = ∑ er, P er * f er := by
  simp only [mul_sum, ← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro er _
  rw [← sum_mul, sum_mul_condKey hP key er]

/-- Averaging the failure potential counts each loss once per traversal,
using stationarity of both conditional resamplings. -/
theorem finiteTraversalFailure_average
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (hP1 : ∑ e, X.P e = 1) (prior : Bool → Ar → ℝ) (lam a b : ℝ) :
    ∀ n, (∑ e, X.P e * finiteTraversalFailure X prior lam a b n e) =
      (n : ℝ) * (a + b + ∑ e, X.P e * (if X.heavy prior lam e false then 0 else 1)) := by
  intro n
  induction n with
  | zero => simp [finiteTraversalFailure]
  | succ n ih =>
    simp only [finiteTraversalFailure, mul_add, sum_add_distrib, ← sum_mul, hP1, one_mul]
    rw [condKey_stationary_test X.P hP X.fine
      (fun er => if X.heavy prior lam er false then 0 else 1)]
    rw [condKey_stationary_test X.P hP X.fine
      (fun er => ∑ e', condKey X.P (X.armKey false) er e' * finiteTraversalFailure X prior lam a b n e')]
    rw [condKey_stationary_test X.P hP (X.armKey false)
      (finiteTraversalFailure X prior lam a b n), ih]
    push_cast
    ring

/-- The invariant and endpoint test may depend on the starting event. The
surviving mass is still measured against the unchanged original start law. -/
theorem finiteTraversalValue_average_survival
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (hP1 : ∑ e, X.P e = 1) (prior : Bool → Ar → ℝ) (lam a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (Q : Ω → Ω → List (Pal × Tc) → Prop)
    (R : Ω → Ω → List (Pal × Tc) → Ω → Prop)
    (T : Ω → Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (τ : Ω → Ω → List (Pal × Tc) → ℝ)
    (hτ : ∀ s e l, Q s e l → 1 ≤ τ s e l)
    (hQ : ∀ s e l er e', Q s e l → condKey X.P X.fine e er ≠ 0 →
      X.heavy prior lam er false → R s e l er →
      condKey X.P (X.armKey false) er e' ≠ 0 → T s e l er e' →
      Q s e' (l ++ [(X.Z er, X.cell e')]))
    (hR : ∀ s e l, Q s e l →
      (∑ er, condKey X.P X.fine e er * (if R s e l er then 0 else 1)) ≤ a)
    (hT : ∀ s e l er, Q s e l → 0 < X.P er → X.heavy prior lam er false → R s e l er →
      (∑ e', condKey X.P (X.armKey false) er e' * (if T s e l er e' then 0 else 1)) ≤ b)
    (hstart : ∀ s, 0 < X.P s → Q s s [])
    (hheavy : (∑ e, X.P e * (if X.heavy prior lam e false then 0 else 1)) ≤ c)
    (n : ℕ) :
    1 - (n : ℝ) * (a + b + c) ≤ ∑ s, X.P s *
      finiteTraversalValue X prior lam (fun e l er e' => R s e l er ∧ T s e l er e') (τ s) n s [] := by
  have hpoint (s : Ω) : X.P s * (1 - finiteTraversalFailure X prior lam a b n s) ≤
      X.P s * finiteTraversalValue X prior lam
        (fun e l er e' => R s e l er ∧ T s e l er e') (τ s) n s [] := by
    rcases (hP s).eq_or_lt with hz | hpos
    · rw [← hz]
      simp
    · exact mul_le_mul_of_nonneg_left
        (finiteTraversalValue_survival X hP prior lam a b ha hb (Q s) (R s) (T s) (τ s)
          (hτ s) (hQ s) (hR s) (hT s) n s [] (hstart s hpos) hpos) (hP s)
  have hsum := sum_le_sum (s := univ) fun s _ => hpoint s
  have heq : (∑ s, X.P s * (1 - finiteTraversalFailure X prior lam a b n s)) =
      1 - ∑ s, X.P s * finiteTraversalFailure X prior lam a b n s := by
    simp only [mul_sub, sum_sub_distrib, mul_one, hP1]
  rw [heq, finiteTraversalFailure_average X hP hP1 prior lam a b n] at hsum
  have hmono : (n : ℝ) * (a + b + ∑ e, X.P e *
      (if X.heavy prior lam e false then 0 else 1)) ≤ (n : ℝ) * (a + b + c) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
  linarith

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
