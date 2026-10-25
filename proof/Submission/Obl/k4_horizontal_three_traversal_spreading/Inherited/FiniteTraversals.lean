-- Adapted from the same LOT tree, o201, session x0697, commit d395b4346c32c12a70c4bc86d657dea88e733fcd
-- Source: Submission/Obl/k4_horizontal_critical_rate_candidates/Inherited/FiniteTraversals.lean
-- Earlier source attribution is retained below.
-- Adapted from the same LOT tree, o107, session x0353, commit 2dadd64f9c576ee68d49917fce08111798f9ad02
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/FiniteTraversals.lean
-- Unaccepted helper shared on origin/x0353; namespace and local imports renamed.
import Submission.Obl.k4_matching_abstract_switching_mixture.Finite

/-! Finite conditional traversals with an external reference palette.
The conditional laws and the time-cell estimate are reused from accepted o081.
-/

namespace Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited

noncomputable section

open Finset Classical
open Submission.Obl.k4_matching_abstract_switching_mixture.Finite

variable {Ω Sf Sc Ar Iv Pal Tc : Type*} [Fintype Ω] [DecidableEq Sf]
  [DecidableEq Sc] [DecidableEq Ar] [DecidableEq Iv] [Fintype Pal] [DecidableEq Pal]
  [Fintype Tc] [DecidableEq Tc]

/-- Pointwise domination of the refreshed palette atoms gives domination
for every nonnegative palette test. -/
theorem finite_refresh_palette_test_bound
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (π : Pal → ℝ) (K : ℝ)
    (hcap : ∀ e z, (∑ er ∈ univ.filter (fun er => X.Z er = z),
      condKey X.P X.fine e er) ≤ K * π z)
    (e : Ω) (φ : Pal → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    (∑ er, condKey X.P X.fine e er * φ (X.Z er)) ≤ K * ∑ z, π z * φ z := by
  calc
    _ = ∑ z, (∑ er ∈ univ.filter (fun er => X.Z er = z),
        condKey X.P X.fine e er) * φ z := by
      rw [← sum_fiberwise (s := univ) (g := X.Z)]
      apply sum_congr rfl
      intro z _
      rw [sum_mul]
      apply sum_congr rfl
      intro er her
      rw [(mem_filter.mp her).2]
    _ ≤ ∑ z, K * π z * φ z := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_right (hcap e z) (hφ z)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro z _
      ring

/-- One refresh followed by a traversal, tested only through its palette and time cell. -/
theorem single_traversal_reference_bound
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (π : Pal → ℝ) (K lam ρ : ℝ)
    (hlam : 0 < lam) (hρ : 0 ≤ ρ)
    (hcell : ∀ κ a t, fiberMass X.P (fun e => (X.arm e κ, X.cell e)) (a, t) ≤
      prior κ a * ρ)
    (hpalette : ∀ e (φ : Pal → ℝ), (∀ z, 0 ≤ φ z) →
      (∑ er, condKey X.P X.fine e er * φ (X.Z er)) ≤ K * ∑ z, π z * φ z)
    (e : Ω) (h : Pal → Tc → ℝ) (hh : ∀ z t, 0 ≤ h z t) :
    (∑ er, condKey X.P X.fine e er *
      (if X.heavy prior lam er false then
        ∑ e', condKey X.P (X.armKey false) er e' * h (X.Z er) (X.cell e') else 0)) ≤
      (K * (ρ / lam)) * ∑ z, π z * ∑ t, h z t := by
  have hr : 0 ≤ ρ / lam := div_nonneg hρ hlam.le
  have ht (er : Ω) :
      (if X.heavy prior lam er false then
        ∑ e', condKey X.P (X.armKey false) er e' * h (X.Z er) (X.cell e') else 0) ≤
        (ρ / lam) * ∑ t, h (X.Z er) t := by
    split_ifs with hheavy
    · exact X.sum_condKey_cell_le hP prior hlam hρ hcell er false hheavy
        (h (X.Z er)) (hh (X.Z er))
    · exact mul_nonneg hr (sum_nonneg fun t _ => hh _ t)
  calc
    _ ≤ ∑ er, condKey X.P X.fine e er * ((ρ / lam) * ∑ t, h (X.Z er) t) := by
      apply sum_le_sum
      intro er _
      exact mul_le_mul_of_nonneg_left (ht er) (condKey_nonneg hP X.fine e er)
    _ = (ρ / lam) * ∑ er, condKey X.P X.fine e er * ∑ t, h (X.Z er) t := by
      rw [mul_sum]
      apply sum_congr rfl
      intro er _
      ring
    _ ≤ (ρ / lam) * (K * ∑ z, π z * ∑ t, h z t) :=
      mul_le_mul_of_nonneg_left
        (hpalette e (fun z => ∑ t, h z t) (fun z => sum_nonneg fun t _ => hh z t)) hr
    _ = _ := by ring

/-- The retained path expectation, before any normalization after heavy-line deletion.
The predicate allowed may impose additional tests depending on the entire past. -/
def finiteTraversalValue (X : SwitchData Ω Sf Sc Ar Iv Pal Tc)
    (prior : Bool → Ar → ℝ) (lam : ℝ)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (τ : Ω → List (Pal × Tc) → ℝ) : ℕ → Ω → List (Pal × Tc) → ℝ
  | 0, e, l => τ e l
  | n + 1, e, l => ∑ er, condKey X.P X.fine e er *
      (if X.heavy prior lam er false then ∑ e', condKey X.P (X.armKey false) er e' *
        (if allowed e l er e' then
          finiteTraversalValue X prior lam allowed τ n e' (l ++ [(X.Z er, X.cell e')])
          else 0) else 0)

/-- The corresponding independent reference expectation, including its mass factor. -/
def finiteTraversalFree (π : Pal → ℝ) (a : ℝ) (F : List (Pal × Tc) → ℝ) :
    ℕ → List (Pal × Tc) → ℝ
  | 0, l => F l
  | n + 1, l => a * ∑ z, π z * ∑ t, finiteTraversalFree π a F n (l ++ [(z, t)])

theorem finiteTraversalFree_nonneg (π : Pal → ℝ) (a : ℝ) (F : List (Pal × Tc) → ℝ)
    (hπ : ∀ z, 0 ≤ π z) (ha : 0 ≤ a) (hF : ∀ l, 0 ≤ F l) :
    ∀ n l, 0 ≤ finiteTraversalFree π a F n l := by
  intro n
  induction n with
  | zero => exact hF
  | succ n ih =>
    intro l
    exact mul_nonneg ha (sum_nonneg fun z _ =>
      mul_nonneg (hπ z) (sum_nonneg fun t _ => ih _))

/-- Full-past domination for an arbitrary number of traversals. No path or
transition is renormalized after a test fails. -/
theorem finiteTraversalValue_le_free
    (X : SwitchData Ω Sf Sc Ar Iv Pal Tc) (hP : ∀ e, 0 ≤ X.P e)
    (prior : Bool → Ar → ℝ) (π : Pal → ℝ) (K lam ρ : ℝ)
    (hK : 0 ≤ K) (hπ : ∀ z, 0 ≤ π z) (hlam : 0 < lam) (hρ : 0 ≤ ρ)
    (hcell : ∀ κ a t, fiberMass X.P (fun e => (X.arm e κ, X.cell e)) (a, t) ≤
      prior κ a * ρ)
    (hpalette : ∀ e (φ : Pal → ℝ), (∀ z, 0 ≤ φ z) →
      (∑ er, condKey X.P X.fine e er * φ (X.Z er)) ≤ K * ∑ z, π z * φ z)
    (allowed : Ω → List (Pal × Tc) → Ω → Ω → Prop)
    (τ : Ω → List (Pal × Tc) → ℝ) (F : List (Pal × Tc) → ℝ)
    (hF : ∀ l, 0 ≤ F l) (hτ : ∀ e l, τ e l ≤ F l) :
    ∀ n e l, finiteTraversalValue X prior lam allowed τ n e l ≤
      finiteTraversalFree π (K * (ρ / lam)) F n l := by
  have ha : 0 ≤ K * (ρ / lam) := mul_nonneg hK (div_nonneg hρ hlam.le)
  have hfree := finiteTraversalFree_nonneg π (K * (ρ / lam)) F hπ ha hF
  intro n
  induction n with
  | zero => exact hτ
  | succ n ih =>
    intro e l
    calc
      _ ≤ ∑ er, condKey X.P X.fine e er *
          (if X.heavy prior lam er false then
            ∑ e', condKey X.P (X.armKey false) er e' *
              finiteTraversalFree π (K * (ρ / lam)) F n (l ++ [(X.Z er, X.cell e')]) else 0) := by
        apply sum_le_sum
        intro er _
        apply mul_le_mul_of_nonneg_left _ (condKey_nonneg hP X.fine e er)
        split_ifs with hheavy
        · apply sum_le_sum
          intro e' _
          apply mul_le_mul_of_nonneg_left _ (condKey_nonneg hP (X.armKey false) er e')
          split_ifs
          · exact ih e' _
          · exact hfree n _
        · exact le_rfl
      _ ≤ _ := single_traversal_reference_bound X hP prior π K lam ρ hlam hρ hcell hpalette e
        (fun z t => finiteTraversalFree π (K * (ρ / lam)) F n (l ++ [(z, t)]))
        (fun z t => hfree n _)

end

end Submission.Obl.k4_horizontal_three_traversal_spreading.Inherited
