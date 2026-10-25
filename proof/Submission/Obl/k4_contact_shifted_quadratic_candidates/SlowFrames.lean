import Submission.Lib.K4ModelReduction.Diagonal
import Submission.Obl.k4_scalar_mesh_block_reduction.Uniformity

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates

open Filter
open scoped Topology

noncomputable section

/-- Finite-grid constructions at every fixed resolution and tolerance can be
installed on one slowly refining sequence. All frame costs and exponent
rounding are paid by one subpower sequence. Bad initial samples receive no
frame, so no arbitrary initial-sample hypotheses are introduced. -/
theorem exists_slow_frames
    (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ N k)
    (X : ℕ → ℕ → Type*)
    (Valid : (m k : ℕ) → X m k → Prop)
    (cost : (m k : ℕ) → X m k → ℝ)
    (hfinite : ∀ m : ℕ, 1 ≤ m → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∃ x : X m k, Valid m k x ∧ cost m k x ≤ N k ^ ε) :
    ∃ (m : ℕ → ℕ) (H : ℕ → ℝ) (frames : (k : ℕ) → Option (X (m k) k)),
      Monotone m ∧ (∀ k, 1 ≤ m k) ∧ Tendsto m atTop atTop ∧
      (∀ k, 1 ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ N k ^ ε) ∧
      (∀ k, N k ^ (1 / (m k : ℝ)) ≤ H k) ∧
      (∀ k x, frames k = some x → Valid (m k) k x ∧ cost (m k) k x ≤ H k) ∧
      (∀ᶠ k in atTop, frames k ≠ none) := by
  classical
  let P : ℕ → ℝ → ℕ → Prop := fun j ε k =>
    ∃ x : X (j + 1) k, Valid (j + 1) k x ∧ cost (j + 1) k x ≤ N k ^ ε
  obtain ⟨J, η, hJmono, hJtop, hηpos, _, hηlim, hdiag⟩ :=
    Submission.Lib.K4ModelReduction.exists_slow_tolerance P
      (fun j ε hε => hfinite (j + 1) (by omega) ε hε)
  let m : ℕ → ℕ := fun k => J k + 1
  let ζ : ℕ → ℝ := fun k => η k + 1 / (m k : ℝ)
  let H : ℕ → ℝ := fun k => N k ^ ζ k
  have hm1 : ∀ k, 1 ≤ m k := fun k => by dsimp [m]; omega
  have hmt : Tendsto m atTop atTop := (tendsto_add_atTop_nat 1).comp hJtop
  have hmr : Tendsto (fun k => (m k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hmt
  have hζlim : Tendsto ζ atTop (𝓝 0) := by
    simpa only [ζ, one_div, add_zero, Function.comp_apply] using hηlim.add (tendsto_inv_atTop_zero.comp hmr)
  have hζnonneg : ∀ k, 0 ≤ ζ k := by
    intro k
    dsimp [ζ]
    have := hηpos k
    positivity
  have hH := Submission.Obl.k4_scalar_mesh_block_reduction.subpower_of_vanishing_exponent
    N ζ hN hζnonneg hζlim
  have hcostpower (k : ℕ) : N k ^ η k ≤ H k := by
    apply Real.rpow_le_rpow_of_exponent_le (hN k)
    dsimp [ζ]
    exact le_add_of_nonneg_right (by positivity)
  let frames : (k : ℕ) → Option (X (m k) k) := fun k =>
    if h : ∃ x : X (m k) k, Valid (m k) k x ∧ cost (m k) k x ≤ N k ^ η k
    then some (Classical.choose h) else none
  refine ⟨m, H, frames, (fun i j hij => Nat.add_le_add_right (hJmono hij) 1),
    hm1, hmt, hH.1, hH.2, ?_, ?_, ?_⟩
  · intro k
    apply Real.rpow_le_rpow_of_exponent_le (hN k)
    dsimp [ζ]
    linarith [hηpos k]
  · intro k x hx
    dsimp only [frames] at hx
    split_ifs at hx with hex
    · have heq : Classical.choose hex = x := Option.some.inj hx
      subst x
      exact ⟨(Classical.choose_spec hex).1, (Classical.choose_spec hex).2.trans (hcostpower k)⟩
  · filter_upwards [hdiag] with k hk
    have hex : ∃ x : X (m k) k, Valid (m k) k x ∧ cost (m k) k x ≤ N k ^ η k :=
      hk (J k) le_rfl
    simp only [frames, dite_eq_left hex, ne_eq, Option.some_ne_none, not_false_eq_true]

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates
