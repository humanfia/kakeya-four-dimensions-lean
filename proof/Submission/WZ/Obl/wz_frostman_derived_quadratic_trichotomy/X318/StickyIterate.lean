-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyIterate.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyPieces
-- Copied from session x0338 (o070 branch, commit ec01e52, file StickyIterate.lean), namespace renamed.

/-!
# The level iteration of the sticky branch

At every level `k < N` the cells of the current set are refined by a "good" subset (for the
sticky branch: the Katz–Tao subset that x0318's `fibre_dichotomy` returns), losing a factor `λ`
per cell, unless the cells without a good subset hold half of the current set (a flat-dominated
level).  `iterate_levels` runs x0305's `cell_refine` over the levels `0, …, N-1`.  At the end every
cell of every level lies in a good set, and at most a factor `(2λ)^N` of the set is lost.

`flatP G λ F` says that `F` has no good subset `F'` with `|F| ≤ λ |F'|`.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- `F` has no good subset keeping a `1/λ` share of it. -/
def flatP {ι : Type*} (G : Finset ι → Prop) (lam : ℝ) (F : Finset ι) : Prop :=
  ¬ ∃ F' ⊆ F, (F.card : ℝ) ≤ lam * F'.card ∧ G F'

open Classical in
/-- The chosen good subset of a non-flat set (the set itself otherwise). -/
noncomputable def goodSub {ι : Type*} (G : Finset ι → Prop) (lam : ℝ) (F : Finset ι) :
    Finset ι :=
  if h : ∃ F' ⊆ F, (F.card : ℝ) ≤ lam * F'.card ∧ G F' then h.choose else F

lemma goodSub_spec {ι : Type*} (G : Finset ι → Prop) (lam : ℝ) (F : Finset ι)
    (h : ¬ flatP G lam F) :
    goodSub G lam F ⊆ F ∧ (F.card : ℝ) ≤ lam * (goodSub G lam F).card ∧ G (goodSub G lam F) := by
  classical
  unfold flatP at h
  push Not at h
  have h' : ∃ F' ⊆ F, (F.card : ℝ) ≤ lam * F'.card ∧ G F' := by
    obtain ⟨F', hF'⟩ := h
    exact ⟨F', hF'.1, hF'.2⟩
  unfold goodSub
  rw [dite_eq_left_of_eq_true (eq_true h')]
  exact h'.choose_spec

open Classical in
/-- **Level iteration.**  For cell maps `κ k` (`k < N`), good-set predicates `G k` and a loss
`λ ≥ 1`: either some level `k < N` is flat-dominated in a set `S' ⊆ S` that kept a
`(2λ)^(-k)` share, or a set `S' ⊆ S` keeping a `(2λ)^(-N)` share has every level-`k` cell
(`k < N`) inside a good set for `G k`. -/
theorem iterate_levels {ι α : Type*} [DecidableEq ι] [DecidableEq α] (κ : ℕ → ι → α)
    (G : ℕ → Finset ι → Prop) {lam : ℝ} (hlam : 1 ≤ lam) (S : Finset ι) (N : ℕ) :
    (∃ k < N, ∃ S' ⊆ S, (S.card : ℝ) ≤ (2 * lam) ^ k * S'.card ∧
        S'.card ≤ 2 * (S'.filter (fun i => flatP (G k) lam (fibre S' (κ k) i))).card) ∨
      (∃ S' ⊆ S, (S.card : ℝ) ≤ (2 * lam) ^ N * S'.card ∧
        ∀ k < N, ∀ i ∈ S', ∃ F', fibre S' (κ k) i ⊆ F' ∧ G k F') := by
  classical
  have h2l : (0 : ℝ) ≤ 2 * lam := by linarith
  induction N with
  | zero =>
    right
    exact ⟨S, subset_rfl, by simp, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ N ih =>
    rcases ih with ⟨k, hk, S', hS'S, hcard, hflat⟩ | ⟨S₁, hS₁S, hcard₁, hgood₁⟩
    · left
      exact ⟨k, by omega, S', hS'S, hcard, hflat⟩
    · rcases cell_refine S₁ (κ N) lam hlam (flatP (G N) lam) (goodSub (G N) lam)
          (fun F hF => ⟨(goodSub_spec (G N) lam F hF).1, (goodSub_spec (G N) lam F hF).2.1⟩)
        with hhalf | ⟨S₂, hS₂S₁, hcard₂, hcell₂⟩
      · left
        exact ⟨N, by omega, S₁, hS₁S, hcard₁, hhalf⟩
      · right
        refine ⟨S₂, hS₂S₁.trans hS₁S, ?_, fun k hk i hi => ?_⟩
        · calc (S.card : ℝ) ≤ (2 * lam) ^ N * S₁.card := hcard₁
            _ ≤ (2 * lam) ^ N * (2 * lam * S₂.card) := by gcongr
            _ = (2 * lam) ^ (N + 1) * S₂.card := by ring
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
          · obtain ⟨F', hF', hG⟩ := hgood₁ k hk' i (hS₂S₁ hi)
            refine ⟨F', fun j hj => hF' ?_, hG⟩
            obtain ⟨hjS₂, hji⟩ := Finset.mem_filter.1 hj
            exact Finset.mem_filter.2 ⟨hS₂S₁ hjS₂, hji⟩
          · obtain ⟨hnf, heq⟩ := hcell₂ i hi
            refine ⟨goodSub (G k) lam (fibre S₁ (κ k) i), heq.le, ?_⟩
            exact (goodSub_spec (G k) lam _ hnf).2.2

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
