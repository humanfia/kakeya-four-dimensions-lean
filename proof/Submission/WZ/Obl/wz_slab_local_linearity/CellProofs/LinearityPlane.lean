-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_slab_local_linearity.CellProofs.LinearityPlane.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_slab_local_linearity.CellProofs.LinearityExtract

/-!
# Plane sets for sticky Theorem 5.2

* `CovLe r X N` / `CovGe r X N`: upper and lower bounds `N` for the number of closed `r`-balls
  needed to cover `X` (`E_r(X)` in the sticky paper).
* `ADset δ α C X`: sticky Definition 4.2 (`E_ρ(X ∩ B(x, r)) ≤ C (r/ρ)^α` for `δ ≤ ρ ≤ r`).
* `lineThrough p d`: the line through `p` with direction `d`.
* `LinearityDichotomy σ`: what sticky Lemma 5.3 uses from Theorem 5.2.  Finite families
  `a k` (`k ∈ Ks`) and `b j` (`j ∈ Js`) of points of the unit square, both `(δ, 1, δ^{-η})`-AD,
  with at most `N₀` points of each family within `2δ` of any of its points, and at least
  `N₀³ δ^{η-3}` triples (hence `E_δ(H) ≥ δ^{η-3}`) whose dot products `a · (b - b')` lie in
  a `(δ, 1 - σ, δ^{-η})` Assouad-type set: then `δ^{ε-1}` points `a k` lie within `δ` of a line.
  It follows from Theorem 5.2 by contradicting alternative (B) (which produces dot products of
  dimension `1 - ε > 1 - σ`) and reading off alternative (A).
* `adset_of_biLipschitz`: a set bi-Lipschitz to a subset of the line is `(δ, 1, C)`-AD.
-/

namespace WangZahlLot.Obl.wz_slab_local_linearity.CellProofs

open Finset Set Metric
open scoped RealInnerProductSpace

noncomputable section

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The closed unit square of the plane. -/
def unitSquare : Set Plane := {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}

/-- `X` is covered by at most `N` closed balls of radius `r`. -/
def CovLe {E : Type*} [PseudoMetricSpace E] (r : ℝ) (X : Set E) (N : ℝ) : Prop :=
  ∃ (m : ℕ) (c : Fin m → E), X ⊆ ⋃ j, closedBall (c j) r ∧ (m : ℝ) ≤ N

/-- Every cover of `X` by closed balls of radius `r` uses at least `N` balls. -/
def CovGe {E : Type*} [PseudoMetricSpace E] (r : ℝ) (X : Set E) (N : ℝ) : Prop :=
  ∀ (m : ℕ) (c : Fin m → E), X ⊆ ⋃ j, closedBall (c j) r → N ≤ m

/-- Sticky Definition 4.2: a `(δ, α, C)`-ADset. -/
def ADset {E : Type*} [PseudoMetricSpace E] (δ α C : ℝ) (X : Set E) : Prop :=
  ∀ (x : E) (ρ r : ℝ), δ ≤ ρ → ρ ≤ r → CovLe ρ (X ∩ closedBall x r) (C * (r / ρ) ^ α)

/-- The line through `p` with direction `d`. -/
def lineThrough (p d : Plane) : Set Plane := {x | ∃ t : ℝ, x = p + t • d}

open Classical in
/-- What sticky Lemma 5.3 uses from sticky Theorem 5.2. -/
def LinearityDichotomy (σ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∀ (Ks Js : Finset ℤ) (a b : ℤ → Plane) (T : Finset (ℤ × ℤ × ℤ)) (D : Set ℝ),
      (∀ k ∈ Ks, a k ∈ unitSquare) → (∀ j ∈ Js, b j ∈ unitSquare) →
      ∀ N₀ : ℝ, 1 ≤ N₀ → (∀ k ∈ Ks, (#(Ks.filter fun k' => dist (a k) (a k') ≤ 2 * δ) : ℝ) ≤ N₀) →
      (∀ j ∈ Js, (#(Js.filter fun j' => dist (b j) (b j') ≤ 2 * δ) : ℝ) ≤ N₀) →
      ADset δ 1 (δ ^ (-η)) (a '' Ks) → ADset δ 1 (δ ^ (-η)) (b '' Js) →
      T ⊆ Ks ×ˢ Js ×ˢ Js → N₀ ^ 3 * δ ^ (η - 3) ≤ #T →
      Assouad δ (1 - σ) (δ ^ (-η)) D →
      (∀ t ∈ T, ⟪a t.1, b t.2.1 - b t.2.2⟫ ∈ D) →
      ∃ p d : Plane, d ≠ 0 ∧
        δ ^ (ε - 1) ≤ #(Ks.filter fun k => a k ∈ thickening δ (lineThrough p d))

/-- **Bi-Lipschitz curves are AD.** If `u : Plane → ℝ` satisfies
`|u p - u p'| ≤ L1 ‖p - p'‖` and `‖p - p'‖ ≤ L2 |u p - u p'|` on `X`, then `X` is a
`(δ, 1, 4 L1 L2 + 3)`-ADset for every `δ > 0`. -/
theorem adset_of_biLipschitz {X : Set Plane} {u : Plane → ℝ} {L1 L2 δ : ℝ} (hδ : 0 < δ)
    (hL1 : 0 ≤ L1) (hL2 : 0 < L2)
    (h1 : ∀ p ∈ X, ∀ p' ∈ X, |u p - u p'| ≤ L1 * dist p p')
    (h2 : ∀ p ∈ X, ∀ p' ∈ X, dist p p' ≤ L2 * |u p - u p'|) :
    ADset δ 1 (4 * L1 * L2 + 3) X := by
  classical
  intro x ρ r hδρ hρr
  have hρ : 0 < ρ := lt_of_lt_of_le hδ hδρ
  have hr0 : 0 ≤ r := le_trans hρ.le hρr
  by_cases hne : (X ∩ closedBall x r).Nonempty
  · obtain ⟨p0, hp0X, hp0B⟩ := hne
    -- cells of `u` of length `ρ / L2`
    set w := ρ / L2 with hw
    have hwpos : 0 < w := div_pos hρ hL2
    set n0 : ℤ := ⌊(u p0 - 2 * L1 * r) / w⌋
    set N : ℕ := ⌈(4 * L1 * r) / w⌉₊ + 2
    -- a point of each nonempty cell
    have hex : ∀ i : Fin N, ∃ c : Plane, ∀ p ∈ X ∩ closedBall x r,
        ⌊u p / w⌋ = n0 + i → dist p c ≤ ρ := by
      intro i
      by_cases hi : ∃ p ∈ X ∩ closedBall x r, ⌊u p / w⌋ = n0 + i
      · obtain ⟨c, hc, hci⟩ := hi
        refine ⟨c, fun p hp hpi => ?_⟩
        have hfl := abs_sub_lt_of_floor_div_eq hwpos (hpi.trans hci.symm)
        calc dist p c ≤ L2 * |u p - u c| := h2 p hp.1 c hc.1
          _ ≤ L2 * w := by gcongr
          _ = ρ := by rw [hw]; field_simp
      · push Not at hi
        exact ⟨0, fun p hp hpi => absurd hpi (hi p hp)⟩
    choose c hc using hex
    refine ⟨N, c, ?_, ?_⟩
    · intro p hp
      -- the cell of `p` is one of the `N` cells
      have hup : |u p - u p0| ≤ 2 * L1 * r := by
        calc |u p - u p0| ≤ L1 * dist p p0 := h1 p hp.1 p0 hp0X
          _ ≤ L1 * (2 * r) := by
              gcongr
              calc dist p p0 ≤ dist p x + dist p0 x := dist_triangle_right _ _ _
                _ ≤ r + r := add_le_add (mem_closedBall.mp hp.2) (mem_closedBall.mp hp0B)
                _ = 2 * r := by ring
          _ = 2 * L1 * r := by ring
      rw [abs_le] at hup
      have hlo : n0 ≤ ⌊u p / w⌋ := by
        apply Int.floor_le_floor
        rw [div_le_div_iff_of_pos_right hwpos]; linarith
      have hhi : ⌊u p / w⌋ - n0 < N := by
        have e1 : (⌊u p / w⌋ : ℝ) ≤ u p / w := Int.floor_le _
        have e2 : (u p0 - 2 * L1 * r) / w - 1 < (n0 : ℝ) := by
          have := Int.lt_floor_add_one ((u p0 - 2 * L1 * r) / w); linarith
        have e3 : u p / w - (u p0 - 2 * L1 * r) / w ≤ (4 * L1 * r) / w := by
          rw [← sub_div]; apply div_le_div_of_nonneg_right _ hwpos.le; linarith
        have e4 : (4 * L1 * r) / w ≤ (⌈(4 * L1 * r) / w⌉₊ : ℝ) := Nat.le_ceil _
        have : ((⌊u p / w⌋ - n0 : ℤ) : ℝ) < N := by
          push_cast; simp only [N]; push_cast; linarith
        exact_mod_cast this
      have hnn : 0 ≤ ⌊u p / w⌋ - n0 := by omega
      set i : Fin N := ⟨(⌊u p / w⌋ - n0).toNat, by omega⟩
      refine Set.mem_iUnion.mpr ⟨i, mem_closedBall.mpr (hc i p hp ?_)⟩
      simp only [i, Int.toNat_of_nonneg hnn]
      ring
    · -- count
      have hN : (N : ℝ) ≤ 4 * L1 * r / w + 3 := by
        simp only [N]; push_cast
        have := Nat.ceil_lt_add_one (show 0 ≤ (4 * L1 * r) / w by positivity)
        linarith
      have hrw : 4 * L1 * r / w = 4 * L1 * L2 * (r / ρ) := by rw [hw]; field_simp
      have hrρ : 1 ≤ r / ρ := by rw [le_div_iff₀ hρ]; linarith
      rw [Real.rpow_one]
      calc (N : ℝ) ≤ 4 * L1 * L2 * (r / ρ) + 3 := by rw [← hrw]; exact hN
        _ ≤ (4 * L1 * L2 + 3) * (r / ρ) := by nlinarith [mul_nonneg hL1 hL2.le]
  · refine ⟨0, Fin.elim0, ?_, ?_⟩
    · intro p hp; exact absurd ⟨p, hp⟩ hne
    · simp only [Nat.cast_zero]
      have : 0 ≤ r / ρ := div_nonneg (le_trans hρ.le hρr) hρ.le
      positivity

end

end WangZahlLot.Obl.wz_slab_local_linearity.CellProofs
