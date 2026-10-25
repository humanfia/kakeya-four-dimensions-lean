-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod.TubeCells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.PolyMethod.LineCells
import Submission.WZ.Obl.wz_coarse_tube_grains.PolyMethod.HamSandwich

/-!
# A tube meets few sign cells; degree budget of the partitioning polynomials

* `tube_sign_cells_ncard`: the strict sign patterns realized at points `x` of the
  `δ`-thickening of a segment whose `δ`-ball avoids every zero set are among the patterns
  realized on the line through the segment, so there are at most `∑ deg + 1` of them
  (`line_sign_cells_ncard`). A point `x` and a point `p` of the segment with `dist x p < δ`
  are joined by the segment `[x, p] ⊆ ball x δ`, on which no `P j` vanishes; by the
  intermediate value theorem `P j` has the same strict sign at `x` and at `p`.
* `sum_totalDegree_cube_le`: if `deg (P j) ^ 3 ≤ 27 · 2 ^ j` then
  `(∑ j, deg (P j)) ^ 3 ≤ 1600 · 2 ^ J`, by induction on `J` with the invariant
  `125 · S ^ 3 ≤ 58 ^ 3 · 2 ^ J` (i.e. `S ≤ 11.6 · 2 ^ (J/3)`), the step being a Hölder-type
  bound on the cross terms of `(S + d) ^ 3`.
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod

namespace TubeCellsAux

lemma continuous_evalE (Q : MvPolynomial (Fin 3) ℝ) :
    Continuous fun x : EuclideanSpace ℝ (Fin 3) => MvPolynomial.eval (fun i => x i) Q :=
  (MvPolynomial.continuous_eval Q).comp (by fun_prop)

/-- A continuous real function without zeros on the segment `[x, p]` has the same strict sign
at `x` and at `p`. -/
lemma sign_transfer {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : Continuous f)
    {x p : EuclideanSpace ℝ (Fin 3)} (hne : ∀ y ∈ segment ℝ x p, f y ≠ 0) :
    (0 < f x → 0 < f p) ∧ (f x < 0 → f p < 0) := by
  have hconn : IsPreconnected (segment ℝ x p) := (convex_segment x p).isPreconnected
  constructor
  · intro hx
    by_contra h
    obtain ⟨y, hy, hy0⟩ := hconn.intermediate_value (right_mem_segment ℝ x p)
      (left_mem_segment ℝ x p) hf.continuousOn ⟨not_lt.1 h, hx.le⟩
    exact hne y hy hy0
  · intro hx
    by_contra h
    obtain ⟨y, hy, hy0⟩ := hconn.intermediate_value (left_mem_segment ℝ x p)
      (right_mem_segment ℝ x p) hf.continuousOn ⟨hx.le, not_lt.1 h⟩
    exact hne y hy hy0

/-- The induction step for the degree budget: with `S ≤ 11.6 X^{1/3}` and `d ≤ 3 X^{1/3}`,
`S + d ≤ 14.6 X^{1/3} ≤ 11.6 (2X)^{1/3}`; the cross terms are bounded without cube roots. -/
lemma cube_step (S d X : ℕ) (hS : 125 * S ^ 3 ≤ 195112 * X) (hd : d ^ 3 ≤ 27 * X) :
    125 * (S + d) ^ 3 ≤ 195112 * (2 * X) := by
  have h1 : 25 * S ^ 2 * d ≤ 10092 * X := by
    have h : (25 * S ^ 2 * d) ^ 3 ≤ (10092 * X) ^ 3 := by
      calc (25 * S ^ 2 * d) ^ 3 = (125 * S ^ 3) ^ 2 * d ^ 3 := by ring
        _ ≤ (195112 * X) ^ 2 * (27 * X) := Nat.mul_le_mul (Nat.pow_le_pow_left hS 2) hd
        _ = (10092 * X) ^ 3 := by ring
    exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num)).1 h
  have h2 : 5 * S * d ^ 2 ≤ 522 * X := by
    have h : (5 * S * d ^ 2) ^ 3 ≤ (522 * X) ^ 3 := by
      calc (5 * S * d ^ 2) ^ 3 = (125 * S ^ 3) * (d ^ 3) ^ 2 := by ring
        _ ≤ (195112 * X) * (27 * X) ^ 2 := Nat.mul_le_mul hS (Nat.pow_le_pow_left hd 2)
        _ = (522 * X) ^ 3 := by ring
    exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num)).1 h
  have hexp : 125 * (S + d) ^ 3 =
      125 * S ^ 3 + 15 * (25 * S ^ 2 * d) + 75 * (5 * S * d ^ 2) + 125 * d ^ 3 := by ring
  rw [hexp]
  omega

lemma sum_cube_le_aux (J : ℕ) (d : Fin J → ℕ) (hd : ∀ j : Fin J, d j ^ 3 ≤ 27 * 2 ^ (j : ℕ)) :
    125 * (∑ j, d j) ^ 3 ≤ 195112 * 2 ^ J := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, pow_succ 2 n, mul_comm (2 ^ n) 2]
    have h1 := ih (fun j => d (Fin.castSucc j)) (fun j => by simpa using hd (Fin.castSucc j))
    have h2 := hd (Fin.last n)
    rw [Fin.val_last] at h2
    exact cube_step _ _ _ h1 h2

end TubeCellsAux

open TubeCellsAux in
/-- A δ-tube realizes, at points whose δ-ball avoids every zero set, at most `∑ deg + 1` strict
sign patterns: each such point has the sign pattern of the nearest point of the core segment. -/
theorem tube_sign_cells_ncard (J : ℕ) (P : Fin J → MvPolynomial (Fin 3) ℝ)
    (a u : EuclideanSpace ℝ (Fin 3)) (δ : ℝ) :
    {s : Fin J → Bool | ∃ x ∈ Metric.thickening δ (segment ℝ a (a + u)),
        (∀ y ∈ Metric.ball x δ, ∀ j, MvPolynomial.eval (fun i => y i) (P j) ≠ 0) ∧
        ∀ j, if s j = true then 0 < MvPolynomial.eval (fun i => x i) (P j)
             else MvPolynomial.eval (fun i => x i) (P j) < 0}.ncard ≤
      (∑ j, (P j).totalDegree) + 1 := by
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (line_sign_cells_ncard J P a u)
  rintro s ⟨x, hx, hball, hs⟩
  obtain ⟨p, hp, hdist⟩ := Metric.mem_thickening_iff.1 hx
  rw [segment_eq_image'] at hp
  obtain ⟨t, -, hpt⟩ := hp
  simp only [add_sub_cancel_left] at hpt
  subst hpt
  refine ⟨t, fun j => ?_⟩
  have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg hdist
  have hsub : segment ℝ x (a + t • u) ⊆ Metric.ball x δ :=
    (convex_ball x δ).segment_subset (Metric.mem_ball_self hδ)
      (by rw [Metric.mem_ball, dist_comm]; exact hdist)
  have key := sign_transfer (continuous_evalE (P j)) (fun y hy => hball y (hsub hy) j)
  have hsj := hs j
  split_ifs at hsj ⊢
  · exact key.1 hsj
  · exact key.2 hsj

open TubeCellsAux in
/-- Total degree of the Guth–Katz partitioning polynomials. -/
theorem sum_totalDegree_cube_le (J : ℕ) (P : Fin J → MvPolynomial (Fin 3) ℝ)
    (hP : ∀ j : Fin J, (P j).totalDegree ^ 3 ≤ 27 * 2 ^ (j : ℕ)) :
    (∑ j, (P j).totalDegree) ^ 3 ≤ 1600 * 2 ^ J := by
  have h := sum_cube_le_aux J (fun j => (P j).totalDegree) hP
  omega

end WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod
