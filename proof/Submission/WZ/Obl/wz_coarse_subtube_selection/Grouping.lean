-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_subtube_selection.Grouping.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_subtube_selection.Geometry

/-!
# Grouping the tubes of a coarse tube into boundedly many sub-tubes

The normalized parameters `((x - a)/ρ, (v - b)/ρ)` of a unit `δ`-tube inside `T (ρ/2) y w`,
with `(a, b) = (y, w)` or `(y + w, -w)`, lie in a fixed ball of `Space × Space`. A fixed finite
cover of that ball by small balls (compactness) colours the tubes with a number of colours
independent of `δ`, `ρ` and the family; tubes of the same colour lie in the `ρ/256`-thickening of
one another.
-/

namespace WangZahlLot.Obl.wz_coarse_subtube_selection

open Set Metric MeasureTheory
open LeanEval.Analysis.WangZahlKakeya

/-- A fixed finite cover of a closed ball of `Space × Space` by balls of radius `ε`, with a
choice of a covering ball for every point of the closed ball. -/
theorem exists_param_cover {R : ℝ} (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (c : Fin N → Space × Space) (κ : Space × Space → Fin N), 0 < N ∧
      ∀ z : Space × Space, ‖z‖ ≤ R → dist z (c (κ z)) < ε := by
  classical
  obtain ⟨t, -, ht, hcover⟩ :=
    (isCompact_closedBall (0 : Space × Space) R).finite_cover_balls hε
  set s := ht.toFinset with hs
  have hmem : (0 : Space × Space) ∈ closedBall (0 : Space × Space) R := mem_closedBall_self hR
  have hN : 0 < s.card := by
    obtain ⟨x, hx, -⟩ := mem_iUnion₂.mp (hcover hmem)
    exact Finset.card_pos.mpr ⟨x, ht.mem_toFinset.mpr hx⟩
  let c : Fin s.card → Space × Space := fun k => (s.equivFin.symm k).1
  have hex : ∀ z : Space × Space, ∃ k : Fin s.card, ‖z‖ ≤ R → dist z (c k) < ε := by
    intro z
    by_cases hz : ‖z‖ ≤ R
    · have hz' : z ∈ closedBall (0 : Space × Space) R := by
        rwa [mem_closedBall, dist_zero_right]
      obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hcover hz')
      refine ⟨s.equivFin ⟨x, ht.mem_toFinset.mpr hx⟩, fun _ => ?_⟩
      simp only [c, Equiv.symm_apply_apply]
      exact hzx
    · exact ⟨⟨0, hN⟩, fun h => absurd h hz⟩
  choose κ hκ using hex
  exact ⟨s.card, c, κ, hN, hκ⟩

/-- The sub-tube grouping: a fixed number `K` of colours suffices to colour the unit `δ`-tubes of
any family inside `T (ρ/2) y w` (with `δ ≤ ρ/512`) so that tubes of the same colour lie in the
`ρ/256`-thickening of one another. -/
theorem exists_subtube_grouping : ∃ K : ℕ, 0 < K ∧ ∀ {δ ρ : ℝ}, 0 < δ → 0 < ρ → δ ≤ ρ / 512 →
    ∀ {n : ℕ} (x v : Fin n → Space) (F : Finset (Fin n)) (y w : Space), ‖w‖ = 1 →
    (∀ i ∈ F, ‖v i‖ = 1 ∧ thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      thickening (ρ / 2) (segment ℝ y (y + w))) →
    ∃ f : Fin n → Fin K, ∀ i ∈ F, ∀ j ∈ F, f i = f j →
      thickening δ (segment ℝ (x j) (x j + v j)) ⊆
        thickening (ρ / 256) (segment ℝ (x i) (x i + v i)) := by
  obtain ⟨N, c, κ, hN, hκ⟩ :=
    exists_param_cover (R := 2) (by norm_num) (ε := 1 / 2048) (by norm_num)
  refine ⟨2 * N, by omega, ?_⟩
  intro δ ρ hδ hρ hδρ n x v F y w hw hF
  classical
  let cond : Fin n → Prop := fun i => ‖x i - y‖ < 3 * ρ / 2 ∧ ‖v i - w‖ < 2 * ρ
  let a : Fin n → Space := fun i => if cond i then y else y + w
  let b : Fin n → Space := fun i => if cond i then w else -w
  let P : Fin n → Space × Space := fun i => (ρ⁻¹ • (x i - a i), ρ⁻¹ • (v i - b i))
  let f : Fin n → Fin (2 * N) :=
    fun i => finProdFinEquiv ((if cond i then 0 else 1 : Fin 2), κ (P i))
  refine ⟨f, ?_⟩
  have hPx : ∀ i ∈ F, ‖x i - a i‖ < 3 * ρ / 2 ∧ ‖v i - b i‖ < 2 * ρ := by
    intro i hi
    by_cases hc : cond i
    · simp only [a, b, hc, ite_true]; exact hc
    · simp only [a, b, hc, ite_false]
      rcases endpoint_alternative hδ (hF i hi).1 hw (hF i hi).2 with h' | h'
      · exact absurd h' hc
      · exact ⟨h'.1, by rw [sub_neg_eq_add]; exact h'.2⟩
  have hP : ∀ i ∈ F, ‖P i‖ ≤ 2 := by
    intro i hi
    obtain ⟨h1, h2⟩ := hPx i hi
    rw [Prod.norm_mk, norm_smul, norm_smul, norm_inv, Real.norm_of_nonneg hρ.le]
    apply max_le
    · rw [inv_mul_le_iff₀ hρ]; linarith
    · rw [inv_mul_le_iff₀ hρ]; linarith
  intro i hi j hj hij
  have hpair := finProdFinEquiv.injective hij
  rw [Prod.mk.injEq] at hpair
  obtain ⟨hflag, hk⟩ := hpair
  have hab : a j = a i ∧ b j = b i := by
    by_cases hi' : cond i <;> by_cases hj' : cond j <;>
      simp only [a, b, hi', hj', ite_true, ite_false, and_self] <;>
      simp only [hi', hj', ite_true, ite_false] at hflag <;> exact absurd hflag (by decide)
  have hdi := hκ (P i) (hP i hi)
  have hdj := hκ (P j) (hP j hj)
  rw [hk] at hdi
  have hPij : dist (P j) (P i) < 2 / 2048 := by
    calc dist (P j) (P i) ≤ dist (P j) (c (κ (P j))) + dist (c (κ (P j))) (P i) :=
          dist_triangle _ _ _
      _ < 1 / 2048 + 1 / 2048 := by rw [dist_comm (c _) (P i)]; exact add_lt_add hdj hdi
      _ = 2 / 2048 := by norm_num
  rw [Prod.dist_eq] at hPij
  have h1 : dist (P j).1 (P i).1 < 2 / 2048 := lt_of_le_of_lt (le_max_left _ _) hPij
  have h2 : dist (P j).2 (P i).2 < 2 / 2048 := lt_of_le_of_lt (le_max_right _ _) hPij
  have e1 : dist (P j).1 (P i).1 = ρ⁻¹ * ‖x j - x i‖ := by
    simp only [P, dist_eq_norm, hab.1]
    rw [← smul_sub, norm_smul, norm_inv, Real.norm_of_nonneg hρ.le]
    congr 2; abel
  have e2 : dist (P j).2 (P i).2 = ρ⁻¹ * ‖v j - v i‖ := by
    simp only [P, dist_eq_norm, hab.2]
    rw [← smul_sub, norm_smul, norm_inv, Real.norm_of_nonneg hρ.le]
    congr 2; abel
  rw [e1, inv_mul_lt_iff₀ hρ] at h1
  rw [e2, inv_mul_lt_iff₀ hρ] at h2
  exact tube_subset_of_close (ε := ρ / 1024) (by linarith) (by linarith) (by linarith)

end WangZahlLot.Obl.wz_coarse_subtube_selection
