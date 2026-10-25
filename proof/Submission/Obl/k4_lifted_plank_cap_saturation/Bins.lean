import Mathlib
import Submission.Lib.K4QuadraticSublevel

namespace Submission.Obl.k4_lifted_plank_cap_saturation

open Set MeasureTheory Metric

/-- A coefficient ball meets only a controlled number of ordinary coefficient bins. -/
theorem coefficient_ball_grid_cover (b : EuclideanSpace ℝ (Fin 3)) {R p : ℝ}
    (hR : 0 ≤ R) (hp : 0 < p) :
    ∃ Q : Finset (Fin 3 → ℤ),
      (Q.card : ℝ) ≤ (4 * R / p + 2) ^ 3 ∧
      ∀ x ∈ ball b R, (fun j : Fin 3 => ⌊x j / p⌋) ∈ Q := by
  classical
  let S : Fin 3 → Set ℝ := fun j => (fun x : EuclideanSpace ℝ (Fin 3) => x j) '' ball b R
  have hS (j : Fin 3) :
      ((fun x : ℝ => ⌊x / p⌋) '' S j).Finite ∧
        (((fun x : ℝ => ⌊x / p⌋) '' S j).ncard : ℝ) ≤ 4 * R / p + 2 := by
    simpa only [sub_zero, show (2 : ℝ) * (2 * R) = 4 * R by ring] using
      Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      (S j) (show 0 ≤ 2 * R by positivity) hp 0 (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        calc
          dist (x j) (y j) ≤ dist x y := PiLp.dist_apply_le _ _ _
          _ ≤ dist x b + dist y b := dist_triangle_right _ _ _
          _ ≤ 2 * R := by linarith [mem_ball.mp hx, mem_ball.mp hy])
  let B : Fin 3 → Finset ℤ := fun j => (hS j).1.toFinset
  refine ⟨Fintype.piFinset B, ?_, ?_⟩
  · calc
      ((Fintype.piFinset B).card : ℝ) = ∏ j : Fin 3, ((B j).card : ℝ) := by
        rw [Fintype.card_piFinset, Nat.cast_prod]
      _ ≤ ∏ _j : Fin 3, (4 * R / p + 2) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          positivity
        · intro j hj
          simpa only [B, ← Set.ncard_eq_toFinset_card] using (hS j).2
      _ = (4 * R / p + 2) ^ 3 := by simp
  · intro x hx
    apply Fintype.mem_piFinset.mpr
    intro j
    change ⌊x j / p⌋ ∈ (hS j).1.toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨x j, ⟨x, hx, rfl⟩, rfl⟩

/-- A uniform bound on ordinary coefficient bins bounds the mass in a coefficient ball. -/
theorem coefficient_ball_mass_le_of_bin_bounds
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (a : α → EuclideanSpace ℝ (Fin 3)) (G : Set α)
    (b : EuclideanSpace ℝ (Fin 3)) {R p T : ℝ}
    (hR : 0 ≤ R) (hp : 0 < p) (hT : 0 ≤ T)
    (hbins : ∀ q : Fin 3 → ℤ,
      ν {l | (∀ j : Fin 3, ⌊a l j / p⌋ = q j) ∧ l ∈ G} ≤ ENNReal.ofReal T) :
    ν {l | a l ∈ ball b R ∧ l ∈ G} ≤
      ENNReal.ofReal ((4 * R / p + 2) ^ 3 * T) := by
  classical
  obtain ⟨Q, hQcard, hQcover⟩ := coefficient_ball_grid_cover b hR hp
  have hsub : {l | a l ∈ ball b R ∧ l ∈ G} ⊆
      ⋃ q ∈ Q, {l | (∀ j : Fin 3, ⌊a l j / p⌋ = q j) ∧ l ∈ G} := by
    intro l hl
    exact mem_biUnion (hQcover (a l) hl.1) ⟨fun j => rfl, hl.2⟩
  calc
    ν {l | a l ∈ ball b R ∧ l ∈ G} ≤
        ∑ q ∈ Q, ν {l | (∀ j : Fin 3, ⌊a l j / p⌋ = q j) ∧ l ∈ G} :=
      (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _q ∈ Q, ENNReal.ofReal T := Finset.sum_le_sum fun q hq => hbins q
    _ = ENNReal.ofReal ((Q.card : ℝ) * T) := by
      simp [nsmul_eq_mul, ENNReal.ofReal_mul]
    _ ≤ ENNReal.ofReal ((4 * R / p + 2) ^ 3 * T) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hQcard hT)

/-- A ball with mass above the finite-bin cap contains a heavy ordinary coefficient bin. -/
theorem exists_heavy_coefficient_bin
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (a : α → EuclideanSpace ℝ (Fin 3)) (G : Set α)
    (b : EuclideanSpace ℝ (Fin 3)) {R p T : ℝ}
    (hR : 0 ≤ R) (hp : 0 < p) (hT : 0 ≤ T)
    (hmass : ENNReal.ofReal ((4 * R / p + 2) ^ 3 * T) <
      ν {l | a l ∈ ball b R ∧ l ∈ G}) :
    ∃ q : Fin 3 → ℤ,
      ENNReal.ofReal T ≤ ν {l | (∀ j : Fin 3, ⌊a l j / p⌋ = q j) ∧ l ∈ G} := by
  by_contra! h
  exact (not_lt_of_ge (coefficient_ball_mass_le_of_bin_bounds ν a G b hR hp hT
    (fun q => (h q).le))) hmass

end Submission.Obl.k4_lifted_plank_cap_saturation
