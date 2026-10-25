/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ScalarGridGlobal.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarGridCovering
import Submission.Lib.K4QuadraticSublevel

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set Metric

noncomputable section

theorem ScalarGridCovers.mono_constant {grid S : Set ℝ} {d K K' : ℝ}
    (h : ScalarGridCovers grid d K S) (hKK : K ≤ K') : ScalarGridCovers grid d K' S := by
  constructor
  · intro r hr R hR hr₀ hrR a
    obtain ⟨m, c, hcover, hcard⟩ := h.local_cover r hr R hR hr₀ hrR a
    have hR₀ : 0 < R := hr₀.trans_le hrR
    exact ⟨m, c, hcover, hcard.trans (mul_le_mul_of_nonneg_right hKK (by positivity))⟩
  · intro r hr hr₀ hr₁
    obtain ⟨m, c, hcover, hcard⟩ := h.global_cover r hr hr₀ hr₁
    exact ⟨m, c, hcover, hcard.trans (mul_le_mul_of_nonneg_right hKK (by positivity))⟩

/-- Local grid covers give global grid covers by combining the finitely
many occupied unit intervals. -/
theorem scalar_grid_covers_of_unit_bins {grid S : Set ℝ} {d K : ℝ}
    (hK : 0 ≤ K) (hunit : (1 : ℝ) ∈ grid)
    (hlocal : ∀ r ∈ grid, ∀ R ∈ grid, 0 < r → r ≤ R → ∀ a,
      ∃ (m : ℕ) (c : Fin m → ℝ), S ∩ Icc a (a + R) ⊆ ⋃ j, closedBall (c j) r ∧
        (m : ℝ) ≤ K * (R / r) ^ d)
    (B : Finset ℤ) (hB : ∀ x ∈ S, ⌊x⌋ ∈ B) :
    ScalarGridCovers grid d (((B.card : ℝ) + 1) * K) S := by
  classical
  have hKK : K ≤ ((B.card : ℝ) + 1) * K := by
    nlinarith only [mul_nonneg (Nat.cast_nonneg B.card) hK]
  constructor
  · intro r hr R hR hr₀ hrR a
    obtain ⟨m, c, hcover, hcard⟩ := hlocal r hr R hR hr₀ hrR a
    have hR₀ : 0 < R := hr₀.trans_le hrR
    exact ⟨m, c, hcover, hcard.trans (mul_le_mul_of_nonneg_right hKK (by positivity))⟩
  · intro r hr hr₀ hr₁
    have hband (j : B) := hlocal r hr 1 hunit hr₀ hr₁ (j.val : ℝ)
    choose m c hcover hcard using hband
    let ι := Σ j : B, Fin (m j)
    let e := Fintype.equivFin ι
    refine ⟨Fintype.card ι, fun i => c (e.symm i).1 (e.symm i).2, ?_, ?_⟩
    · intro x hx
      let j : B := ⟨⌊x⌋, hB x hx⟩
      have hxband : x ∈ S ∩ Icc (j.val : ℝ) ((j.val : ℝ) + 1) :=
        ⟨hx, Int.floor_le x, (Int.lt_floor_add_one x).le⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover j hxband)
      refine mem_iUnion.mpr ⟨e ⟨j, i⟩, ?_⟩
      change x ∈ closedBall (c (e.symm (e ⟨j, i⟩)).1 (e.symm (e ⟨j, i⟩)).2) r
      rw [e.symm_apply_apply]
      exact hi
    · have hsum : (Fintype.card ι : ℝ) ≤ (B.card : ℝ) * (K * (1 / r) ^ d) := by
        change (Fintype.card (Σ j : B, Fin (m j)) : ℝ) ≤ _
        rw [Fintype.card_sigma]
        simp only [Fintype.card_fin, Nat.cast_sum]
        calc
          (∑ j : B, (m j : ℝ)) ≤ ∑ _j : B, K * (1 / r) ^ d :=
            Finset.sum_le_sum (fun j _ => hcard j)
          _ = _ := by simp
      have hnonneg : 0 ≤ K * (1 / r) ^ d :=
        mul_nonneg hK (Real.rpow_nonneg (by positivity : 0 ≤ 1 / r) d)
      exact hsum.trans (by nlinarith only [hnonneg])

/-- Bounded scalar support needs only the local finite-grid estimates;
the global cover costs a fixed linear factor in the scalar bound. -/
theorem scalar_grid_covers_of_bounded {grid S : Set ℝ} {d K U : ℝ}
    (hK : 0 ≤ K) (hU : 0 ≤ U) (hunit : (1 : ℝ) ∈ grid)
    (hbound : ∀ x ∈ S, |x| ≤ U)
    (hlocal : ∀ r ∈ grid, ∀ R ∈ grid, 0 < r → r ≤ R → ∀ a,
      ∃ (m : ℕ) (c : Fin m → ℝ), S ∩ Icc a (a + R) ⊆ ⋃ j, closedBall (c j) r ∧
        (m : ℝ) ≤ K * (R / r) ^ d) :
    ScalarGridCovers grid d ((4 * U + 3) * K) S := by
  classical
  have hbins := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le S
    (by positivity : 0 ≤ 2 * U) (by norm_num : (0 : ℝ) < 1) 0 (by
      intro x hx y hy
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans ((add_le_add (hbound x hx) (hbound y hy)).trans_eq (by ring)))
  let B := hbins.1.toFinset
  have hB (x : ℝ) (hx : x ∈ S) : ⌊x⌋ ∈ B :=
    hbins.1.mem_toFinset.mpr ⟨x, hx, by simp only [sub_zero, div_one]⟩
  have hcard : (B.card : ℝ) ≤ 4 * U + 2 := by
    rw [← Set.ncard_eq_toFinset_card _ hbins.1]
    exact hbins.2.trans_eq (by ring)
  exact (scalar_grid_covers_of_unit_bins hK hunit hlocal B hB).mono_constant
    (mul_le_mul_of_nonneg_right (by linarith : (B.card : ℝ) + 1 ≤ 4 * U + 3) hK)

end

end Submission.Obl.k4_scalar_graph_residual_discovery
