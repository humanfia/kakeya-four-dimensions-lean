/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

import Submission.Obl.k4_dyadic_crop_affine_laws.GrowthBounds

namespace Submission.Obl.k4_dyadic_crop_affine_laws

open Filter

/-- One ceiling valid for every retained world, including an empty retained set. -/
noncomputable def maxWorldCeiling {n : ℕ} (S : Finset (Fin n))
    (q : Fin n → ℝ) (a Λ : ℝ) : ℝ := by
  classical
  exact (insert 0 (S.image (fun i => a ^ 2 * Λ / q i))).sup' (by simp) id

lemma le_maxWorldCeiling {n : ℕ} (S : Finset (Fin n)) (q : Fin n → ℝ)
    (a Λ : ℝ) {i : Fin n} (hi : i ∈ S) : a ^ 2 * Λ / q i ≤ maxWorldCeiling S q a Λ := by
  classical
  unfold maxWorldCeiling
  apply Finset.le_sup' id
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

lemma maxWorldCeiling_nonneg {n : ℕ} (S : Finset (Fin n)) (q : Fin n → ℝ) (a Λ : ℝ) :
    0 ≤ maxWorldCeiling S q a Λ := by
  classical
  exact Finset.le_sup' id (Finset.mem_insert_self _ _)

lemma maxWorldCeiling_le {n : ℕ} (S : Finset (Fin n)) (q : Fin n → ℝ)
    (a Λ R : ℝ) (hR : 0 ≤ R) (h : ∀ i ∈ S, a ^ 2 * Λ / q i ≤ R) :
    maxWorldCeiling S q a Λ ≤ R := by
  classical
  apply Finset.sup'_le
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact hR
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    exact h i hi

lemma crop_slope_ratio_bound {N a Λ q u β ε : ℝ}
    (hN : 1 ≤ N) (_hε : 0 < ε)
    (hwidth : a ^ 2 ≤ 4 * N ^ (-2 * u))
    (hΛ : Λ ≤ N ^ (ε / 3)) (hconst : 4 ≤ N ^ (ε / 3))
    (hq : N ^ (-β - ε / 3) ≤ q) :
    a ^ 2 * Λ / q ≤ N ^ (-2 * u + β + ε) := by
  have hNpos : 0 < N := by linarith
  have hqpos : 0 < q := (Real.rpow_pos_of_pos hNpos _).trans_le hq
  calc
    a ^ 2 * Λ / q ≤ a ^ 2 * N ^ (ε / 3) / q :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ (sq_nonneg a)) hqpos.le
    _ ≤ (4 * N ^ (-2 * u)) * N ^ (ε / 3) / q :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hwidth (Real.rpow_nonneg hNpos.le _)) hqpos.le
    _ ≤ (4 * N ^ (-2 * u)) * N ^ (ε / 3) / N ^ (-β - ε / 3) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hq
    _ ≤ (N ^ (ε / 3) * N ^ (-2 * u)) * N ^ (ε / 3) / N ^ (-β - ε / 3) := by
      gcongr
    _ = N ^ (-2 * u + β + ε) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_sub hNpos]
      congr 1
      ring

/-- The exact maximum of all crop ceilings has logarithmic exponent `β-2u`.
Uniform prior-mass classes make this estimate independent of the world count. -/
theorem maxWorldCeiling_hasUpperExponent
    (N a Λ : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (n : ℕ → ℕ) (S : (k : ℕ) → Finset (Fin (n k)))
    (q : (k : ℕ) → Fin (n k) → ℝ) (u β : ℝ)
    (hwidth : ∀ k, a k ^ 2 ≤ 4 * N k ^ (-2 * u))
    (hΛ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Λ k ≤ N k ^ ε)
    (hq : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i ∈ S k,
      N k ^ (-β - ε) ≤ q k i) :
    HasUpperExponent N (fun k => maxWorldCeiling (S k) (q k) (a k) (Λ k)) (-2 * u + β) := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hlarge : ∀ᶠ k in atTop, 4 ≤ N k ^ (ε / 3) :=
    ((tendsto_rpow_atTop hε3).comp hN).eventually (eventually_ge_atTop 4)
  filter_upwards [hΛ (ε / 3) hε3, hq (ε / 3) hε3, hlarge] with k hΛk hqk hlargek
  apply maxWorldCeiling_le _ _ _ _ _ (Real.rpow_nonneg (by linarith [hN₂ k]) _)
  intro i hi
  exact crop_slope_ratio_bound (by linarith [hN₂ k]) hε (hwidth k) hΛk hlargek (hqk i hi)

end Submission.Obl.k4_dyadic_crop_affine_laws
