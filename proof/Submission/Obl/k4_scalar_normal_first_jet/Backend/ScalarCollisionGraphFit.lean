/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCollisionGraphFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCollisionGraphFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGraphMultiplicity
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarRotatedFit

/-! The finite scalar collision-graph kernel. Its hypotheses are scalar
Lipschitz comparisons, original mesh indices and a scalar support bound;
plane AD, multiplicity and normalization data are all derived internally. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set Metric
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped RealInnerProductSpace

theorem finite_scalar_collision_graph_fit (hproj : ProjectionDichotomy)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η p₀ : ℝ, 0 < η ∧ 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
    ∀ (K J : Finset ℤ) (t v : ℤ → ℝ) (f G : ℝ → ℝ)
      (T : Finset (ℤ × ℤ × ℤ)) (S : Set ℝ) (B L C N e shift : ℝ) (n : ℕ),
      1 ≤ B → 0 ≤ L → 0 ≤ C → 11 ≤ N → 16 * B + 3 ≤ N →
      33 * N < p ^ (ε - 1) → |e| = 1 →
      (∀ k ∈ K, |t k| ≤ 1 ∧ |f (t k)| ≤ |t k|) →
      (∀ k ∈ K, 0 ≤ e * t k) →
      (∀ k ∈ K, ∀ k' ∈ K, |f (t k) - f (t k')| ≤ |t k - t k'|) →
      (∀ j ∈ J, |v j| ≤ B ∧ |G (v j)| ≤ B) →
      (∀ j ∈ J, ∀ j' ∈ J, |G (v j) - G (v j')| ≤ L * |v j - v j'|) →
      (∀ k ∈ K, ⌊t k / p⌋ = k) → (∀ j ∈ J, ⌊v j / p⌋ = j) →
      11 ≤ p ^ (-η) → 4 * (L + 1) + 3 ≤ p ^ (-η) →
      (2 * (n : ℝ) + 3) * C * (1 + 2 * (n : ℝ)) ^ (1 - σ) ≤ p ^ (-η) →
      T ⊆ K ×ˢ (J ×ˢ J) → N ^ 3 * p ^ (η - 3) ≤ (T.card : ℝ) →
      IntervalAD p (1 - σ) C S →
      (∀ q ∈ T, ∃ s ∈ S,
        |t q.1 * (G (v q.2.1) - G (v q.2.2)) + f (t q.1) * (v q.2.1 - v q.2.2) -
          (s + shift)| ≤ (n : ℝ) * p) →
      ∃ (K' : Finset ℤ) (a slope : ℝ), K' ⊆ K ∧ p ^ (ε - 1) ≤ (K'.card : ℝ) ∧
        |a| ≤ 9 ∧ |slope| ≤ 4 ∧ ∀ k ∈ K', |f (t k) - (a + slope * t k)| ≤ 8 * p := by
  classical
  obtain ⟨η, p₀, hη, hp₀, hfit⟩ := finite_rotated_planar_affine_fit hproj hσ hσ1 hε
  refine ⟨η, p₀, hη, hp₀, ?_⟩
  intro p hp hpmax K J t v f G T S B L C N e shift n hB hL hC hNA hNB hlarge he
    hbounded hsign hf hb hG htgrid hvgrid hbudgetA hbudgetB hbudgetD hT hcard hS hnear
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have heSq : e ^ 2 = 1 := by simpa only [he, one_pow] using (sq_abs e).symm
  let b : ℤ → Plane := fun j => boxedDiagonalPoint e B (G (v j)) (v j)
  have hbunit : ∀ j ∈ J, ∀ i : Fin 2, 0 ≤ b j i ∧ b j i ≤ 1 :=
    fun j hj => boxedDiagonalPoint_unit he hBpos (hb j hj).2 (hb j hj).1
  have hmA : ∀ k ∈ K, ((K.filter fun k' =>
      dist (graphPoint f (t k)) (graphPoint f (t k')) ≤ 4 * p).card : ℝ) ≤ N :=
    fun k hk => (graph_grid_multiplicity hp K t f htgrid k hk).trans hNA
  have hmB : ∀ j ∈ J, ((J.filter fun j' => dist (b j) (b j') ≤ 2 * p).card : ℝ) ≤ N :=
    fun j hj => (boxed_grid_multiplicity hp hBpos e heSq J v G hvgrid j hj).trans hNB
  have hfl : ∀ x ∈ t '' (K : Set ℤ), ∀ y ∈ t '' (K : Set ℤ),
      |f x - f y| ≤ 1 * |x - y| := by
    rintro x ⟨k, hk, rfl⟩ y ⟨k', hk', rfl⟩
    simpa only [one_mul] using hf k hk k' hk'
  have hADa₀ : PlaneAD p 11 ((fun k => diagonalPoint e (t k) (f (t k))) '' (K : Set ℤ)) := by
    have h := diagonal_graph_planeAD hp (by norm_num : (0 : ℝ) ≤ 1) heSq (t '' (K : Set ℤ)) f hfl
    norm_num at h
    simpa only [Set.image_image, Function.comp_def] using h
  have hGl : ∀ x ∈ v '' (J : Set ℤ), ∀ y ∈ v '' (J : Set ℤ),
      |G x - G y| ≤ L * |x - y| := by
    rintro x ⟨j, hj, rfl⟩ y ⟨j', hj', rfl⟩
    exact hG j hj j' hj'
  have hADb₀ : PlaneAD p (4 * (L + 1) + 3) (b '' (J : Set ℤ)) := by
    have h := boxed_graph_planeAD (B := B) hp hL heSq (v '' (J : Set ℤ)) G hGl
    simpa only [b, Set.image_image, Function.comp_def] using h
  let D₀ : Set ℝ := {z | ∃ s ∈ S, |z - (s + shift)| ≤ (n : ℝ) * p}
  let scale : ℝ := 1 / (4 * B)
  let D : Set ℝ := (fun z => scale * z + 0) '' D₀
  have hscale : 0 < scale := one_div_pos.mpr (mul_pos (by norm_num) hBpos)
  have hscale1 : scale ≤ 1 := by
    apply (div_le_one (mul_pos (by norm_num) hBpos)).mpr
    linarith
  have hD₀ : IntervalAD p (1 - σ)
      ((2 * (n : ℝ) + 3) * C * (1 + 2 * (n : ℝ)) ^ (1 - σ)) D₀ :=
    intervalAD_nearby hp (by linarith) hC n hS (fun z hz => hz)
  have hscaled := intervalAD_contract (b := 0) hp hscale hscale1 hD₀
  have hD : IntervalAD p (1 - σ) (p ^ (-η)) D :=
    (show CellProofs.Assouad p (1 - σ)
      ((2 * (n : ℝ) + 3) * C * (1 + 2 * (n : ℝ)) ^ (1 - σ)) D from hscaled).mono_constant hp hbudgetD
  have hdot : ∀ q ∈ T, ⟪diagonalPoint e (t q.1) (f (t q.1)), b q.2.1 - b q.2.2⟫ ∈ D := by
    intro q hq
    refine ⟨t q.1 * (G (v q.2.1) - G (v q.2.2)) + f (t q.1) * (v q.2.1 - v q.2.2),
      hnear q hq, ?_⟩
    dsimp [b]
    rw [boxedDiagonalPoint_dot e heSq B hBpos.ne']
    simp only [scale, add_zero]
  exact hfit p hp hpmax K J t f b T D N e (by linarith) hlarge he hbounded hsign hf hbunit
    hmA hmB (PlaneAD.mono_constant hp hbudgetA hADa₀) (PlaneAD.mono_constant hp hbudgetB hADb₀)
    hT hcard hD hdot

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
