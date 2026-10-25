/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarRotatedFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarRotatedFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlaneRotation

/-! Planar forcing for centered scalar graphs of either sign. Only the
second planar family is translated during normalization. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set Metric
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped RealInnerProductSpace

theorem finite_rotated_planar_affine_fit (hproj : ProjectionDichotomy)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η p₀ : ℝ, 0 < η ∧ 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
    ∀ (K J : Finset ℤ) (t : ℤ → ℝ) (f : ℝ → ℝ) (b : ℤ → Plane)
      (T : Finset (ℤ × ℤ × ℤ)) (D : Set ℝ) (N e : ℝ),
      1 ≤ N → 33 * N < p ^ (ε - 1) → |e| = 1 →
      (∀ k ∈ K, |t k| ≤ 1 ∧ |f (t k)| ≤ |t k|) →
      (∀ k ∈ K, 0 ≤ e * t k) →
      (∀ k ∈ K, ∀ k' ∈ K, |f (t k) - f (t k')| ≤ |t k - t k'|) →
      (∀ j ∈ J, ∀ i : Fin 2, 0 ≤ b j i ∧ b j i ≤ 1) →
      (∀ k ∈ K, ((K.filter fun k' =>
        dist (graphPoint f (t k)) (graphPoint f (t k')) ≤ 4 * p).card : ℝ) ≤ N) →
      (∀ j ∈ J, ((J.filter fun j' => dist (b j) (b j') ≤ 2 * p).card : ℝ) ≤ N) →
      PlaneAD p (p ^ (-η)) ((fun k => diagonalPoint e (t k) (f (t k))) '' (K : Set ℤ)) →
      PlaneAD p (p ^ (-η)) (b '' (J : Set ℤ)) →
      T ⊆ K ×ˢ (J ×ˢ J) → N ^ 3 * p ^ (η - 3) ≤ (T.card : ℝ) →
      IntervalAD p (1 - σ) (p ^ (-η)) D →
      (∀ q ∈ T, ⟪diagonalPoint e (t q.1) (f (t q.1)), b q.2.1 - b q.2.2⟫ ∈ D) →
      ∃ (K' : Finset ℤ) (a v : ℝ), K' ⊆ K ∧ p ^ (ε - 1) ≤ (K'.card : ℝ) ∧
        |a| ≤ 9 ∧ |v| ≤ 4 ∧ ∀ k ∈ K', |f (t k) - (a + v * t k)| ≤ 8 * p := by
  classical
  obtain ⟨η, p₀, hη, hp₀, hfinite⟩ :=
    finiteDichotomy_of_projection hproj hσ hσ1 ε hε
  refine ⟨η, min p₀ (1 / 2), hη, lt_min hp₀ (by norm_num), ?_⟩
  intro p hp hpmax K J t f b T D N e hN hlarge he hbounded hsign hf hb hmA hmB hADa hADb hT hcard hD hdot
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have heSq : e ^ 2 = 1 := by simpa only [he, one_pow] using (sq_abs e).symm
  let δ := Real.sqrt (2 : ℝ) * p
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtle : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hδ : 0 < δ := mul_pos hsqrt hp
  have hδle : δ ≤ 2 * p := mul_le_mul_of_nonneg_right hsqrtle hp.le
  have hδ1 : δ ≤ 1 := by linarith [hpmax.trans (min_le_right p₀ (1 / 2))]
  have haunit : ∀ k ∈ K, ∀ i : Fin 2,
      0 ≤ diagonalPoint e (t k) (f (t k)) i ∧ diagonalPoint e (t k) (f (t k)) i ≤ 1 :=
    fun k hk => diagonalPoint_unit he (hbounded k hk).1 (hbounded k hk).2 (hsign k hk)
  have hmA' : ∀ k ∈ K, ((K.filter fun k' =>
      dist (diagonalPoint e (t k) (f (t k))) (diagonalPoint e (t k') (f (t k'))) ≤ 2 * p).card : ℝ) ≤ N := by
    intro k hk
    apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hmA k hk)
    intro k' hk'
    obtain ⟨hk'K, hd⟩ := Finset.mem_filter.mp hk'
    refine Finset.mem_filter.mpr ⟨hk'K, ?_⟩
    have hdist := diagonalPoint_original_dist_le e heSq (t k) (f (t k)) (t k') (f (t k'))
    change dist (!₂[t k, f (t k)] : ScalarPlane) !₂[t k', f (t k')] ≤ 4 * p
    nlinarith only [hdist, hd]
  obtain ⟨n, c, hn, hcount⟩ := hfinite p hp (hpmax.trans (min_le_left _ _))
    K J (fun k => diagonalPoint e (t k) (f (t k))) b T D haunit hb N hN hmA' hmB
    hADa hADb hT hcard hD hdot
  let K' := K.filter fun k => |⟪diagonalPoint e (t k) (f (t k)), n⟫ - c| < p
  have hsub : K' ⊆ K := Finset.filter_subset _ _
  have hcount' : p ^ (ε - 1) ≤ (K'.card : ℝ) := hcount
  have hmult : ∀ k ∈ K', ((K'.filter fun k' =>
      dist (graphPoint f (t k)) (graphPoint f (t k')) ≤ 2 * δ).card : ℝ) ≤ N := by
    intro k hk
    apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hmA k (hsub hk))
    intro k' hk'
    obtain ⟨hk'K, hd⟩ := Finset.mem_filter.mp hk'
    exact Finset.mem_filter.mpr ⟨hsub hk'K, hd.trans (by linarith)⟩
  have hcov : CoverLower ((fun k => graphPoint f (t k)) '' (K' : Set ℤ)) δ
      (p ^ (ε - 1) / N) := by
    apply coverLower_of_card K' _ hNpos hmult
    simpa [mul_div_cancel₀ _ hNpos.ne'] using hcount'
  let Z := t '' (K' : Set ℤ)
  have hcovZ : CoverLower (graphPoint f '' Z) δ (p ^ (ε - 1) / N) := by
    simpa only [Z, Set.image_image, Function.comp_def] using hcov
  have hfl : ∀ x ∈ Z, ∀ y ∈ Z, |f x - f y| ≤ |x - y| := by
    rintro x ⟨k, hk, rfl⟩ y ⟨k', hk', rfl⟩
    exact hf k (hsub hk) k' (hsub hk')
  let n₀ := (signedPlaneRotation e heSq).symm n
  have hn₀ : ‖n₀‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hn
  have hstrip : ∀ z ∈ Z, |n₀ 0 * z + n₀ 1 * f z - Real.sqrt 2 * c| ≤ δ := by
    rintro z ⟨k, hk, rfl⟩
    have hh := diagonalPoint_strip_transfer e heSq (t k) (f (t k)) c p n
      (Finset.mem_filter.mp hk).2.le
    simpa [n₀, δ, PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using hh
  have hsep := separated_pair_of_graph_coverLower hδ
    ((lt_div_iff₀ hNpos).mpr hlarge) hfl hcovZ
  obtain ⟨a, v, hv, hfit⟩ := affine_of_strip_with_slope hn₀ hδ.le hfl hstrip hsep
  have hnonempty : K'.Nonempty := by
    by_contra hnK
    simp only [Finset.not_nonempty_iff_eq_empty.mp hnK, Finset.card_empty, Nat.cast_zero] at hcount'
    exact (not_le_of_gt (Real.rpow_pos_of_pos hp _)) hcount'
  obtain ⟨k₀, hk₀⟩ := hnonempty
  have hk₀Z : t k₀ ∈ Z := ⟨k₀, hk₀, rfl⟩
  have htk₀ := (hbounded k₀ (hsub hk₀)).1
  have hfk₀ := (hbounded k₀ (hsub hk₀)).2.trans htk₀
  have ha : |a| ≤ 9 := by
    have hvt : |v * t k₀| ≤ 4 := by
      rw [abs_mul]
      nlinarith [abs_nonneg v, abs_nonneg (t k₀)]
    have hh := (abs_sub (f (t k₀)) (f (t k₀) - (a + v * t k₀))).trans
      (add_le_add le_rfl (hfit _ hk₀Z))
    have ht := abs_sub (f (t k₀) - (f (t k₀) - (a + v * t k₀))) (v * t k₀)
    have heq : f (t k₀) - (f (t k₀) - (a + v * t k₀)) - v * t k₀ = a := by ring
    rw [heq] at ht
    linarith
  exact ⟨K', a, v, hsub, hcount', ha, hv, fun k hk =>
    (hfit _ ⟨k, hk, rfl⟩).trans (by linarith)⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
