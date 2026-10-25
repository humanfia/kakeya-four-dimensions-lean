/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarPlanar.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarPlanar.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib
import Submission.WZ.Obl.wz_slab_local_linearity.Dichotomy

/-!
# Affine fitting from scalar collision triples

The geometric dot-product argument is imported from `WangZahlLot`. This module
adapts its finite indexed conclusion to an affine fit of a common scalar row.
The indices of the selected time cells, and therefore their original label
sets, are retained explicitly.
-/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_slab_local_linearity
open scoped ENNReal

/-- Scalar collision triples force a common affine row on many represented
time cells. The multiplicity bound permits repeated or nearby graph points.
All the covering inputs concern the displayed, original indexed triples. -/
theorem finite_planar_affine_fit (hproj : ProjectionDichotomy)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η p₀ : ℝ, 0 < η ∧ 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
    ∀ (K J : Finset ℤ) (t : ℤ → ℝ) (f : ℝ → ℝ) (b : ℤ → Plane)
      (T : Finset (ℤ × ℤ × ℤ)) (D : Set ℝ) (N : ℝ),
      1 ≤ N → 33 * N < p ^ (ε - 1) →
      (∀ k ∈ K, t k ∈ Icc (0 : ℝ) 1 ∧ f (t k) ∈ Icc (0 : ℝ) 1) →
      (∀ k ∈ K, ∀ k' ∈ K, |f (t k) - f (t k')| ≤ |t k - t k'|) →
      (∀ j ∈ J, ∀ i : Fin 2, 0 ≤ b j i ∧ b j i ≤ 1) →
      (∀ k ∈ K, ((K.filter fun k' =>
        dist (graphPoint f (t k)) (graphPoint f (t k')) ≤ 2 * p).card : ℝ) ≤ N) →
      (∀ j ∈ J, ((J.filter fun j' => dist (b j) (b j') ≤ 2 * p).card : ℝ) ≤ N) →
      PlaneAD p (p ^ (-η)) ((fun k => graphPoint f (t k)) '' (K : Set ℤ)) →
      PlaneAD p (p ^ (-η)) (b '' (J : Set ℤ)) →
      T ⊆ K ×ˢ (J ×ˢ J) → N ^ 3 * p ^ (η - 3) ≤ (T.card : ℝ) →
      IntervalAD p (1 - σ) (p ^ (-η)) D →
      (∀ q ∈ T, inner ℝ (graphPoint f (t q.1)) (b q.2.1 - b q.2.2) ∈ D) →
      ∃ (K' : Finset ℤ) (a v : ℝ), K' ⊆ K ∧
        p ^ (ε - 1) ≤ (K'.card : ℝ) ∧ |a| ≤ 9 ∧ |v| ≤ 4 ∧
        ∀ k ∈ K', |f (t k) - (a + v * t k)| ≤ 4 * p := by
  classical
  obtain ⟨η, p₀, hη, hp₀, hfinite⟩ :=
    finiteDichotomy_of_projection hproj hσ hσ1 ε hε
  refine ⟨η, min p₀ 1, hη, lt_min hp₀ zero_lt_one, ?_⟩
  intro p hp hpmax K J t f b T D N hN hlarge hunit hf hb hmA hmB hADa hADb hT hcard hD hdot
  have hp₁ : p ≤ 1 := hpmax.trans (min_le_right _ _)
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hunit' : ∀ k ∈ K, ∀ i : Fin 2,
      0 ≤ graphPoint f (t k) i ∧ graphPoint f (t k) i ≤ 1 := by
    intro k hk i
    fin_cases i
    · simpa [graphPoint] using (hunit k hk).1
    · simpa [graphPoint] using (hunit k hk).2
  obtain ⟨e, c, he, hcount⟩ := hfinite p hp (hpmax.trans (min_le_left _ _))
    K J (fun k => graphPoint f (t k)) b T D hunit' hb N hN hmA hmB hADa hADb
    hT hcard hD hdot
  let K' := K.filter fun k => |inner ℝ (graphPoint f (t k)) e - c| < p
  have hsub : K' ⊆ K := Finset.filter_subset _ _
  have hcount' : p ^ (ε - 1) ≤ (K'.card : ℝ) := hcount
  have hmult : ∀ k ∈ K', ((K'.filter fun k' =>
      dist (graphPoint f (t k)) (graphPoint f (t k')) ≤ 2 * p).card : ℝ) ≤ N := by
    intro k hk
    exact (Nat.cast_le.mpr (Finset.card_le_card
      (Finset.filter_subset_filter _ hsub))).trans (hmA k (hsub hk))
  have hcov : CoverLower ((fun k => graphPoint f (t k)) '' (K' : Set ℤ)) p
      (p ^ (ε - 1) / N) := by
    apply coverLower_of_card K' _ hNpos hmult
    simpa [mul_div_cancel₀ _ hNpos.ne'] using hcount'
  let Z := t '' (K' : Set ℤ)
  have hcovZ : CoverLower (graphPoint f '' Z) p (p ^ (ε - 1) / N) := by
    simpa only [Z, Set.image_image, Function.comp_def] using hcov
  have hfl : ∀ x ∈ Z, ∀ y ∈ Z, |f x - f y| ≤ |x - y| := by
    rintro x ⟨k, hk, rfl⟩ y ⟨k', hk', rfl⟩
    exact hf k (hsub hk) k' (hsub hk')
  have hstrip : ∀ z ∈ Z, |e 0 * z + e 1 * f z - c| ≤ p := by
    rintro z ⟨k, hk, rfl⟩
    have hh := (Finset.mem_filter.mp hk).2.le
    simpa [PiLp.inner_apply, Fin.sum_univ_two, graphPoint, mul_comm] using hh
  have hsep := separated_pair_of_graph_coverLower hp
    ((lt_div_iff₀ hNpos).mpr hlarge) hfl hcovZ
  obtain ⟨a, v, hv, hfit⟩ := affine_of_strip_with_slope he hp.le hfl hstrip hsep
  have hnonempty : K'.Nonempty := by
    by_contra hn
    simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty,
      Nat.cast_zero] at hcount'
    exact (not_le_of_gt (Real.rpow_pos_of_pos hp _)) hcount'
  obtain ⟨k₀, hk₀⟩ := hnonempty
  have hk₀Z : t k₀ ∈ Z := ⟨k₀, hk₀, rfl⟩
  have htk₀ : |t k₀| ≤ 1 := abs_le.mpr ⟨by linarith [(hunit k₀ (hsub hk₀)).1.1],
    (hunit k₀ (hsub hk₀)).1.2⟩
  have hfk₀ : |f (t k₀)| ≤ 1 := abs_le.mpr
    ⟨by linarith [(hunit k₀ (hsub hk₀)).2.1], (hunit k₀ (hsub hk₀)).2.2⟩
  have ha : |a| ≤ 9 := by
    have hvt : |v * t k₀| ≤ 4 := by
      rw [abs_mul]
      nlinarith [abs_nonneg v, abs_nonneg (t k₀)]
    calc
      |a| = |f (t k₀) - (f (t k₀) - (a + v * t k₀)) - v * t k₀| := by
        congr 1; ring
      _ ≤ |f (t k₀)| + |f (t k₀) - (a + v * t k₀)| + |v * t k₀| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 9 := by linarith [hfit _ hk₀Z]
  exact ⟨K', a, v, hsub, hcount', ha, hv, fun k hk => hfit _ ⟨k, hk, rfl⟩⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
