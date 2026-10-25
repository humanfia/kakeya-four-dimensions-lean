/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarMeasuredFit.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarMeasuredFit.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCollisionGraphFit
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCellMass

/-! Passing from original collision mass and cell ceilings to a row fit.
The sign is chosen only after the original occupied tuples are counted. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open WangZahlLot.Obl.wz_slab_local_linearity

theorem original_mass_scalar_collision_fit (hproj : ProjectionDichotomy)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η p₀ : ℝ, 0 < η ∧ 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
      (E : Set Ω) (code : Ω → ℤ × ℤ × ℤ) (K J : Finset ℤ)
      (t v : ℤ → ℝ) (f G : ℝ → ℝ) (S : Set ℝ) (B L C N shift c : ℝ) (n : ℕ),
      1 ≤ B → 0 ≤ L → 0 ≤ C → 11 ≤ N → 16 * B + 3 ≤ N →
      33 * N < p ^ (ε - 1) → 0 < c →
      (∀ k ∈ K, |t k| ≤ 1 ∧ |f (t k)| ≤ |t k|) →
      (∀ k ∈ K, ∀ k' ∈ K, |f (t k) - f (t k')| ≤ |t k - t k'|) →
      (∀ j ∈ J, |v j| ≤ B ∧ |G (v j)| ≤ B) →
      (∀ j ∈ J, ∀ j' ∈ J, |G (v j) - G (v j')| ≤ L * |v j - v j'|) →
      (∀ k ∈ K, ⌊t k / p⌋ = k) → (∀ j ∈ J, ⌊v j / p⌋ = j) →
      11 ≤ p ^ (-η) → 4 * (L + 1) + 3 ≤ p ^ (-η) →
      (2 * (n : ℝ) + 3) * C * (1 + 2 * (n : ℝ)) ^ (1 - σ) ≤ p ^ (-η) →
      (∀ᵐ x ∂μ, x ∈ E → code x ∈ K ×ˢ (J ×ˢ J)) →
      (∀ q ∈ K ×ˢ (J ×ˢ J), μ.real (E ∩ code ⁻¹' {q}) ≤ c) →
      2 * (N ^ 3 * p ^ (η - 3)) * c ≤ μ.real E →
      IntervalAD p (1 - σ) C S →
      (∀ x ∈ E, ∃ s ∈ S,
        |t (code x).1 * (G (v (code x).2.1) - G (v (code x).2.2)) +
          f (t (code x).1) * (v (code x).2.1 - v (code x).2.2) - (s + shift)| ≤ (n : ℝ) * p) →
      ∃ (K' : Finset ℤ) (a slope : ℝ), K' ⊆ K ∧ p ^ (ε - 1) ≤ (K'.card : ℝ) ∧
        |a| ≤ 9 ∧ |slope| ≤ 4 ∧ ∀ k ∈ K', |f (t k) - (a + slope * t k)| ≤ 8 * p := by
  classical
  obtain ⟨η, p₀, hη, hp₀, hfit⟩ := finite_scalar_collision_graph_fit hproj hσ hσ1 hε
  refine ⟨η, p₀, hη, hp₀, ?_⟩
  intro p hp hpmax Ω _ μ _ E code K J t v f G S B L C N shift c n hB hL hC hNA hNB
    hlarge hc hunit hf hb hG htgrid hvgrid hbudgetA hbudgetB hbudgetD hcover hcap hmass hS hnear
  obtain ⟨T, hTK, hcount, hrep⟩ := original_positive_cells μ E code (K ×ˢ (J ×ˢ J)) hcover hc hcap
  obtain ⟨e, T', he, hTT, hhalf, hsign⟩ := exists_signed_half T (fun q => t q.1)
  let Ke := K.filter (fun k => 0 ≤ e * t k)
  have hKe : Ke ⊆ K := Finset.filter_subset _ _
  have hT' : T' ⊆ Ke ×ˢ (J ×ˢ J) := by
    intro q hq
    obtain ⟨hk, hj⟩ := Finset.mem_product.mp (hTK (hTT hq))
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hk, hsign q hq⟩, hj⟩
  have hmass' : 2 * (N ^ 3 * p ^ (η - 3)) ≤ μ.real E / c :=
    (le_div_iff₀ hc).mpr hmass
  have hdense : N ^ 3 * p ^ (η - 3) ≤ (T'.card : ℝ) := by
    linarith
  have hnear' : ∀ q ∈ T', ∃ s ∈ S,
      |t q.1 * (G (v q.2.1) - G (v q.2.2)) + f (t q.1) * (v q.2.1 - v q.2.2) -
        (s + shift)| ≤ (n : ℝ) * p := by
    intro q hq
    obtain ⟨x, hx, hcode⟩ := hrep q (hTT hq)
    simpa only [hcode] using hnear x hx
  obtain ⟨K', a, slope, hKK, hcard, ha, hv, hrow⟩ :=
    hfit p hp hpmax Ke J t v f G T' S B L C N e shift n hB hL hC hNA hNB hlarge he
      (fun k hk => hunit k (hKe hk))
      (fun k hk => (Finset.mem_filter.mp hk).2)
      (fun k hk k' hk' => hf k (hKe hk) k' (hKe hk')) hb hG
      (fun k hk => htgrid k (hKe hk)) hvgrid hbudgetA hbudgetB hbudgetD hT' hdense hS hnear'
  exact ⟨K', a, slope, fun k hk => hKe (hKK hk), hcard, ha, hv, hrow⟩

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
