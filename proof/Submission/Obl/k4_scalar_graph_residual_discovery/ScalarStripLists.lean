/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file ScalarStripLists.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.ScalarGridGlobal
import Submission.Obl.k4_scalar_grid_parameter_preparation.TraceRectangle

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set Metric
open Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

theorem normalized_strip_gap {ρ r n n' : ℝ} (hr : 0 < r)
    (hbin : (⌊n / (ρ * r)⌋ : ℤ) = ⌊n' / (ρ * r)⌋) : |n / ρ - n' / ρ| ≤ r := by
  have hn : n / ρ ∈ scalarVelocityBin r ⌊n / (ρ * r)⌋ := by
    change ⌊(n / ρ) / r⌋ = ⌊n / (ρ * r)⌋
    rw [div_div]
  have hn' : n' / ρ ∈ scalarVelocityBin r ⌊n / (ρ * r)⌋ := by
    change ⌊(n' / ρ) / r⌋ = ⌊n / (ρ * r)⌋
    rw [div_div]
    exact hbin.symm
  simpa only [Real.dist_eq] using scalarVelocityBin_diameter_le hr hn hn'

/-- Moving along the entire assigned strip doubles the scalar error.
This allows filling to use the whole strip, rather than a single time slice. -/
theorem scalar_error_of_same_strip {ρ r n n' s shift : ℝ} (hr : 0 < r)
    (hbin : (⌊n / (ρ * r)⌋ : ℤ) = ⌊n' / (ρ * r)⌋)
    (hnear : |s - (n / ρ - shift)| ≤ r) : |s - (n' / ρ - shift)| ≤ 2 * r := by
  have hgap : |(n / ρ - shift) - (n' / ρ - shift)| ≤ r := by
    rw [show (n / ρ - shift) - (n' / ρ - shift) = n / ρ - n' / ρ by ring]
    exact normalized_strip_gap hr hbin
  exact (abs_sub_le _ (n / ρ - shift) _).trans ((add_le_add hnear hgap).trans_eq (by ring))

/-- A scalar interval of width R gives a normal band of width at most
(1+2e)*rho*R when the scalar error is e*r and r<=R. -/
theorem normal_band_of_scalar_interval {ρ r R e n s shift a : ℝ}
    (hρ : 0 < ρ) (he : 0 ≤ e) (hrR : r ≤ R)
    (hs : s ∈ Icc a (a + R)) (hnear : |s - (n / ρ - shift)| ≤ e * r) :
    n ∈ Icc (ρ * (a + shift - e * r))
      (ρ * (a + shift - e * r) + (1 + 2 * e) * ρ * R) := by
  have hh := abs_le.mp hnear
  have hlo := (le_div_iff₀ hρ).mp
    (by linarith only [hs.1, hh.2] : a + shift - e * r ≤ n / ρ)
  have hhi := (div_le_iff₀ hρ).mp
    (by linarith only [hs.2, hh.1] : n / ρ ≤ a + R + shift + e * r)
  have hwidth : 0 ≤ (2 * e * ρ) * (R - r) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hrR)
  constructor <;> nlinarith only [hlo, hhi, hwidth]

/-- A scalar witness at one time localizes the WHOLE assigned strip in
a normal band. All its other times remain available for planar filling. -/
theorem whole_strip_band_of_scalar_witness {ρ r R n n' s shift a : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hrR : r ≤ R)
    (hs : s ∈ Icc a (a + R))
    (hbin : (⌊n / (ρ * r)⌋ : ℤ) = ⌊n' / (ρ * r)⌋)
    (hnear : |s - (n / ρ - shift)| ≤ r) :
    n' ∈ Icc (ρ * (a + shift - 2 * r))
      (ρ * (a + shift - 2 * r) + 5 * ρ * R) := by
  have hh := normal_band_of_scalar_interval hρ (by norm_num : (0 : ℝ) ≤ 2) hrR hs
    (scalar_error_of_same_strip hr hbin hnear)
  norm_num at hh
  exact hh

/-- A finite assigned normal-strip list gives a scalar-bin list with only
an absolute loss, allowing the fixed central-curve translation. -/
theorem scalar_bins_of_normal_strip_list {X : Type*} (E : Set X) (S n : X → ℝ)
    {ρ r : ℝ} (hr : 0 < r) (shift : ℝ)
    (hnear : ∀ x ∈ E, |S x - (n x / ρ - shift)| ≤ r)
    (L : Finset ℤ) (hL : ∀ x ∈ E, ⌊n x / (ρ * r)⌋ ∈ L) :
    ∃ Q : Finset ℤ, (Q.card : ℝ) ≤ 8 * (L.card : ℝ) ∧
      ∀ x ∈ E, ⌊S x / r⌋ ∈ Q := by
  classical
  have hpiece (j : ℤ) : ∃ Q : Finset ℤ, (Q.card : ℝ) ≤ 8 ∧
      ∀ x ∈ E, ⌊n x / (ρ * r)⌋ = j → ⌊S x / r⌋ ∈ Q := by
    let A := {x ∈ E | (⌊n x / (ρ * r)⌋ : ℤ) = j}
    have hdiam (x : X) (hx : x ∈ A) (y : X) (hy : y ∈ A) : |S x - S y| ≤ 3 * r := by
      have htail := scalar_error_of_same_strip hr (hy.2.trans hx.2.symm) (hnear y hy.1)
      exact (abs_sub_le _ (n x / ρ - shift) _).trans
        ((add_le_add (hnear x hx.1) (by simpa only [abs_sub_comm] using htail)).trans_eq (by ring))
    have hbins := Submission.Lib.K4QuadraticSublevel.grid_bins_of_pairwise_dist_le
      (S '' A) (by positivity : 0 ≤ 3 * r) hr 0 (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        simpa only [Real.dist_eq] using hdiam x hx y hy)
    refine ⟨hbins.1.toFinset, ?_, ?_⟩
    · rw [← Set.ncard_eq_toFinset_card _ hbins.1]
      exact hbins.2.trans_eq (by field_simp; norm_num)
    · intro x hx hj
      exact hbins.1.mem_toFinset.mpr ⟨S x, ⟨x, ⟨hx, hj⟩, rfl⟩, by simp only [sub_zero]⟩
  choose Q hcard hmem using hpiece
  refine ⟨L.biUnion Q, ?_, ?_⟩
  · calc
      ((L.biUnion Q).card : ℝ) ≤ ∑ j ∈ L, ((Q j).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ L, (8 : ℝ) := Finset.sum_le_sum (fun j _ => hcard j)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  · intro x hx
    exact Finset.mem_biUnion.mpr ⟨_, hL x hx, hmem _ x hx rfl⟩

end

end Submission.Obl.k4_scalar_graph_residual_discovery
