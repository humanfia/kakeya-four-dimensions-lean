import Submission.Obl.k4_scalar_normalized_exact_refinement.Mass
import Submission.Obl.k4_scalar_normalized_exact_refinement.SparseMass

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open scoped ENNReal

/-- The retained original budget is the old budget multiplied by the retained
fraction of normalized weights. -/
lemma subset_assignment_normalizer {ι κ : Type*} [Fintype κ]
    (a : ι → ℝ) (e : κ → ι) (Z : ℝ) (hZ : Z ≠ 0) :
    (∑ i, a (e i)) = Z * (∑ i, a (e i) / Z) := by
  rw [← Finset.sum_div]
  field_simp

/-- Renormalizing retained weights gives the same literal formula as
normalizing their original assignment budgets directly. -/
lemma renormalized_subset_weight {ι κ : Type*} [Fintype κ]
    (a : ι → ℝ) (e : κ → ι) (Z : ℝ) (hZ : Z ≠ 0)
    (hret : (∑ i, a (e i)) ≠ 0) (i : κ) :
    (∑ j, a (e j) / Z)⁻¹ * (a (e i) / Z) = a (e i) / ∑ j, a (e j) := by
  rw [← Finset.sum_div]
  field_simp

lemma retained_assignment_normalizer_lower {ι κ : Type*} [Fintype κ]
    (a : ι → ℝ) (e : κ → ι) (Z z₀ K : ℝ) (hZ : Z ≠ 0)
    (hz₀ : 0 ≤ z₀) (hZlower : z₀ ≤ Z) (hK : 0 < K)
    (hret : K⁻¹ ≤ ∑ i, a (e i) / Z) :
    z₀ / K ≤ ∑ i, a (e i) := by
  rw [subset_assignment_normalizer a e Z hZ, div_eq_mul_inv]
  exact mul_le_mul hZlower hret (inv_pos.mpr hK).le (hz₀.trans hZlower)

/-- Success of the exactly normalized selected mixture forces success in
the original chart-wise selected masses, with the original normalizer. -/
lemma normalized_success_original_mass {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (m : ι → ENNReal) (Z K : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 < a i) (hZ : 0 < Z) (_hK : 0 < K)
    (hsuccess : ENNReal.ofReal K⁻¹ ≤
      ∑ i, ENNReal.ofReal (w i * a i / Z) * ((ENNReal.ofReal (a i))⁻¹ * m i)) :
    ENNReal.ofReal (Z / K) ≤ ∑ i, ENNReal.ofReal (w i) * m i := by
  rw [normalized_selected_mixture w a m Z hw ha hZ] at hsuccess
  calc
    ENNReal.ofReal (Z / K) = ENNReal.ofReal Z * ENNReal.ofReal K⁻¹ := by
      rw [div_eq_mul_inv, ENNReal.ofReal_mul hZ.le]
    _ ≤ ENNReal.ofReal Z * ((ENNReal.ofReal Z)⁻¹ * ∑ i, ENNReal.ofReal (w i) * m i) :=
      mul_le_mul' le_rfl hsuccess
    _ = _ := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hZ)
        ENNReal.ofReal_ne_top, one_mul]

lemma normalized_sparse_union_lower_bound {X ι Γ : Type*}
    [MeasurableSpace X] [Fintype ι] [Fintype Γ]
    (μ : Γ → Measure X) (w : Γ → ℝ) (γ : ι → Γ) (C : ι → Set X)
    (hC : ∀ i, MeasurableSet (C i)) (Λ : Γ → X → Finset ι)
    (a : ι → ℝ) (Z K H : ℝ)
    (hw : ∀ g, 0 ≤ w g) (ha : ∀ i, 0 < a i) (hZ : 0 < Z) (hK : 0 < K) (hH : 0 < H)
    (hcard : ∀ g x, ((Λ g x).card : ℝ) ≤ H)
    (hrec : ∀ i, μ (γ i) {x | x ∈ C i ∧ i ∉ Λ (γ i) x} = 0)
    (hsuccess : ENNReal.ofReal K⁻¹ ≤ ∑ i,
      ENNReal.ofReal (w (γ i) * a i / Z) * ((ENNReal.ofReal (a i))⁻¹ * μ (γ i) (C i))) :
    ENNReal.ofReal (Z / K / H) ≤ ∑ g, ENNReal.ofReal (w g) *
      μ g {x | ∃ i, γ i = g ∧ x ∈ C i} := by
  have hlower := normalized_success_original_mass (fun i => w (γ i)) a
    (fun i => μ (γ i) (C i)) Z K (fun i => hw _) ha hZ hK hsuccess
  have hupper := weighted_sparse_list_union_mass μ (fun g => ENNReal.ofReal (w g)) γ C hC Λ
    (ENNReal.ofReal H) (fun g x => by simpa using ENNReal.ofReal_le_ofReal (hcard g x)) hrec
  rw [ENNReal.ofReal_div_of_pos hH]
  apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hH) ENNReal.ofReal_ne_top).mpr
  simpa only [mul_comm] using hlower.trans hupper

end Submission.Obl.k4_scalar_normalized_exact_refinement
