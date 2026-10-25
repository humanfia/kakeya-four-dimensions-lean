/- Adapted from this LOT tree: o199, session x0695, branch x0695,
   commit 9136fa89, Submission/Obl/k4_finite_path_candidate_conversion/FiniteGainMenu.lean.
   This file retains the source's own provenance comments below. -/
import Mathlib

/-!
The multiplicative actual-gain menu in MixedCover is finite before the sample
index is chosen. Original angular density exceptions can therefore be applied
at every menu scale using a finite common cutoff and positive exponent.
-/

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

theorem geometric_gain_index_bound {gain ρ H : ℝ} (hgain : 0 < gain) (hρ : 0 < ρ)
    (e : ℕ) (hmax : gain * (1 + ρ) ^ e ≤ H) : e < ⌈H / (gain * ρ)⌉₊ + 1 := by
  have hpow : 1 + (e : ℝ) * ρ ≤ (1 + ρ) ^ e := one_add_mul_le_pow (by linarith) e
  have hprod := mul_le_mul_of_nonneg_left hpow hgain.le
  have he : (e : ℝ) ≤ H / (gain * ρ) := (le_div_iff₀ (mul_pos hgain hρ)).mpr (by nlinarith)
  have he' : e ≤ ⌈H / (gain * ρ)⌉₊ := by
    exact_mod_cast he.trans (Nat.le_ceil _)
  omega

noncomputable def geometricGainMenu (gain ρ H : ℝ) : Finset ℝ := by
  classical
  exact (Finset.range (⌈H / (gain * ρ)⌉₊ + 1)).image (fun e => gain * (1 + ρ) ^ e)

theorem mem_geometricGainMenu {gain ρ H h : ℝ} (hgain : 0 < gain) (hρ : 0 < ρ)
    (hmenu : ∃ e : ℕ, h = gain * (1 + ρ) ^ e) (hmax : h ≤ H) :
    h ∈ geometricGainMenu gain ρ H := by
  classical
  obtain ⟨e, rfl⟩ := hmenu
  exact Finset.mem_image.mpr ⟨e,
    Finset.mem_range.mpr (geometric_gain_index_bound hgain hρ e hmax), rfl⟩

end Submission.Obl.k4_finite_positive_mixed_cover_realization
