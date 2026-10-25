import Submission.Obl.k4_homogeneous_native_pair_preparation.Front
import Submission.Obl.k4_homogeneous_native_pair_preparation.Numerics

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory

namespace ClassSample

variable {N : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {B : Fin W → ℝ} {f : ℝ → ℝ} {L h : ℝ} {M D : ℕ} {τ e : ℝ}
  (cs : ClassSample N W ω ν E B f L h M D τ e)

theorem ncls_one : 1 ≤ cs.ncls := by
  have hcov := cs.hcov
  have hκ : 0 < cs.κ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le cs.κ_one)
  by_contra hn
  have hn0 : cs.ncls = 0 := by omega
  simp only [hn0, Nat.cast_zero, zero_mul] at hcov
  exact (ENNReal.ofReal_pos.mpr hκ).not_ge hcov

theorem nonempty_labels : Nonempty (Fin cs.C) := by
  have hcov := cs.hcov
  have hκ : 0 < cs.κ⁻¹ := inv_pos.mpr (zero_lt_one.trans_le cs.κ_one)
  by_contra hn
  letI : IsEmpty (Fin cs.C) := ⟨fun b => hn ⟨b⟩⟩
  simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero] at hcov
  exact (ENNReal.ofReal_pos.mpr hκ).not_ge hcov

/-- The class-count loss is the only change in the original weighted mass. -/
theorem retained_mass_le : ENNReal.ofReal (retainedMass cs.κ cs.ncls) ≤
    ∑ b, ENNReal.ofReal (ω (cs.γ b)) * ((ν (cs.γ b)).prod volume) (cs.F b) := by
  have hnpos : 0 < (cs.ncls : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le cs.ncls_one)
  have hn0 : (cs.ncls : ENNReal) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt (Nat.zero_lt_one.trans_le cs.ncls_one))
  have heq : retainedMass cs.κ cs.ncls = cs.κ⁻¹ / cs.ncls := by
    dsimp [retainedMass]
    field_simp
  rw [heq, ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast]
  apply (ENNReal.div_le_iff hn0 (ENNReal.natCast_ne_top _)).mpr
  simpa only [mul_comm] using cs.hcov

/-- Both selected homogeneous scales have fixed polynomial bounds inherited
from a single old chart and its inverse. -/
theorem homogeneous_scale_bounds (hN : 2 ≤ N) :
    cs.R₁ ≤ N ^ (3 * M + 2) ∧ cs.R₂⁻¹ ≤ N ^ (3 * M + 2) := by
  have hN1 : 1 ≤ N := one_le_two.trans hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  obtain ⟨b⟩ := cs.nonempty_labels
  have hsc := Construction.scales_range (chart_det (cs.hchart b))
    (one_le_pow₀ hN1) (chart_frame (cs.hchart b))
  have hR₁ : cs.R₁ ≤ N ^ M := (cs.r₁lo b).trans hsc.2.2
  have hlow : (4 * (N ^ M) ^ 3)⁻¹ ≤ cs.R₂ := by
    have heq : (4 * (N ^ M) ^ 3)⁻¹ = (1 / (2 * (N ^ M) ^ 3)) / 2 := by
      field_simp
      norm_num
    rw [heq]
    linarith only [hsc.1, cs.r₂hi b]
  have hinv : cs.R₂⁻¹ ≤ 4 * (N ^ M) ^ 3 := by
    have hi := inv_anti₀ (by positivity : 0 < (4 * (N ^ M) ^ 3)⁻¹) hlow
    simpa only [inv_inv] using hi
  have hfour : (4 : ℝ) ≤ N ^ (2 : ℕ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 2
    norm_num at hh
    exact hh
  have hpow : 4 * (N ^ M) ^ 3 ≤ N ^ (3 * M + 2) := by
    calc
      4 * (N ^ M) ^ 3 = N ^ (3 * M) * 4 := by rw [← pow_mul, Nat.mul_comm M 3, mul_comm]
      _ ≤ N ^ (3 * M) * N ^ 2 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = N ^ (3 * M + 2) := (pow_add _ _ _).symm
  exact ⟨hR₁.trans (pow_le_pow_right₀ hN1 (by omega)), hinv.trans hpow⟩

end ClassSample
end Submission.Obl.k4_homogeneous_native_pair_preparation
