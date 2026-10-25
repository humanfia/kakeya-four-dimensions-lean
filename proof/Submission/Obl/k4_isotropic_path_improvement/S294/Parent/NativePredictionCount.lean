-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.NativePredictionCount, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/NativePredictionCount.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FiniteStripUniform

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FrontAlternative

open Filter

/-- Reciprocal native-power fractions have a permitted prediction count.
The exponent is fixed before the actual native bound K is supplied. -/
theorem eventually_native_prediction_count (N : ℕ → ℝ)
    (hN : Tendsto N atTop atTop) {η : ℝ} (hη : 0 < η) (power : ℕ) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 ∧ ∀ᶠ k in atTop,
      ∀ K : ℝ, 1 ≤ K → K ≤ N k^σ → (⌈K^power⌉₊ : ℝ) ≤ N k^η := by
  let σ := min 1 (η/(2*((power:ℝ)+1)))
  have hσ : 0 < σ := lt_min zero_lt_one (by positivity)
  have hσp : σ*(power:ℝ) ≤ η/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*((power:ℝ)+1))).mp
      (min_le_right 1 (η/(2*((power:ℝ)+1))))
    change σ*(2*((power:ℝ)+1)) ≤ η at hh
    nlinarith only [hh,hσ]
  have hcost := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hN (show η/2 < η by linarith) 2
  have hone := hN.eventually (eventually_ge_atTop (1:ℝ))
  refine ⟨σ,hσ,min_le_left _ _,?_⟩
  filter_upwards [hcost,hone] with k hcostk honeK
  intro K hK hKN
  have hKp : 0 ≤ K^power := pow_nonneg (zero_le_one.trans hK) _
  have hpower : K^power ≤ N k^(η/2) := by
    calc
      _ ≤ (N k^σ)^power := pow_le_pow_left₀ (zero_le_one.trans hK) hKN _
      _ = N k^(σ*(power:ℝ)) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans honeK)]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le honeK hσp
  have honePow : 1 ≤ N k^(η/2) := Real.one_le_rpow honeK (by positivity)
  have hceil := (Nat.ceil_lt_add_one hKp).le
  calc
    (⌈K^power⌉₊ : ℝ) ≤ K^power+1 := hceil
    _ ≤ 2*N k^(η/2) := by linarith
    _ ≤ N k^η := hcostk.le

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FrontAlternative
