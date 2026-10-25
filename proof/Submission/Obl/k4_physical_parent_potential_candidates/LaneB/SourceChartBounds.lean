import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourceCoefficients

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set Metric MvPolynomial

noncomputable section

namespace SourceNormalization

/-- The unsheared source origin is controlled by the original chart's
coordinate bound, uniformly over the old block index. -/
theorem parent_origin_bound {Nk : ℝ} (hNk : 2 ≤ Nk) (Mp T j : ℕ) (hj : j < 2^T)
    (c u : P2) (hcu : ‖c‖+‖u‖ ≤ Nk^Mp) :
    ∀ i, |Broad.parentBaseOrigin T j c u i| ≤ Nk^Mp := by
  have hNk1 : 1 ≤ Nk := by linarith
  have hN : 1 ≤ Nk^Mp := one_le_pow₀ hNk1
  have hpow : 0 < (2:ℝ)^T := by positivity
  have hjR : (j:ℝ) < (2:ℝ)^T := by exact_mod_cast hj
  have ht0 : 0 ≤ (j:ℝ)*((2:ℝ)^T)⁻¹ := by positivity
  have ht1 : (j:ℝ)*((2:ℝ)^T)⁻¹ ≤ 1 := by
    rw [←div_eq_mul_inv]
    exact (div_le_one hpow).mpr hjR.le
  have hbase (i:Fin 2) : |c i+((j:ℝ)*((2:ℝ)^T)⁻¹)*u i| ≤ Nk^Mp := by
    have hc : |c i| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le c i
    have hu : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
    calc
      _ ≤ |c i|+|((j:ℝ)*((2:ℝ)^T)⁻¹)*u i| := abs_add_le _ _
      _ = |c i|+((j:ℝ)*((2:ℝ)^T)⁻¹)*|u i| := by rw [abs_mul,abs_of_nonneg ht0]
      _ ≤ ‖c‖+1*‖u‖ := add_le_add hc (mul_le_mul ht1 hu (abs_nonneg _) (by positivity))
      _ ≤ _ := by simpa only [one_mul] using hcu
  intro i
  fin_cases i
  · change |(j:ℝ)*((2:ℝ)^T)⁻¹| ≤ Nk^Mp
    rw [abs_of_nonneg ht0]
    exact ht1.trans hN
  · exact hbase 0
  · exact hbase 1

/-- An actual old chart bounds the normalized hidden coordinate at every
source incidence by the same original parameter powers. -/
theorem hidden_graphPoint_bound {Nk B : ℝ} (hNk : 2 ≤ Nk) (Mp Mr : ℕ)
    (hB : |B| ≤ Nk^Mr) (l : Ln) (hl : ∀ i, |l.2 i| ≤ Nk^Mp)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    |B*Analytic.graphPoint l t 3| ≤ 2*Nk^(Mp+Mr) := by
  have hcoord : |Analytic.graphPoint l t 3| ≤ 2*Nk^Mp := by
    change |l.2 2+t*l.2 5| ≤ _
    calc
      _ ≤ |l.2 2|+|t*l.2 5| := abs_add_le _ _
      _ ≤ Nk^Mp+1*Nk^Mp := by
        rw [abs_mul,abs_of_nonneg ht.1]
        exact add_le_add (hl 2) (mul_le_mul ht.2 (hl 5) (abs_nonneg _) (by positivity))
      _ = _ := by ring
  rw [abs_mul]
  calc
    _ ≤ Nk^Mr*(2*Nk^Mp) := mul_le_mul hB hcoord (abs_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- Near a normalized source incidence, the actual branch has the
polynomial height bound used by its coefficient format. -/
theorem branch_height_bound {Nk B band : ℝ} (hNk : 2 ≤ Nk) (Mp Mr : ℕ)
    (hB : |B| ≤ Nk^Mr) (l : Ln) (hl : ∀ i, |l.2 i| ≤ Nk^Mp)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (z:P3) (f:P3 → ℝ)
    (hband : |B*Analytic.graphPoint l t 3-f z| ≤ band) (hband1 : band ≤ 1) :
    |f z| ≤ 4*Nk^(Mp+Mr+1) := by
  have hhidden := hidden_graphPoint_bound hNk Mp Mr hB l hl t ht
  have hN1 : 1 ≤ Nk := by linarith
  have hbig : 1 ≤ Nk^(Mp+Mr+1) := one_le_pow₀ hN1
  have hmono : Nk^(Mp+Mr) ≤ Nk^(Mp+Mr+1) := pow_le_pow_right₀ hN1 (by omega)
  have htri : |f z| ≤ |B*Analytic.graphPoint l t 3|+|B*Analytic.graphPoint l t 3-f z| := by
    have hh := abs_add_le (B*Analytic.graphPoint l t 3) (f z-B*Analytic.graphPoint l t 3)
    rw [add_sub_cancel,abs_sub_comm (f z)] at hh
    exact hh
  linarith only [hhidden,hband,hband1,hbig,hmono,htri]

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
