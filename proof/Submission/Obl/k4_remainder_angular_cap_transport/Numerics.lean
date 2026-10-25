import Submission.Obl.k4_remainder_angular_cap_transport.NormAngular

namespace Submission.Obl.k4_remainder_angular_cap_transport
open MeasureTheory
open scoped ENNReal

/-- The velocity-cell covering multiplicity is quadratic in the chart slack. -/
theorem cover_multiplicity_le {κ : ℝ} (hκ : 1 ≤ κ) :
    (((2 * ⌈κ⌉ + 1).toNat : ENNReal) ^ 2) ≤ ENNReal.ofReal (25 * κ ^ 2) := by
  have hc : 0 ≤ ⌈κ⌉ := Int.ceil_nonneg (by linarith)
  have hn : 0 ≤ 2 * ⌈κ⌉ + 1 := by omega
  have heq : (((2 * ⌈κ⌉ + 1).toNat : ℕ) : ℝ) = 2 * (⌈κ⌉ : ℝ) + 1 := by
    have hi := Int.toNat_of_nonneg hn
    exact_mod_cast hi
  have hceil := Int.ceil_lt_add_one κ
  have hlin : (((2 * ⌈κ⌉ + 1).toNat : ℕ) : ℝ) ≤ 5 * κ := by rw [heq]; linarith
  have hsq : ((((2 * ⌈κ⌉ + 1).toNat : ℕ) : ℝ) ^ 2) ≤ 25 * κ ^ 2 := by
    nlinarith [sq_nonneg (5 * κ - (((2 * ⌈κ⌉ + 1).toNat : ℕ) : ℝ))]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal hsq

namespace Geometry.Frame
variable (F : Geometry.Frame)

/-- The inverse observation Jacobian is the chart's time length times its spatial Jacobian. -/
theorem obs_jacobian (hq : 0 < F.q) : |F.obsMatrix.det|⁻¹ = F.q * |F.D.det| := by
  simp [F.det_obsMatrix, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', abs_mul,
    abs_of_pos hq, mul_comm]

/-- Time normalization cancels from the conditioned observation density multiplier. -/
theorem conditioning_jacobian (hq : 0 < F.q) (ν : Measure Geometry.Trajectory)
    [IsFiniteMeasure ν] (A : Set Geometry.Trajectory) (hA : 0 < (ν A).toReal) :
    (ν A * ENNReal.ofReal F.q)⁻¹ * ENNReal.ofReal |F.obsMatrix.det|⁻¹ =
      ENNReal.ofReal (|F.D.det| / (ν A).toReal) := by
  rw [F.obs_jacobian hq]
  calc
    _ = ENNReal.ofReal (((ν A).toReal * F.q)⁻¹ * (F.q * |F.D.det|)) := by
      symm
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (mul_pos hA hq),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = _ := by congr 1; field_simp

end Geometry.Frame

namespace Geometry.ChartSystem
variable {W T : ℕ} (s : Geometry.ChartSystem W T)

/-- The exact normalized weight cancels the prior and time conditioning factors. -/
theorem weight_conditioning (ω : Fin W → ℝ) (ν : Fin W → Measure Geometry.Trajectory)
    [∀ γ, IsFiniteMeasure (ν γ)] (hω : ∀ γ, 0 ≤ ω γ) (hZ : 0 < s.normZ ω ν)
    (c : Fin s.count) (hA : 0 < (ν (s.world c) (s.assignment c)).toReal) :
    ENNReal.ofReal (s.normWeight ω ν c) *
      (ν (s.world c) (s.assignment c) * ENNReal.ofReal (s.frameOf c).q)⁻¹ =
      ENNReal.ofReal (s.normZ ω ν)⁻¹ * ENNReal.ofReal (ω (s.world c)) := by
  let a := (ν (s.world c) (s.assignment c)).toReal
  have hq : 0 < (s.frameOf c).q := s.frameOf_q_pos c
  have hw : s.normWeight ω ν c = ω (s.world c) * (a * (s.frameOf c).q) / s.normZ ω ν := by
    unfold normWeight
    change _ = ω (s.world c) * (a * (1 / (2 : ℝ) ^ T)) / s.normZ ω ν
    dsimp [a]
    ring
  rw [hw]
  calc
    _ = ENNReal.ofReal ((ω (s.world c) * (a * (s.frameOf c).q) / s.normZ ω ν) *
        (a * (s.frameOf c).q)⁻¹) := by
      symm
      rw [ENNReal.ofReal_mul (div_nonneg (mul_nonneg (hω _) (mul_nonneg hA.le hq.le)) hZ.le),
        ENNReal.ofReal_inv_of_pos (mul_pos hA hq),
        ENNReal.ofReal_mul (show 0 ≤ a from ENNReal.toReal_nonneg),
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ = ENNReal.ofReal ((s.normZ ω ν)⁻¹ * ω (s.world c)) := by
      congr 1
      field_simp [show a ≠ 0 from hA.ne', hq.ne', hZ.ne']
    _ = _ := ENNReal.ofReal_mul (by positivity)

end Geometry.ChartSystem
end Submission.Obl.k4_remainder_angular_cap_transport

namespace Submission.Obl.k4_remainder_angular_cap_transport

/-- The terminal comparison and subpower slack put the transported ceiling below the desired one. -/
theorem threshold_le {N κ a J f₀ f₁ v τ : ℝ} (hN : 1 ≤ N) (ha : 0 < a)
    (hcomp : N ^ (-f₀) * J ≤ N ^ (τ / 4) * a * N ^ (-f₁))
    (hfactor : 100 * κ ^ 2 * N ^ (τ / 2) ≤ N ^ τ) :
    100 * κ ^ 2 * N ^ (-f₀ - v + τ / 4) * (J / a) ≤ N ^ (-f₁ - v + τ) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hc : N ^ (-f₀) * (J / a) ≤ N ^ (τ / 4) * N ^ (-f₁) := by
    rw [← mul_div_assoc, div_le_iff₀ ha]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcomp
  have he : N ^ (-f₀ - v + τ / 4) = N ^ (-f₀) * N ^ (-v + τ / 4) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  calc
    _ = 100 * κ ^ 2 * N ^ (-v + τ / 4) * (N ^ (-f₀) * (J / a)) := by rw [he]; ring
    _ ≤ 100 * κ ^ 2 * N ^ (-v + τ / 4) * (N ^ (τ / 4) * N ^ (-f₁)) := by
      gcongr
    _ = (100 * κ ^ 2 * N ^ (τ / 2)) * N ^ (-f₁ - v) := by
      rw [show 100 * κ ^ 2 * N ^ (-v + τ / 4) * (N ^ (τ / 4) * N ^ (-f₁)) =
        (100 * κ ^ 2) * (N ^ (-v + τ / 4) * N ^ (τ / 4) * N ^ (-f₁)) by ring,
        ← Real.rpow_add hN0, ← Real.rpow_add hN0,
        show -v + τ / 4 + τ / 4 + -f₁ = τ / 2 + (-f₁ - v) by ring,
        Real.rpow_add hN0]
      ring
    _ ≤ N ^ τ * N ^ (-f₁ - v) := by gcongr
    _ = _ := by rw [← Real.rpow_add hN0]; congr 1; ring

end Submission.Obl.k4_remainder_angular_cap_transport
