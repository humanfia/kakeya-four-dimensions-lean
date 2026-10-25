import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.Asymptotic

namespace Submission.Obl.k4_scalar_angular_pair_agreement

/-- The absolute multiplier in the normalized three-line estimate after coarsening. -/
def geometryConstant : ℝ := 2048000 * 96 * (4 : ℝ) ^ 9 * 4

/-- A fixed amount of exponent slack absorbs every local geometric constant. -/
theorem geometry_power_bound {N R L θ e u a : ℝ}
    (hN : 1 ≤ N) (he : 0 ≤ e) (hR0 : 0 ≤ R) (hR : R ≤ 2 * N ^ e)
    (hθ : θ ≤ e / 40) (hallow : 3 * e + 9 * u ≤ a * e)
    (hconst : geometryConstant ≤ N ^ (e / 2)) :
    2048000 * (96 * R ^ 2 * (N ^ θ * N ^ (-L))) *
      (4 * (N ^ θ) ^ 2) ^ 9 / (N ^ (-u)) ^ 9 ≤ N ^ (-L + a * e) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hN0 : 0 ≤ N := hNp.le
  calc
    _ ≤ 2048000 * (96 * (2 * N ^ e) ^ 2 * (N ^ θ * N ^ (-L))) *
        (4 * (N ^ θ) ^ 2) ^ 9 / (N ^ (-u)) ^ 9 := by gcongr
    _ = geometryConstant * N ^ (-L + (e * 2 + θ + θ * 18 + u * 9)) := by
      rw [Real.rpow_neg hN0 u, inv_pow, div_inv_eq_mul]
      simp only [mul_pow, ← pow_mul]
      rw [← Real.rpow_mul_natCast hN0 e 2, ← Real.rpow_mul_natCast hN0 θ 18,
        ← Real.rpow_mul_natCast hN0 u 9]
      simp only [Real.rpow_add hNp]
      dsimp [geometryConstant]
      norm_num
      ring
    _ ≤ N ^ (e / 2) * N ^ (-L + (e * 2 + θ + θ * 18 + u * 9)) := by
      gcongr
    _ = N ^ (-L + (e / 2 + e * 2 + θ + θ * 18 + u * 9)) := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    _ ≤ N ^ (-L + a * e) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The eventual constant bound needed above follows from divergence of the base. -/
theorem eventually_geometry_constant_le {N : ℕ → ℝ}
    (hN : Filter.Tendsto N Filter.atTop Filter.atTop) {e : ℝ} (he : 0 < e) :
    ∀ᶠ k in Filter.atTop, geometryConstant ≤ N k ^ (e / 2) :=
  Submission.Obl.k4_scalar_terminal_chart_packet_extraction.eventually_const_le_rpow
    hN geometryConstant (by positivity)

/-- The width and terminal density cancel against the source true floor. -/
theorem source_cap_cancel_factors {F G A R J q₀ q₁ : ℝ}
    (hF : 0 ≤ F) (hG : 0 ≤ G) (hA : 1 ≤ A) (hR : 1 ≤ R)
    (hJ : 0 ≤ J) (hq₀ : 0 ≤ q₀) (hq₁ : 0 < q₁) :
    (q₀ / q₁) * ((F * G) * (96 * R ^ 2 * A + 3) * (A * 6) *
      (q₁ * (2 * ((1 + 2 * R) * (A * J))))) ≤
        (3564 * R ^ 3 * A ^ 4 * G) * (F * J * q₀ / A) := by
  have hA0 : 0 ≤ A := by linarith
  have hAp : 0 < A := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hRA : 1 ≤ R ^ 2 * A := by
    nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hA)]
  calc
    _ ≤ (q₀ / q₁) * ((F * G) * (99 * R ^ 2 * A) * (A * 6) *
        (q₁ * (2 * ((3 * R) * (A * J))))) := by
      gcongr <;> nlinarith
    _ = (3564 * R ^ 3 * A ^ 4 * G) * (F * J * q₀ / A) := by
      field_simp
      ring

/-- The source true floor cancels both `J` and `f(L)` from the normalized cap estimate. -/
theorem source_cap_cancel_floor {N R J q₀ q₁ f S u τ θ : ℝ}
    (hN : 1 ≤ N) (hθ : 0 ≤ θ) (hR : 1 ≤ R)
    (hJ : 0 ≤ J) (hq₀ : 0 ≤ q₀) (hq₁ : 0 < q₁) :
    (q₀ / q₁) * (N ^ (-f - S * u + τ) * (96 * R ^ 2 * N ^ θ + 3) *
      (N ^ θ * 6) * (q₁ * (2 * ((1 + 2 * R) * (N ^ θ * J))))) ≤
        (3564 * R ^ 3 * N ^ (4 * θ + τ - S * u)) * (N ^ (-f) * J * q₀ / N ^ θ) := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcap : N ^ (-f - S * u + τ) = N ^ (-f) * N ^ (τ - S * u) := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hpowers : (N ^ θ) ^ 4 * N ^ (τ - S * u) = N ^ (4 * θ + τ - S * u) := by
    rw [← Real.rpow_mul_natCast hNp.le θ 4, ← Real.rpow_add hNp]
    congr 1
    ring
  have hh := source_cap_cancel_factors (Real.rpow_nonneg hNp.le (-f))
    (Real.rpow_nonneg hNp.le (τ - S * u)) (Real.one_le_rpow hN hθ) hR hJ hq₀ hq₁
  rw [← hcap] at hh
  convert hh using 1
  rw [← hpowers]
  ring

/-- The angular gain dominates the remaining coarsening and chart-slack factors. -/
theorem bad_cap_coefficient_le {N R θ e S u τ : ℝ}
    (hN : 1 ≤ N) (he : 0 ≤ e) (hR0 : 0 ≤ R) (hR : R ≤ 2 * N ^ e)
    (hθ : θ ≤ e / 40) (hτ : τ ≤ e / 8) (hgain : 6 * e ≤ S * u)
    (hconst : geometryConstant ≤ N ^ (e / 2)) :
    3564 * R ^ 3 * N ^ (4 * θ + τ - S * u) ≤ N ^ (-2 * θ) / 4 := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hC : (114048 : ℝ) ≤ N ^ (e / 2) :=
    (by norm_num [geometryConstant] : (114048 : ℝ) ≤ geometryConstant).trans hconst
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  calc
    _ ≤ 4 * (3564 * (2 * N ^ e) ^ 3 * N ^ (4 * θ + τ - S * u)) := by
      conv_lhs => rw [mul_comm _ 4]
      gcongr
    _ = 114048 * N ^ (3 * e + (4 * θ + τ - S * u)) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hNp.le e 3]
      simp only [Real.rpow_add hNp]
      norm_num only [Nat.cast_ofNat]
      have hh : N ^ (e * 3) = N ^ (3 * e) := by congr 1; ring
      rw [hh]
      ring
    _ ≤ N ^ (e / 2) * N ^ (3 * e + (4 * θ + τ - S * u)) := by gcongr
    _ = N ^ (e / 2 + (3 * e + (4 * θ + τ - S * u))) := (Real.rpow_add hNp _ _).symm
    _ ≤ N ^ (-2 * θ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- The cancellation bound charged directly to the original selected mass. -/
theorem source_cap_cancel_floor_ennreal {N R J q₀ q₁ f S u τ θ : ℝ} {m : ENNReal}
    (hN : 1 ≤ N) (hθ : 0 ≤ θ) (hR : 1 ≤ R)
    (hJ : 0 ≤ J) (hq₀ : 0 ≤ q₀) (hq₁ : 0 < q₁)
    (hfloor : ENNReal.ofReal (N ^ (-f) * J * q₀ / N ^ θ) ≤ m) :
    ENNReal.ofReal ((q₀ / q₁) * (N ^ (-f - S * u + τ) *
      (96 * R ^ 2 * N ^ θ + 3) * (N ^ θ * 6) *
      (q₁ * (2 * ((1 + 2 * R) * (N ^ θ * J)))))) ≤
        ENNReal.ofReal (3564 * R ^ 3 * N ^ (4 * θ + τ - S * u)) * m := by
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ ENNReal.ofReal ((3564 * R ^ 3 * N ^ (4 * θ + τ - S * u)) *
        (N ^ (-f) * J * q₀ / N ^ θ)) :=
      ENNReal.ofReal_le_ofReal (source_cap_cancel_floor hN hθ hR hJ hq₀ hq₁)
    _ = ENNReal.ofReal (3564 * R ^ 3 * N ^ (4 * θ + τ - S * u)) *
        ENNReal.ofReal (N ^ (-f) * J * q₀ / N ^ θ) := ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := by gcongr

end Submission.Obl.k4_scalar_angular_pair_agreement
