import Submission.Obl.k4_subcritical_endpoint_native_pairing.Interface
import Submission.Obl.k4_subcritical_endpoint_native_pairing.NativeLevel
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.Domain
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory Filter MvPolynomial
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

/-- The native spatial slopes control its variation across a parameter square;
the velocity representative and the constant coefficient cancel. -/
theorem native_parameter_variation (L : Fin 4 → ℝ)
    {S D v t p q p' q' : ℝ} (hS : 0 ≤ S) (hD : 0 ≤ D)
    (hL2 : |L 2| ≤ S) (hL3 : |L 3| ≤ S) (ht : |t| ≤ 1)
    (hp : |p - p'| ≤ D) (hq : |q - q'| ≤ D) :
    |parameterPredictor (Match3.nativeParam L v) t p q -
      parameterPredictor (Match3.nativeParam L v) t p' q'| ≤ 3 * S * D := by
  rw [Match3.parameterPredictor_nativeParam, Match3.parameterPredictor_nativeParam]
  have heq : L 0 + L 1 * t + L 2 * (p + t * v) + L 3 * (q - t * p) -
      (L 0 + L 1 * t + L 2 * (p' + t * v) + L 3 * (q' - t * p')) =
      L 2 * (p - p') + L 3 * ((q - q') - t * (p - p')) := by ring
  rw [heq]
  calc
    _ ≤ |L 2| * |p - p'| + |L 3| * |(q - q') - t * (p - p')| := by
      simpa only [abs_mul] using abs_add_le (L 2 * (p - p'))
        (L 3 * ((q - q') - t * (p - p')))
    _ ≤ S * D + S * (D + 1 * D) := by
      apply add_le_add (mul_le_mul hL2 hp (abs_nonneg _) hS)
      apply mul_le_mul hL3 ?_ (abs_nonneg _) hS
      exact (abs_sub _ _).trans (add_le_add hq (by rw [abs_mul]; gcongr))
    _ = _ := by ring

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem NativeLevel.nativeParameter_eq {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s)) (v t p q : ℝ) :
    cfg.nativeParameter k s i v t p q =
      parameterPredictor (Match3.nativeParam (a.L i) v) t p q := by
  rw [Match3.parameterPredictor_nativeParam]
  unfold nativeParameter
  rw [a.defining_polynomial i]
  simp only [eval_sub, eval_X, eval_add, eval_C, eval_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- The actual native fit transfers to fixed-velocity parameter coordinates.
Only the original native slopes multiply the two reconstruction errors. -/
theorem NativeLevel.parameter_fit {k : ℕ} {s : ℝ} (a : cfg.NativeLevel k s)
    (i : Fin (cfg.n k s)) {l : α} (hl : l ∈ cfg.B k s i) {v t χ Δ : ℝ}
    (ht : t ∈ I (cfg.T k s) (cfg.j k s i))
    (hvel : |cfg.b k l 3 - v| ≤ χ) (hdef : |cfg.b k l 4 + cfg.b k l 0| ≤ Δ) :
    |(cfg.x k l t) 3 - cfg.nativeParameter k s i v t (cfg.b k l 0) (cfg.b k l 1)| ≤
      cfg.K k * cfg.N k ^ (-s) + 36 * cfg.K k ^ 4 * (χ + Δ) := by
  have hunit := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) ht
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg hunit.1]; exact hunit.2
  have hχ : 0 ≤ χ := (abs_nonneg _).trans hvel
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans hdef
  have hZ : |cfg.b k l 0 + t * cfg.b k l 3 - (cfg.b k l 0 + t * v)| ≤ χ := by
    rw [show cfg.b k l 0 + t * cfg.b k l 3 - (cfg.b k l 0 + t * v) =
      t * (cfg.b k l 3 - v) by ring, abs_mul]
    exact (mul_le_mul ht1 hvel (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hY : |cfg.b k l 1 + t * cfg.b k l 4 - (cfg.b k l 1 - t * cfg.b k l 0)| ≤ Δ := by
    rw [show cfg.b k l 1 + t * cfg.b k l 4 - (cfg.b k l 1 - t * cfg.b k l 0) =
      t * (cfg.b k l 4 + cfg.b k l 0) by ring, abs_mul]
    exact (mul_le_mul ht1 hdef (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [a.nativeParameter_eq]
  have hf := Match3.native_fit_transfer (a.fit i l hl t ht) hZ hY
  apply hf.trans
  have hL2 := a.slope i (1 : Fin 3)
  have hL3 := a.slope i (2 : Fin 3)
  change |a.L i 2| ≤ 36 * cfg.K k ^ 4 at hL2
  change |a.L i 3| ≤ 36 * cfg.K k ^ 4 at hL3
  nlinarith [mul_le_mul_of_nonneg_right hL2 hχ, mul_le_mul_of_nonneg_right hL3 hΔ]

/-- An occupied good original trajectory bounds the native predictor on its
whole true time block and whole parameter square. -/
theorem NativeLevel.parameter_square_norm (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s))
    {χ D v p₀ q₀ : ℝ} (hχ : χ ≤ 1) (hD : 0 ≤ D) (hD1 : D ≤ 1)
    (ha : cfg.N k ^ (-s) ≤ 1)
    (hoccupied : ∃ l ∈ cfg.B k s i,
      (∀ e, |cfg.b k l e| ≤ 2 * cfg.K k) ∧
      |cfg.b k l 3 - v| ≤ χ ∧ |cfg.b k l 4 + cfg.b k l 0| ≤ χ ∧
      cfg.b k l 0 ∈ Icc p₀ (p₀ + D) ∧ cfg.b k l 1 ∈ Icc q₀ (q₀ + D)) :
    ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
      ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
      |cfg.nativeParameter k s i v t p q| ≤ 200 * cfg.K k ^ 4 := by
  obtain ⟨l, hl, hb, hv, hd, hp₀, hq₀⟩ := hoccupied
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK
  have hK4 : cfg.K k ≤ cfg.K k ^ 4 := by
    simpa using pow_le_pow_right₀ hK (show (1 : ℕ) ≤ 4 by norm_num)
  have hS : 0 ≤ 36 * cfg.K k ^ 4 := by positivity
  intro t ht p hp q hq
  have hunit := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
    (cfg.T k s) (cfg.j k s i) ht
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg hunit.1]; exact hunit.2
  have hvalue : |(cfg.x k l t) 3| ≤ 4 * cfg.K k := by
    change |cfg.b k l 2 + t * cfg.b k l 5| ≤ _
    calc
      _ ≤ |cfg.b k l 2| + |t| * |cfg.b k l 5| := by simpa [abs_mul] using abs_add_le (cfg.b k l 2) (t * cfg.b k l 5)
      _ ≤ 2 * cfg.K k + 1 * (2 * cfg.K k) :=
        add_le_add (hb 2) (mul_le_mul ht1 (hb 5) (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  have hfit := a.parameter_fit i hl ht hv hd
  have hvar := native_parameter_variation (a.L i) (v := v) (t := t) (p := p) (q := q)
    (p' := cfg.b k l 0) (q' := cfg.b k l 1) hS hD
    (a.slope i (1 : Fin 3)) (a.slope i (2 : Fin 3)) ht1
    (abs_le.mpr ⟨by linarith [hp.1, hp₀.2], by linarith [hp.2, hp₀.1]⟩)
    (abs_le.mpr ⟨by linarith [hq.1, hq₀.2], by linarith [hq.2, hq₀.1]⟩)
  rw [← a.nativeParameter_eq, ← a.nativeParameter_eq] at hvar
  have htotal : |cfg.nativeParameter k s i v t p q| ≤
      3 * (36 * cfg.K k ^ 4) * D +
        (cfg.K k * cfg.N k ^ (-s) + 36 * cfg.K k ^ 4 * (χ + χ)) +
          4 * cfg.K k := by
    calc
      _ = |(cfg.nativeParameter k s i v t p q -
          cfg.nativeParameter k s i v t (cfg.b k l 0) (cfg.b k l 1)) +
        (cfg.nativeParameter k s i v t (cfg.b k l 0) (cfg.b k l 1) - (cfg.x k l t) 3) +
        (cfg.x k l t) 3| := by congr 1; ring
      _ ≤ |cfg.nativeParameter k s i v t p q -
          cfg.nativeParameter k s i v t (cfg.b k l 0) (cfg.b k l 1)| +
        |cfg.nativeParameter k s i v t (cfg.b k l 0) (cfg.b k l 1) - (cfg.x k l t) 3| +
        |(cfg.x k l t) 3| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by rw [abs_sub_comm _ ((cfg.x k l t) 3)]; exact add_le_add (add_le_add hvar hfit) hvalue
  apply htotal.trans
  nlinarith [mul_le_mul_of_nonneg_left hD1 (show 0 ≤ 3 * (36 * cfg.K k ^ 4) by positivity),
    mul_le_mul_of_nonneg_left ha hK0,
    mul_le_mul_of_nonneg_left (show χ + χ ≤ 2 by linarith) hS]

/-- The chosen velocity width absorbs all native reconstruction errors,
uniformly over the original native entries and the weakened good-line cut. -/
theorem Prepared.eventually_native_parameter_fit_of_binned_defect (h : cfg.Prepared) {M s : ℝ}
    (hsM : s < M) :
    ∀ᶠ k in atTop, ∀ (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s))
      (l : α), l ∈ cfg.B k s i →
      ∀ (v t : ℝ), t ∈ I (cfg.T k s) (cfg.j k s i) →
      |cfg.b k l 3 - v| ≤ cfg.N k ^ (-M) →
      |cfg.b k l 4 + cfg.b k l 0| ≤ cfg.N k ^ (-M) →
      |(cfg.x k l t) 3 - cfg.nativeParameter k s i v t (cfg.b k l 0) (cfg.b k l 1)| ≤
        2 * cfg.K k * cfg.N k ^ (-s) := by
  have hN1 : ∀ k, 1 ≤ cfg.N k := fun k => by linarith [h.scale k]
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 h.scale_limit h.subpower.1 h.subpower.2 3 (neg_lt_neg hsM)
    (show (0 : ℝ) ≤ 72 by norm_num)
  filter_upwards [hsmall] with k hk
  intro a i l hl v t ht hv hd
  have hK : 0 ≤ cfg.K k := zero_le_one.trans (h.subpower.1 k)
  have hfit := a.parameter_fit i hl ht hv hd
  apply hfit.trans
  have herr := mul_le_mul_of_nonneg_left hk.le hK
  nlinarith

/-- The original horizontal defect implies the same fixed-bin fit. -/
theorem Prepared.eventually_native_parameter_fit (h : cfg.Prepared) {M s : ℝ}
    (hsM : s < M) (hMe : M ≤ cfg.e₀) :
    ∀ᶠ k in atTop, ∀ (a : cfg.NativeLevel k s) (i : Fin (cfg.n k s))
      (l : α), l ∈ cfg.B k s i →
      ∀ (v t : ℝ), t ∈ I (cfg.T k s) (cfg.j k s i) →
      |cfg.b k l 3 - v| ≤ cfg.N k ^ (-M) →
      |cfg.b k l 4 + cfg.b k l 0| ≤ cfg.N k ^ (-cfg.e₀) →
      |(cfg.x k l t) 3 - cfg.nativeParameter k s i v t (cfg.b k l 0) (cfg.b k l 1)| ≤
        2 * cfg.K k * cfg.N k ^ (-s) := by
  filter_upwards [h.eventually_native_parameter_fit_of_binned_defect hsM] with k hk
  intro a i l hl v t ht hv hd
  apply hk a i l hl v t ht hv
  exact hd.trans (Real.rpow_le_rpow_of_exponent_le
    (show 1 ≤ cfg.N k by linarith [h.scale k]) (neg_le_neg hMe))

end Data
end
end Submission.Obl.k4_subcritical_endpoint_native_pairing
