import Submission.Obl.k4_general_wide_layer_offset_comparison.LayerWidth
import Submission.Obl.k4_general_wide_layer_offset_comparison.NativeCommonNumerics
import Submission.Obl.k4_critical_intercept_concentration.CriticalScales

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set Filter

noncomputable section

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- A common fixed slope mesh can be imposed on every layer above `r`.
Only its width changes, with the explicit squared intrinsic loss. -/
theorem cap_at_depth_valid (hp : p.Valid) {k : ℕ} {r s m H : ℝ}
    {L : ProjectedLayer α} (hL : L.Valid p k s m H) (hH : 1 ≤ H) (hrs : r ≤ s) :
    (L.withWidth (min L.β (p.N k ^ (-p.ℓ * r)))).Valid p k s m (H ^ 2) := by
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hpow : p.N k ^ (-p.ℓ * s) ≤ p.N k ^ (-p.ℓ * r) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [hp.scale k])
      (by nlinarith [hp.transverse_pos])
  apply capWidth_valid hL hN hH (by positivity)
    (hL.2.2.1.trans (mul_le_mul_of_nonneg_left hpow (by linarith)))
  exact (div_le_self (Real.rpow_nonneg hN.le _) (one_le_pow₀ hH)).trans hpow

end ProjectedLayer

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The short true width fits all three projected widths eventually. The
original major mesh is finer than that width and the fixed slope mesh. -/
theorem eventually_short_layer_geometry (hp : p.Valid)
    {r u v m : ℝ} (hu : 0 ≤ u) (hvu : v ≤ u)
    (hgap : p.ℓ * u < p.κ * r) (hm : (p.κ + p.ℓ) * r < m)
    (H : ℕ → ℝ) (hH : ∀ k, 1 ≤ H k) (hKH : ∀ k, p.K k ≤ H k)
    (hHs : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N k ^ ε)
    (L : ℕ → Fin 3 → ProjectedLayer α)
    (hL : ∀ k a, (L k a).Valid p k (![r, r + u, r + v] a) m (H k)) :
    ∀ᶠ k in atTop, ∀ R : ℝ, p.AtDepth k r R →
      p.N k ^ (-m) ≤ (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) ∧
      p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r) ∧
      ∀ a, (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) ≤ (L k a).β := by
  have hN1 : ∀ k, 1 ≤ p.N k := fun k => by linarith [hp.scale k]
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hp.scale_limit hH hHs 2
    (show -p.κ * r + p.ℓ * u < 0 by linarith) (by norm_num : (0 : ℝ) ≤ 1)
  have hmesh := eventually_native_common_mesh hN1 hp.scale_limit hH hHs 0 hm
  filter_upwards [hsmall, hmesh] with k hsk hmk
  intro R hat
  have hN : 0 < p.N k := by linarith [hp.scale k]
  have hHp : 0 < H k := zero_lt_one.trans_le (hH k)
  have hKp : 0 < p.K k := zero_lt_one.trans_le (hp.subpower.1 k)
  let q : ℝ := (2 : ℝ) ^ (-(p.T k r : ℤ))
  let g : ℝ := p.N k ^ (-p.ℓ * r)
  have hq : 0 < q := by dsimp [q]; positivity
  have hg : 0 < g := by dsimp [g]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hlength := Submission.Obl.k4_critical_intercept_concentration.time_length_comparison
    hN hKp hat.1 hat.2.1
  have hqlo : p.N k ^ (-p.κ * r) ≤ p.K k * q := by
    simpa only [q, zpow_neg, zpow_natCast] using hlength.2
  have hqhi : q ≤ p.K k * p.N k ^ (-p.κ * r) := by
    have hh := (div_le_iff₀ hKp).mp hlength.1
    simpa only [q, zpow_neg, zpow_natCast, mul_comm] using hh
  have hqloH : p.N k ^ (-p.κ * r) / H k ≤ q := by
    apply (div_le_iff₀ hHp).mpr
    exact hqlo.trans (by nlinarith [hKH k])
  have hχw : p.N k ^ (-m) ≤ q * g := by
    have hh := hmk q hqloH
    exact hh.trans (div_le_self (by positivity) (by norm_num))
  have hχg : p.N k ^ (-m) ≤ g :=
    hχw.trans (mul_le_of_le_one_left hg.le hq1)
  refine ⟨hχw, hχg, ?_⟩
  intro a
  have hs : (![r, r + u, r + v] a) ≤ r + u := by
    fin_cases a
    · change r ≤ r + u
      linarith
    · exact le_rfl
    · change r + v ≤ r + u
      linarith
  have hpow : p.N k ^ (-p.ℓ * (r + u)) ≤ p.N k ^ (-p.ℓ * (![r, r + u, r + v] a)) :=
    Real.rpow_le_rpow_of_exponent_le (hN1 k) (by nlinarith [hp.transverse_pos])
  apply le_trans ?_ (hL k a).2.1
  apply le_trans ?_ (div_le_div_of_nonneg_right hpow hHp.le)
  apply (le_div_iff₀ hHp).mpr
  have hpowers : p.N k ^ (-p.κ * r) * g =
      p.N k ^ (-p.κ * r + p.ℓ * u) * p.N k ^ (-p.ℓ * (r + u)) := by
    dsimp only [g]
    rw [← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  calc
    q * g * H k ≤ (H k * p.N k ^ (-p.κ * r)) * g * H k := by
      gcongr
      exact hqhi.trans (mul_le_mul_of_nonneg_right (hKH k) (by positivity))
    _ = H k ^ 2 * (p.N k ^ (-p.κ * r) * g) := by ring
    _ = (H k ^ 2 * p.N k ^ (-p.κ * r + p.ℓ * u)) *
        p.N k ^ (-p.ℓ * (r + u)) := by rw [hpowers]; ring
    _ ≤ p.N k ^ (-p.ℓ * (r + u)) := by
      have hh : H k ^ 2 * p.N k ^ (-p.κ * r + p.ℓ * u) ≤ 1 := by
        simpa only [one_mul, Real.rpow_zero] using hsk.le
      exact mul_le_of_le_one_left (by positivity) hh

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
