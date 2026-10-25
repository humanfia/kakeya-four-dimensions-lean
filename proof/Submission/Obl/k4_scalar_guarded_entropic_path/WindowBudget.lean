import Submission.Obl.k4_scalar_guarded_entropic_path.Info.WindowChoice

/-! Fixing a sufficiently long finite window chain absorbs the master
velocity exponent. The constant ambiguity costs vanish on the inner tail. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Filter
open scoped Topology

noncomputable section

theorem window_informationExponent_le {N A δ : ℝ} {L C M Kv Ks : ℕ}
    (hN : 1 < N) (hL : 0 < L)
    (hmaster : Real.log (M : ℝ) ≤ A * Real.log N)
    (hfraction : 2 * (C : ℝ) * A / (L : ℝ) ≤ δ / 2)
    (hconstant : 2 * (Real.log (Kv : ℝ) + Real.log (Ks : ℝ) + 4) + 1 ≤
      (δ / 2) * Real.log N) :
    informationExponent N (windowCost L C M Kv Ks) ≤ δ := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hm := mul_le_mul_of_nonneg_left hmaster
    (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg C)) hLR.le)
  have hterm : 2 * (C : ℝ) * Real.log (M : ℝ) / (L : ℝ) ≤ (δ / 2) * Real.log N := by
    calc
      _ ≤ (2 * (C : ℝ) * A / (L : ℝ)) * Real.log N := by convert hm using 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfraction hlog.le
  unfold informationExponent windowCost
  apply (div_le_iff₀ hlog).mpr
  have hterm' : 2 * ((C : ℝ) * Real.log (M : ℝ) / (L : ℝ)) ≤ (δ / 2) * Real.log N := by
    convert hterm using 1 <;> ring
  nlinarith only [hterm', hconstant]

theorem eventually_window_informationExponent_le (N : ℕ → ℝ) (M : ℕ → ℕ)
    (hNt : Tendsto N atTop atTop) {A δ : ℝ} {L C Kv Ks : ℕ}
    (hδ : 0 < δ) (hL : 0 < L)
    (hmaster : ∀ᶠ k in atTop, Real.log (M k : ℝ) ≤ A * Real.log (N k))
    (hfraction : 2 * (C : ℝ) * A / (L : ℝ) ≤ δ / 2) :
    ∀ᶠ k in atTop, informationExponent (N k) (windowCost L C (M k) Kv Ks) ≤ δ := by
  let T := 2 * (Real.log (Kv : ℝ) + Real.log (Ks : ℝ) + 4) + 1
  filter_upwards [hNt.eventually_ge_atTop 2, hmaster,
    (Real.tendsto_log_atTop.comp hNt).eventually_ge_atTop (T / (δ / 2))]
    with k hN hm hT
  apply window_informationExponent_le (by linarith) hL hm hfraction
  have ht := (div_le_iff₀ (half_pos hδ)).mp hT
  simpa only [T, Function.comp_apply, mul_comm] using ht

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
