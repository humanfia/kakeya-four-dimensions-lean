import Submission.Obl.k4_physical_row_packet_potential.PowerEnvelopes
import Submission.Obl.k4_physical_row_packet_potential.GlueNumerics

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Glue

open PowerBudget

/-- The precision exponent is fixed before any physical packet is supplied.
It simultaneously pays for Cartesian interpolation, state and velocity meshes,
and the switching error with the original loss constant. -/
theorem exists_numerics_goal (M : ℕ) (d : ℝ) (hd : d < 1)
    (C : ℝ) (hC : 1 ≤ C) (e cNorm cCurl : ℕ) :
    ∃ Ep : ℕ, NumericsGoal M d C e cNorm cCurl Ep := by
  have hc : 0 < c0 := by norm_num [c0]
  have hCb : PowerBudget.Bound (fun _ => C) := PowerBudget.Bound.const C (by linarith)
  have hki : PowerBudget.Bound Kint :=
    (PowerBudget.Bound.const 64 (by norm_num)).mul (PowerBudget.Bound.id.pow 202)
  have hat : PowerBudget.Bound (AT C e) := hCb.mul (hki.pow e)
  have hcomb : PowerBudget.Bound (Ccomb C e) :=
    ((PowerBudget.Bound.id.pow 3).mul (PowerBudget.Bound.const c0⁻¹ (by positivity))).mul hat
  have hkf : PowerBudget.Bound (Kf M C e) :=
    (((PowerBudget.Bound.const 8 (by norm_num)).mul
      (PowerBudget.Bound.const (3 * (M : ℝ) + 1) (by positivity))).mul
        (PowerBudget.Bound.id.pow 4)).mul hat
  have hkr : PowerBudget.Bound (fun K => 2 * K) :=
    (PowerBudget.Bound.const 2 (by norm_num)).mul PowerBudget.Bound.id
  let Itime : ℝ → ℝ := fun K => 12 * K * Ccomb C e K
  have hi : PowerBudget.Bound Itime :=
    ((PowerBudget.Bound.const 12 (by norm_num)).mul PowerBudget.Bound.id).mul hcomb
  have hvals (K : ℝ) (hK : 2 ≤ K) : 1 ≤ Kint K ∧ 1 ≤ AT C e K ∧ 2 ≤ Kf M C e K ∧ 0 < Itime K := by
    have hK0 : 0 < K := by linarith
    have hK1 : 1 ≤ K := by linarith
    have hki1 : 1 ≤ Kint K := by
      unfold Kint
      have hp := one_le_pow₀ hK1 (n := 202)
      linarith
    have hat1 : 1 ≤ AT C e K := by
      unfold AT
      exact one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hki1)
    have hkf2 : 2 ≤ Kf M C e K := by
      have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
      have hp : 1 ≤ K ^ 4 := one_le_pow₀ hK1
      unfold Kf
      have h1 : 1 ≤ (3 * (M : ℝ) + 1) * K ^ 4 * AT C e K :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hp) hat1
      nlinarith
    refine ⟨hki1, hat1, hkf2, ?_⟩
    dsimp only [Itime, Ccomb]
    positivity
  obtain ⟨E, hE⟩ := PowerBudget.exists_packet_resolution_power (3 * M) cNorm cCurl d hd
    (Kf M C e) (fun K => 2 * K) (AT C e) Itime hkf hkr hat hi
    (fun K hK => (hvals K hK).2.2.1) (by intros; linarith)
    (fun K hK => (hvals K hK).2.2.2)
  let amp : ℝ → ℝ := fun K => 1 + 3 * K * AT C e K
  have hamp : PowerBudget.Bound amp := (PowerBudget.Bound.const 1 (by norm_num)).add
    (((PowerBudget.Bound.const 3 (by norm_num)).mul PowerBudget.Bound.id).mul hat)
  obtain ⟨Ea, hEEa, hEa⟩ := PowerBudget.exists_amplified_ratio_power amp hamp E
  have h30 : PowerBudget.Bound (fun K => 30 * Kint K ^ 2) :=
    (PowerBudget.Bound.const 30 (by norm_num)).mul (hki.pow 2)
  have hatK : PowerBudget.Bound (fun K => AT C e K * K) := hat.mul PowerBudget.Bound.id
  have h2 : PowerBudget.Bound (fun K => 2 * K ^ 101) :=
    (PowerBudget.Bound.const 2 (by norm_num)).mul (PowerBudget.Bound.id.pow 101)
  obtain ⟨b, hb⟩ := hkf.max (h30.max (hatK.max h2))
  let Ep := max Ea b
  refine ⟨Ep, ?_⟩
  intro K a h ζ hK ha hh haK hζ hζ1
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hEb : b ≤ Ep := le_max_right _ _
  have hEaEp : Ea ≤ Ep := le_max_left _ _
  have hEEp : E ≤ Ep := hEEa.trans hEaEp
  have hbud : max (Kf M C e K) (max (30 * Kint K ^ 2) (max (AT C e K * K) (2 * K ^ 101))) ≤ K ^ Ep :=
    (hb K hK).2.trans (pow_le_pow_right₀ hK1 hEb)
  have hcoeff : Kf M C e K ≤ K ^ Ep ∧ 30 * Kint K ^ 2 ≤ K ^ Ep ∧
      AT C e K * K ≤ K ^ Ep ∧ 2 * K ^ 101 ≤ K ^ Ep := by
    simpa only [max_le_iff] using hbud
  obtain ⟨hε, hpv, herr⟩ := hE K ζ a h hK hζ hζ1 ha hh haK
  have hratio : ζ ^ Ep / K ^ Ep ≤ ζ ^ E / K ^ E :=
    PowerBudget.ratio_power_mono hK1 hζ.le hζ1 hEEp
  have hratioAmp : amp K * (ζ ^ Ep / K ^ Ep) ≤ ζ ^ E / K ^ E := by
    have hamp0 : 0 ≤ amp K := by
      have hAt1 := (hvals K hK).2.1
      dsimp only [amp]
      positivity
    exact (mul_le_mul_of_nonneg_left
      (PowerBudget.ratio_power_mono hK1 hζ.le hζ1 hEaEp) hamp0).trans (hEa K ζ hK hζ hζ1)
  have hsmall : a / h * ζ ^ Ep / K ^ Ep / K ^ Ep ≤ (a / h) * (ζ ^ E / K ^ E) := by
    calc
      _ ≤ a / h * ζ ^ Ep / K ^ Ep := div_le_self (by positivity) (one_le_pow₀ hK1)
      _ = (a / h) * (ζ ^ Ep / K ^ Ep) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by positivity)
  refine ⟨hcoeff.1, hcoeff.2.1, hcoeff.2.2.1, hcoeff.2.2.2,
    hsmall.trans hpv, hsmall.trans hε, ?_⟩
  have hfit : a / h * ζ ^ Ep / K ^ Ep * (1 + 3 * K * AT C e K) ≤
      (a / h) * (ζ ^ E / K ^ E) := by
    calc
      _ = (a / h) * (amp K * (ζ ^ Ep / K ^ Ep)) := by dsimp only [amp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratioAmp (by positivity)
  exact hfit.trans herr

end Submission.Obl.k4_physical_row_packet_potential.Glue
