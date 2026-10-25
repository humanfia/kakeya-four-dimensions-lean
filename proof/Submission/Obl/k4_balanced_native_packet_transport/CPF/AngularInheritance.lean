/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/AngularInheritance.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.NativeCoarseningTail
import Submission.Obl.k4_native_grid_profile_extension.Profiles.TypicalDensity
import Submission.Obl.k4_profile_density_bounds.Asymptotics

/-! The full asymptotic angular-cap clause inherited at a smaller pure depth. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory Set Filter
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open scoped ENNReal

theorem Data.Valid.angular_typical_at_depth {p : Data} (hp : p.Valid)
    {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ p.L)
    {u τ : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ γ, ENNReal.ofReal (p.ω k γ) * p.selected k γ
        {z | ENNReal.ofReal (p.N k ^ (-p.f r - p.S * u + τ)) <
          coarsenedAngularDensity p r k γ u
            (nativeJointObs (p.B k γ) (p.N k) r u z)}) ≤
        ENNReal.ofReal (p.N k ^ (-c)) := by
  have hp₀ := hp
  rcases hp with ⟨hN, hNt, _, hL, _, _, _, _, _, _, _, _, htyp, _, hang⟩
  have he : 0 < τ / 4 := by positivity
  let a : ℕ → ℝ≥0∞ := fun k => ∑ γ, ENNReal.ofReal (p.ω k γ) * p.selected k γ
    {z | p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) z) <
      ENNReal.ofReal (p.N k ^ (-p.f p.L - τ / 4))}
  let b : ℕ → ℝ≥0∞ := fun k => ∑ γ, ENNReal.ofReal (p.ω k γ) * p.selected k γ
    {z | ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ / 4)) <
      p.G k γ u (nativeJointObs (p.B k γ) (p.N k) p.L u z)}
  let d : ℕ → ℝ≥0∞ := fun k => ∑ γ, ENNReal.ofReal (p.ω k γ) * p.selected k γ
    {z | ENNReal.ofReal (p.N k ^ (-p.f r + τ / 4)) <
      p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z)}
  have ha : IsPowerSmall p.N a := by
    apply IsPowerSmall.mono (htyp p.L (τ / 4) hL.le le_rfl he)
    exact Eventually.of_forall fun k => Finset.sum_le_sum fun γ _ =>
      mul_le_mul' le_rfl (measure_mono fun z hz => Or.inl hz)
  have hb : IsPowerSmall p.N b := hang u (τ / 4) hu huη he
  have hd : IsPowerSmall p.N d := by
    apply IsPowerSmall.mono (htyp r (τ / 4) hr hrL he)
    exact Eventually.of_forall fun k => Finset.sum_le_sum fun γ _ =>
      mul_le_mul' le_rfl (measure_mono fun z hz => Or.inr hz)
  have hsmall : IsPowerSmall p.N (fun k => 2 * (a k + b k) + d k) := by
    simpa only [two_mul] using ((ha.add hNt hb).add hNt (ha.add hNt hb)).add hNt hd
  apply hsmall.mono
  have hevent := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
    hNt (show -p.f r - p.S * u + 3 * τ / 4 < -p.f r - p.S * u + τ by linarith) 2
  filter_upwards [hevent] with k hk
  have hNk : 0 < p.N k := lt_of_lt_of_le (by norm_num) (hN k)
  let c := ENNReal.ofReal (p.N k ^ (-p.S * u + τ / 2))
  let lo := ENNReal.ofReal (p.N k ^ (-p.f p.L - τ / 4))
  let hi := ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ / 4))
  let U := ENNReal.ofReal (p.N k ^ (-p.f r + τ / 4))
  have hscale : hi ≤ c * lo := by
    apply le_of_eq
    dsimp [hi, c, lo]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNk.le _), ← Real.rpow_add hNk]
    congr 2
    ring
  have hthreshold : 2 * c * U ≤ ENNReal.ofReal (p.N k ^ (-p.f r - p.S * u + τ)) := by
    have hreal : 2 * p.N k ^ (-p.S * u + τ / 2) * p.N k ^ (-p.f r + τ / 4) ≤
        p.N k ^ (-p.f r - p.S * u + τ) := by
      calc
        _ = 2 * p.N k ^ (-p.f r - p.S * u + 3 * τ / 4) := by
          rw [mul_assoc, ← Real.rpow_add hNk]
          congr 2
          ring
        _ ≤ _ := hk.le
    convert ENNReal.ofReal_le_ofReal hreal using 1 <;>
      simp only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * p.N k ^ (-p.S * u + τ / 2)),
        ENNReal.ofReal_ofNat, c, U]
  calc
    _ ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) *
        (2 * (p.selected k γ {z | p.g k γ p.L
              (obs (p.B k γ) (δ (p.N k) p.L) z) < lo} +
          p.selected k γ {z | hi < p.G k γ u
            (nativeJointObs (p.B k γ) (p.N k) p.L u z)}) +
          p.selected k γ {z | U < p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z)}) := by
      apply Finset.sum_le_sum
      intro γ _
      apply mul_le_mul' le_rfl
      apply (measure_mono (fun z hz => hthreshold.trans_lt hz)).trans
      exact hp₀.angular_coarsening_tail hr hrL hu huη k γ c lo hi U hscale
    _ = 2 * (a k + b k) + d k := by
      dsimp only [a, b, d, lo, hi, U]
      simp only [two_mul, mul_add, Finset.sum_add_distrib]

end Submission.Obl.k4_balanced_native_packet_transport.CPF
