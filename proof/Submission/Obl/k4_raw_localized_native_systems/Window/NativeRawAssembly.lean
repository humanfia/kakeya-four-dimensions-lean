import Submission.Obl.k4_raw_localized_native_systems.Window.RawAssembly
import Submission.Obl.k4_raw_localized_native_systems.Window.SupportCompatibility
import Submission.Obl.k4_raw_localized_native_systems.Window.NativeIdentity

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section

/-- The exact raw certificate for full-time native charts. Inverse estimates
are derived from actual trajectories in the two original events; compatibility
need only describe the world and the geometric cutoffs. -/
theorem raw_support_of_native_family {p : Data} (hp : Valid p) {k M D : ℕ}
    {κ r τ χ d s g κC : ℝ} (hχ : 0 < χ) (hpow : 2 ≤ p.N k ^ χ)
    (hN : 256 ≤ p.N k) (hs : s ≤ 1)
    (hκ : 1 ≤ κ) (hκN : κ ≤ p.N k) (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (W : Atlas p k) (H : Fin W.C → Set Point) (defaultLabel : Fin W.C)
    (hW : ∀ e, WChart p k W M D κ r e)
    (hH : ∀ e, MeasurableSet (H e)) (hHsub : ∀ e, H e ⊆ W.F e)
    (hfloor : ∀ e, ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| /
      ((2 : ℝ) ^ W.T * κ)) ≤ rawMass W H e)
    (hgood : ∀ e q, q ∈ H e →
      p.g k (W.γ e) r (obs (p.B k (W.γ e)) (δ (p.N k) r) q) ≤
        ENNReal.ofReal (p.N k ^ (-p.f r + τ)))
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (hbudget : 64 * κ ^ 3 * p.N k ^ τ ≤ p.N k ^ χ)
    (hscale : 1 + κ ≤ p.N k ^ χ) (hK : p.K k ≤ p.N k ^ χ)
    (hvalue : κ * δ (p.N k) r ≤ p.N k ^ χ * p.N k ^ (-s + χ))
    (hcurv : κ / δ (p.N k) r ≤ p.N k ^ χ / p.N k ^ (-s + χ))
    (hT : (2 : ℝ) ^ W.T ≤ p.N k)
    (hvel : ∀ e q, q ∈ H e → ‖v q.1‖ ≤ p.N k)
    {C : ℕ} (γC : Fin C → Fin (p.W k)) (AC : Fin C → Set Line)
    (FC : Fin C → Set Point) (law : Fin C → Measure Point) (R : Fin C → ENNReal)
    (n : Fin C → Plane) (int sp : Fin C → ℝ)
    (Compat : Fin C → Fin W.C → Prop)
    (hcw : ∀ a e, Compat a e → W.γ e = γC a)
    (hFC : ∀ a, MeasurableSet (FC a))
    (hACdisj : ∀ a a', a ≠ a' → γC a = γC a' → Disjoint (AC a) (AC a'))
    (hR : ∀ a, 0 < R a)
    (hlaw : ∀ a, R a • law a ≤
      ENNReal.ofReal (p.ω k (γC a)) • (priorMass p k (γC a)).restrict (FC a))
    (hcover : ∀ a, law a (rawSupportSet W H Compat FC a)ᶜ = 0)
    (hn : ∀ a, ‖n a‖ = 1) (hg : 0 ≤ g) (hκC : 0 ≤ κC) (hκCN : κC ≤ p.N k)
    (hFCsub : ∀ a q, q ∈ FC a → q.1 ∈ AC a ∧ q.2 ∈ Icc (0 : ℝ) 1)
    (hstrip : ∀ a l, l ∈ AC a → ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (n a) (y l t) - int a - t * sp a| ≤ κC * g)
    (hmajor : ∀ a e, Compat a e →
      1 / (p.N k * (2 : ℝ) ^ W.T) ≤ ‖longCol (W.Q e)‖)
    (hangle : ∀ a e, Compat a e →
      min ‖n a - minorNormal (W.Q e)‖ ‖n a + minorNormal (W.Q e)‖ ≤
        p.N k * minorWidth (W.Q e) * (2 : ℝ) ^ W.T)
    (hrel : ∀ a e, Compat a e →
      g ≤ minorWidth (W.Q e) / ((2 : ℝ) ^ W.T * p.N k ^ (4 : ℕ)))
    (hpack : ∀ a t y' (I : Finset (Fin W.C)),
      (∀ e ∈ I, ∃ q ∈ FC a, q ∈ H e ∧ Compat a e ∧ |q.2 - t| ≤ p.N k ^ (-(s + 4)) ∧
        |inner ℝ (normalTangent (n a)) (y q.1 q.2) - y'| ≤ p.N k ^ (-(s + 4))) →
      ∃ z : ℝ, 0 < z ∧ (∀ e ∈ I, ENNReal.ofReal z ≤ rawMass W H e) ∧
        (∑ e ∈ I, rawMass W H e) ≤ ENNReal.ofReal (z * p.N k ^ (d * s + χ))) :
    RawSupport (p.N k) χ d s (s + 4) C R law
      (fun a => fullTimeCoefficients (p.P k (γC a)) (normalTangent (n a)) (AC a)) := by
  let Cp := supportCompat W H FC Compat
  have hCp : ∀ a e, Cp a e → Compat a e := fun _ _ h => h.1
  have hcover' : ∀ a, law a (rawSupportSet W H Cp FC a)ᶜ = 0 := by
    intro a
    rw [rawSupportSet_supportCompat]
    exact hcover a
  have hFCdisj : ∀ a a', a ≠ a' → γC a = γC a' → Disjoint (FC a) (FC a') := by
    intro a a' hne hγ
    apply Set.disjoint_left.mpr
    intro q hq hq'
    exact Set.disjoint_left.mp (hACdisj a a' hne hγ)
      (hFCsub a q hq).1 (hFCsub a' q hq').1
  apply raw_support_of_family hp hχ hpow hκ hr hrL W H defaultLabel hW hH hHsub
    hfloor hgood hdisj hbudget hscale hK hvalue hcurv γC FC law R
    (fun a => fullTimeCoefficients (p.P k (γC a)) (normalTangent (n a)) (AC a))
    n (fun a => int a • n a) (fun a => sp a • n a) (fun _ => κC * g) (fun _ => 0)
    Cp (fun a e hc => hcw a e hc.1) hFC hFCdisj hR hlaw hcover'
  · intro a q hq
    exact (native_full_time_identities _ (valid_P_degree hp k (γC a))
      (n a) (hFCsub a q hq).1 q.2).1
  · exact native_family_geometry _ n int sp (fun _ => κC * g) AC FC hn
      (fun _ => mul_nonneg hκC hg) hFCsub hstrip
  · intro a t y' I hI
    apply hpack a t y' I
    intro e he
    obtain ⟨q, hq, hqe, hc, hqt, hqy⟩ := hI e he
    refine ⟨q, hq, hqe, hc.1, hqt, ?_⟩
    rwa [(native_full_time_identities _ (valid_P_degree hp k (γC a))
      (n a) (hFCsub a q hq).1 q.2).2] at hqy
  · intro a e hc
    obtain ⟨q, hq, hqe⟩ := hc.2
    have hl : q.1 ∈ W.A e := ((hW e).sel (hHsub e hqe)).2.1
    have hspeed := native_strip_velocity (hn a) (hstrip a q.1 (hFCsub a q hq).1)
    exact raw_inverse_bounds hN hχ.le hs hκ hκN hT (hW e) hl (hn a)
      (hvel e q hqe) hg (mul_nonneg hκC hg)
      (mul_le_mul_of_nonneg_right hκCN hg)
      (hspeed.trans (by nlinarith [mul_le_mul_of_nonneg_right hκCN hg]))
      (hmajor a e hc.1) (hangle a e hc.1) (hrel a e hc.1)

end
end Submission.Obl.k4_raw_localized_native_systems.Window
