import Submission.Obl.k4_raw_localized_native_systems.Window.NativeRawAssembly
import Submission.Obl.k4_raw_localized_native_systems.Window.NativePacking
import Submission.Obl.k4_raw_localized_native_systems.Window.OriginalCaps

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing Packing

noncomputable section

/-- A finite native certificate from the original homogeneous earlier family.
The density, packing and inverse-frame clauses are all derived here, retaining
the entire common-masked earlier laws and their original weights. -/
theorem raw_support_of_homogeneous_native_family {p : Data} (hp : Valid p) {k M D : ℕ}
    {κ r τ χ ds s gC κC K q g E nw band u ζ : ℝ}
    (hχ : 0 < χ) (hpow : 2 ≤ p.N k ^ χ) (hN : 256 ≤ p.N k) (hs : s ≤ 1)
    (hκ : 1 ≤ κ) (hκK : κ ≤ K) (hK : 1 ≤ K) (hκsq : 2 * κ ^ 2 ≤ K)
    (hKN : K ≤ p.N k) (hpriorK : p.K k ≤ K) (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (W : Atlas p k) (defaultLabel : Fin W.C)
    (hW : ∀ e, WChart p k W M D κ r e)
    (Good : Fin (p.W k) → Set Point) (hGood : ∀ γ, MeasurableSet (Good γ))
    (hfloor : ∀ e, ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| /
      ((2 : ℝ) ^ W.T * κ)) ≤ rawMass W (maskedWitnessEvents W Good) e)
    (hgood : ∀ γ z, z ∈ Good γ →
      p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) ≤
        ENNReal.ofReal (p.N k ^ (-p.f r + τ)))
    (hzero : ∀ γ z, z ∈ Good γ → p.g k γ 0 (obs (p.B k γ) 1 z) ≤
      ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)))
    (hvel : ∀ γ z, z ∈ Good γ → ‖v z.1‖ ≤ K)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (hbudget : 64 * κ ^ 3 * p.N k ^ τ ≤ p.N k ^ χ)
    (hscale : 1 + κ ≤ p.N k ^ χ) (hKχ : p.K k ≤ p.N k ^ χ)
    (hvalue : κ * δ (p.N k) r ≤ p.N k ^ χ * p.N k ^ (-s + χ))
    (hcurv : κ / δ (p.N k) r ≤ p.N k ^ χ / p.N k ^ (-s + χ))
    (hT : (2 : ℝ) ^ W.T ≤ p.N k)
    (hqtime : q = 1 / (2 : ℝ) ^ W.T)
    (hgpow : g = p.N k ^ (-nw - band)) (hEpow : E = p.N k ^ (2 * band + u))
    (hband0 : 0 ≤ band) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hEbound : E ≤ p.N k ^ (4 : ℕ)) (hangleCost : 32 * κ * p.N k ^ u ≤ p.N k)
    (hwindow : p.N k ^ (-(s + 4)) ≤ q)
    (hpoly : 2097152 * Real.pi * K ^ (8 + 1) ≤ p.N k ^ ζ)
    (hprofile : p.f r - p.f 0 + τ + 4 * band + 2 * u + ζ ≤ ds * s + χ)
    (hknown : ∀ e z, z ∈ W.F e →
      e ∈ W.lst (W.γ e) (obs (p.B k (W.γ e)) (δ (p.N k) p.L) z))
    (hcard : ∀ γ o, ((W.lst γ o).card : ℝ) ≤ K)
    (width : Fin W.C → ℝ)
    (hexact : ∀ e, p.N k ^ (-width e) = |(W.Q e).det| * (4 : ℝ) ^ W.T)
    (hband : ∀ e, |width e - nw| ≤ band)
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
    (hcover : ∀ a, law a (rawSupportSet W (maskedWitnessEvents W Good) Compat FC a)ᶜ = 0)
    (hn : ∀ a, ‖n a‖ = 1) (hgC : 0 ≤ gC) (hκC : 0 ≤ κC) (hκCK : κC ≤ K)
    (hFCsub : ∀ a z, z ∈ FC a → z.1 ∈ AC a ∧ z.2 ∈ Icc (0 : ℝ) 1)
    (hstrip : ∀ a l, l ∈ AC a → ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (n a) (y l t) - int a - t * sp a| ≤ κC * gC)
    (hcut : ∀ a e, Compat a e → q * p.N k ^ (-u) ≤ ‖longCol (W.Q e)‖)
    (hangle : ∀ a e, Compat a e →
      min ‖n a - minorNormal (W.Q e)‖ ‖n a + minorNormal (W.Q e)‖ ≤
        32 * κ * minorWidth (W.Q e) * p.N k ^ u / q)
    (hrel : ∀ a e, Compat a e →
      gC ≤ minorWidth (W.Q e) / ((2 : ℝ) ^ W.T * p.N k ^ (4 : ℕ))) :
    RawSupport (p.N k) χ ds s (s + 4) C R law
      (fun a => fullTimeCoefficients (p.P k (γC a)) (normalTangent (n a)) (AC a)) := by
  have hN0 := hp.scale_pos k
  have hN1 := hp.scale_ge_one k
  have hκ0 : 0 < κ := by linarith
  have hq : 0 < q := by rw [hqtime]; positivity
  have hcap (γ : Fin (p.W k)) :=
    masked_original_zero_base_cap hp k γ hK hpriorK (Good γ) (hGood γ) (hzero γ)
  have hfloorK (e : Fin W.C) :
      ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| / ((2 : ℝ) ^ W.T * K)) ≤
        rawMass W (maskedWitnessEvents W Good) e := by
    apply le_trans _ (hfloor e)
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hκK (by positivity))
  have hmajorRaw (a : Fin C) (e : Fin W.C) (hc : Compat a e) :
      1 / (p.N k * (2 : ℝ) ^ W.T) ≤ ‖longCol (W.Q e)‖ := by
    apply le_trans _ (hcut a e hc)
    calc
      _ = q * p.N k ^ (-1 : ℝ) := by rw [hqtime, Real.rpow_neg_one]; ring
      _ ≤ q * p.N k ^ (-u) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hq.le
  have hangleRaw (a : Fin C) (e : Fin W.C) (hc : Compat a e) :
      min ‖n a - minorNormal (W.Q e)‖ ‖n a + minorNormal (W.Q e)‖ ≤
        p.N k * minorWidth (W.Q e) * (2 : ℝ) ^ W.T := by
    apply (hangle a e hc).trans
    calc
      _ = (32 * κ * p.N k ^ u) * (minorWidth (W.Q e) / q) := by ring
      _ ≤ p.N k * (minorWidth (W.Q e) / q) :=
        mul_le_mul_of_nonneg_right hangleCost (div_nonneg (minorWidth_nonneg _) hq.le)
      _ = _ := by rw [hqtime]; field_simp
  have hpack := native_witness_mass_packing hp W hW hκ0.le hκK hK hκsq
    hqtime hgpow hEpow hband0 hu0 hwindow hpoly hprofile Good hknown hcard hcap
    width hexact hband hfloorK hvel γC AC FC n int sp Compat hcw hn hFCsub hstrip
    hcut hangle hgC hκCK hEbound hrel
  exact raw_support_of_native_family hp hχ hpow hN hs hκ (hκK.trans hKN) hr hrL
    W (maskedWitnessEvents W Good) defaultLabel hW
    (fun e => (hW e).measF.inter (hGood _)) (fun _ => inter_subset_left)
    hfloor (fun e z hz => hgood _ z hz.2) hdisj hbudget hscale hKχ hvalue hcurv hT
    (fun _ z hz => (hvel _ z hz.2).trans hKN)
    γC AC FC law R n int sp Compat hcw hFC hACdisj hR hlaw hcover hn hgC hκC
    (hκCK.trans hKN) hFCsub hstrip hmajorRaw hangleRaw hrel hpack

end
end Submission.Obl.k4_raw_localized_native_systems.Window
