import Submission.Obl.k4_raw_localized_native_systems.Window.HomogeneousRawAssembly
import Submission.Obl.k4_raw_localized_native_systems.Window.LongGoodSets
import Submission.Obl.k4_raw_localized_native_systems.Packing.HomogeneousCompatibility

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing Packing

noncomputable section

/-- The long-heavy selection supplies the entire earlier family for the raw
certificate. Its floor is restored at twice the original slack, while the
assignment geometry, widths and observation policies remain the original ones. -/
theorem raw_support_of_long_good_family {p : Data} (hp : Valid p) {k M D : ℕ}
    {κ r τ χ ds s gC κC K q nw band a u θ ζ : ℝ}
    (hχ : 0 < χ) (hpow : 2 ≤ p.N k ^ χ) (hN : 256 ≤ p.N k) (hs : s ≤ 1)
    (hκ : 1 ≤ κ) (hκK : 2 * κ ≤ K) (hK : 1 ≤ K) (hκsq : 2 * (2 * κ) ^ 2 ≤ K)
    (hKN : K ≤ p.N k) (hpriorK : p.K k ≤ K) (hr : 0 ≤ r) (hrL : r ≤ p.L)
    (W : Atlas p k) (hW : ∀ e, WChart p k W M D κ r e)
    (hfloor : ∀ e, ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| /
      ((2 : ℝ) ^ W.T * κ)) ≤ wmass W e)
    (Good : Fin (p.W k) → Set Point) (hGood : ∀ γ, MeasurableSet (Good γ))
    (hnonempty : Nonempty (Fin (longHeavyWitnessSet W Good (q * p.N k ^ (-a))).card))
    (hgood : ∀ γ z, z ∈ Good γ →
      p.g k γ r (obs (p.B k γ) (δ (p.N k) r) z) ≤
        ENNReal.ofReal (p.N k ^ (-p.f r + τ)))
    (hzero : ∀ γ z, z ∈ Good γ → p.g k γ 0 (obs (p.B k γ) 1 z) ≤
      ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)))
    (hvel : ∀ γ z, z ∈ Good γ → ‖v z.1‖ ≤ K)
    (hdisj : ∀ e e', e ≠ e' → W.γ e = W.γ e' → W.j e = W.j e' →
      Disjoint (W.A e) (W.A e'))
    (hbudget : 64 * (2 * κ) ^ 3 * p.N k ^ τ ≤ p.N k ^ χ)
    (hscale : 1 + 2 * κ ≤ p.N k ^ χ) (hKχ : p.K k ≤ p.N k ^ χ)
    (hvalue : 2 * κ * δ (p.N k) r ≤ p.N k ^ χ * p.N k ^ (-s + χ))
    (hcurv : 2 * κ / δ (p.N k) r ≤ p.N k ^ χ / p.N k ^ (-s + χ))
    (hT : (2 : ℝ) ^ W.T ≤ p.N k) (hqtime : q = 1 / (2 : ℝ) ^ W.T)
    (hband0 : 0 ≤ band) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hau : a ≤ u)
    (hθ : θ ≤ 32 * p.N k ^ (-nw - band) * p.N k ^ u)
    (hEbound : p.N k ^ (2 * band + u) ≤ p.N k ^ (4 : ℕ))
    (hangleCost : 32 * (2 * κ) * p.N k ^ u ≤ p.N k)
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
    (hFC : ∀ c, MeasurableSet (FC c))
    (hACdisj : ∀ c c', c ≠ c' → γC c = γC c' → Disjoint (AC c) (AC c'))
    (hR : ∀ c, 0 < R c)
    (hlaw : ∀ c, R c • law c ≤
      ENNReal.ofReal (p.ω k (γC c)) • (priorMass p k (γC c)).restrict (FC c))
    (hcover : ∀ c, law c
      (rawSupportSet (selectWitnesses W (longHeavyWitnessSet W Good (q * p.N k ^ (-a))))
        (maskedWitnessEvents (selectWitnesses W
          (longHeavyWitnessSet W Good (q * p.N k ^ (-a)))) Good)
        (angleCompat (selectWitnesses W
          (longHeavyWitnessSet W Good (q * p.N k ^ (-a)))) γC n θ (q * p.N k ^ (-a))) FC c)ᶜ = 0)
    (hn : ∀ c, ‖n c‖ = 1) (hgC : 0 ≤ gC) (hκC : 0 ≤ κC) (hκCK : κC ≤ K)
    (hFCsub : ∀ c z, z ∈ FC c → z.1 ∈ AC c ∧ z.2 ∈ Icc (0 : ℝ) 1)
    (hstrip : ∀ c l, l ∈ AC c → ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (n c) (y l t) - int c - t * sp c| ≤ κC * gC)
    (hrel : ∀ e, gC ≤ minorWidth (W.Q e) / ((2 : ℝ) ^ W.T * p.N k ^ (4 : ℕ))) :
    RawSupport (p.N k) χ ds s (s + 4) C R law
      (fun c => fullTimeCoefficients (p.P k (γC c)) (normalTangent (n c)) (AC c)) := by
  let S := longHeavyWitnessSet W Good (q * p.N k ^ (-a))
  let V := selectWitnesses W S
  have hκ0 : 0 < κ := by linarith
  have hκ2 : 0 < 2 * κ := by positivity
  have hV : ∀ e, WChart p k V M D (2 * κ) r e :=
    selected_witness_chart hp hκ0 (by linarith) hW S
  have hVfloor : ∀ e, ENNReal.ofReal (p.N k ^ (-p.f r) * |(V.Q e).det| /
      ((2 : ℝ) ^ V.T * (2 * κ))) ≤ rawMass V (maskedWitnessEvents V Good) e := by
    intro e
    exact long_heavy_witness_floor hp hκ0 le_rfl hW hfloor Good _ e
  have hVexact (e : Fin V.C) : p.N k ^ (-(width (witnessIndex S e))) =
      |(V.Q e).det| * (4 : ℝ) ^ V.T := hexact _
  have hVband (e : Fin V.C) : |width (witnessIndex S e) - nw| ≤ band := hband _
  have hq : 0 < q := by rw [hqtime]; positivity
  have hN1 := hp.scale_ge_one k
  apply raw_support_of_homogeneous_native_family hp hχ hpow hN hs
    (by linarith : 1 ≤ 2 * κ) hκK hK hκsq hKN hpriorK hr hrL
    V (Classical.choice hnonempty) hV Good hGood hVfloor hgood hzero hvel
    (selected_witness_disjoint hdisj S) hbudget hscale hKχ hvalue hcurv hT
    hqtime rfl rfl hband0 hu0 hu1 hEbound hangleCost hwindow hpoly hprofile
    (selected_witness_known W S hknown) ?_
    (fun e => width (witnessIndex S e)) hVexact hVband γC AC FC law R n int sp
    (angleCompat V γC n θ (q * p.N k ^ (-a))) (fun _ _ hc => hc.1)
    hFC hACdisj hR hlaw hcover hn hgC hκC hκCK hFCsub hstrip ?_ ?_ ?_
  · intro γ o
    exact (Nat.cast_le.mpr (selected_witness_list_card W S γ o)).trans (hcard γ o)
  · intro c e hc
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : -u ≤ -a)) hq.le).trans hc.2.2
  · intro c e hc
    exact homogeneous_angle_bound hq hκ2 (hp.scale_pos k)
      (chart_minor_width_lower_bound (hV e) hN1 hκ2 hqtime (hVexact e) (hVband e)) hθ hc.2.1
  · intro c e _
    exact hrel (witnessIndex S e)

end
end Submission.Obl.k4_raw_localized_native_systems.Window
