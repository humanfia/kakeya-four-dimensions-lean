import Submission.Obl.k4_raw_localized_native_systems.Window.NativeIdentity
import Submission.Obl.k4_raw_localized_native_systems.Packing.RawMassPacking

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing Packing

noncomputable section

/-- The full-mass packing input for the native certificate, derived from the
original lists, the common original-law cap and the actual homogeneous frames. -/
theorem native_witness_mass_packing {p : Data} (hp : Valid p) {k M D : ℕ}
    (W : Atlas p k) {κ r K q g E χ ds s m τ nw band u ζ gC κC : ℝ}
    (hW : ∀ e, WChart p k W M D κ r e)
    (hκ : 0 ≤ κ) (hκK : κ ≤ K) (hK : 1 ≤ K) (hκsq : 2 * κ ^ 2 ≤ K)
    (hqtime : q = 1 / (2 : ℝ) ^ W.T)
    (hgpow : g = p.N k ^ (-nw - band)) (hEpow : E = p.N k ^ (2 * band + u))
    (hband0 : 0 ≤ band) (hu : 0 ≤ u) (hwindow : p.N k ^ (-m) ≤ q)
    (hpoly : 2097152 * Real.pi * K ^ (8 + 1) ≤ p.N k ^ ζ)
    (hprofile : p.f r - p.f 0 + τ + 4 * band + 2 * u + ζ ≤ ds * s + χ)
    (Good : Fin (p.W k) → Set Point)
    (hknown : ∀ e z, z ∈ W.F e →
      e ∈ W.lst (W.γ e) (obs (p.B k (W.γ e)) (δ (p.N k) p.L) z))
    (hcard : ∀ γ o, ((W.lst γ o).card : ℝ) ≤ K)
    (hcap : ∀ γ, Measure.map basePt ((selected p k γ).restrict (Good γ)) ≤
      ENNReal.ofReal (64 * K ^ 2 * p.N k ^ (-p.f 0 + τ)) • volume)
    (width : Fin W.C → ℝ)
    (hexact : ∀ e, p.N k ^ (-width e) = |(W.Q e).det| * (4 : ℝ) ^ W.T)
    (hband : ∀ e, |width e - nw| ≤ band)
    (hfloor : ∀ e,
      ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| / ((2 : ℝ) ^ W.T * K)) ≤
        rawMass W (maskedWitnessEvents W Good) e)
    (hvel : ∀ γ z, z ∈ Good γ → ‖v z.1‖ ≤ K)
    {C : ℕ} (γC : Fin C → Fin (p.W k)) (AC : Fin C → Set Line)
    (FC : Fin C → Set Point) (n : Fin C → Plane) (int sp : Fin C → ℝ)
    (Compat : Fin C → Fin W.C → Prop)
    (hcw : ∀ a e, Compat a e → W.γ e = γC a)
    (hn : ∀ a, ‖n a‖ = 1)
    (hFCsub : ∀ a z, z ∈ FC a → z.1 ∈ AC a ∧ z.2 ∈ Icc (0 : ℝ) 1)
    (hstrip : ∀ a l, l ∈ AC a → ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (n a) (y l t) - int a - t * sp a| ≤ κC * gC)
    (hcut : ∀ a e, Compat a e → q * p.N k ^ (-u) ≤ ‖longCol (W.Q e)‖)
    (hangle : ∀ a e, Compat a e →
      min ‖n a - minorNormal (W.Q e)‖ ‖n a + minorNormal (W.Q e)‖ ≤
        32 * κ * minorWidth (W.Q e) * p.N k ^ u / q)
    (hgC : 0 ≤ gC) (hκCK : κC ≤ K) (hEbound : E ≤ p.N k ^ (4 : ℕ))
    (hrel : ∀ a e, Compat a e →
      gC ≤ minorWidth (W.Q e) / ((2 : ℝ) ^ W.T * p.N k ^ (4 : ℕ))) :
    ∀ a t y' (I : Finset (Fin W.C)),
      (∀ e ∈ I, ∃ z ∈ FC a, z ∈ maskedWitnessEvents W Good e ∧ Compat a e ∧
        |z.2 - t| ≤ p.N k ^ (-m) ∧
        |inner ℝ (normalTangent (n a)) (y z.1 z.2) - y'| ≤ p.N k ^ (-m)) →
      ∃ v₀ : ℝ, 0 < v₀ ∧
        (∀ e ∈ I, ENNReal.ofReal v₀ ≤ rawMass W (maskedWitnessEvents W Good) e) ∧
        (∑ e ∈ I, rawMass W (maskedWitnessEvents W Good) e) ≤
          ENNReal.ofReal (v₀ * p.N k ^ (ds * s + χ)) := by
  intro a t y' I hI
  classical
  by_cases hIempty : I = ∅
  · subst I
    exact ⟨1, zero_lt_one, by simp, by simp⟩
  have hc (e : Fin W.C) (he : e ∈ I) : Compat a e := by
    obtain ⟨z, _, _, h, _, _⟩ := hI e he
    exact h
  have hN := hp.scale_ge_one k
  have hN0 := hp.scale_pos k
  have hq : 0 < q := by rw [hqtime]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqtime, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hg : 0 < g := by rw [hgpow]; positivity
  have hE : 1 ≤ E := by
    rw [hEpow]
    exact Real.one_le_rpow hN (by linarith)
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hIempty
  have hdet := determinant_band_bounds hN hqtime (hexact e) (hband e)
  rw [← hgpow] at hdet
  have hminor : minorWidth (W.Q e) ≤ q * g * E := by
    rw [hEpow]
    exact minor_width_power_bound hN hq hg.le hdet.2 (hcut a e (hc e he))
  have hrel' : gC ≤ minorWidth (W.Q e) * q / p.N k ^ (4 : ℕ) := by
    convert hrel a e (hc e he) using 1
    rw [hqtime]
    field_simp
  have hthin := strip_radius_from_relative_width hN0 hq.le hq1 hg.le hE hEbound
    (by linarith : 0 ≤ K) hminor hrel' (mul_le_mul_of_nonneg_right hκCK hgC)
  apply raw_witness_mass_packing hp W hW hκ hκK hK hκsq hqtime hgpow hEpow
    hband0 hu hwindow hpoly hprofile Good (γC a) I
    (fun e he => hcw a e (hc e he)) hknown (hcard (γC a)) (hcap (γC a)) width
    (fun e _ => hexact e) (fun e _ => hband e) (fun e he => hcut a e (hc e he))
    (fun e _ => hfloor e) (hn a)
    (fun e he => hangle a e (hc e he)) hthin
  intro e he
  obtain ⟨z, hz, hzH, _, hzt, hzy⟩ := hI e he
  refine ⟨z, hzH.1, hzt, ?_, ?_, hvel _ z hzH.2, ?_⟩
  · simpa only [tangentValue, normalTangent_eq, real_inner_comm] using hzy
  · have hself : inner ℝ (n a) (n a) = 1 := by
      rw [real_inner_self_eq_norm_sq, hn a]
      norm_num
    rw [real_inner_comm, inner_sub_right, inner_sub_right,
      inner_smul_right, inner_smul_right, inner_smul_right, hself]
    simpa only [mul_one] using hstrip a z.1 (hFCsub a z hz).1 z.2 (hFCsub a z hz).2
  · exact native_strip_velocity (hn a) (hstrip a z.1 (hFCsub a z hz).1)

end
end Submission.Obl.k4_raw_localized_native_systems.Window
