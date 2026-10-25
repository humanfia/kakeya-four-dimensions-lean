import Submission.Obl.k4_raw_localized_native_systems.Packing.MaskedWindow
import Submission.Obl.k4_raw_localized_native_systems.Packing.TubeBudget
import Submission.Obl.k4_raw_localized_native_systems.Packing.FramePowers
import Submission.Obl.k4_raw_localized_native_systems.Packing.Numerics

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section
set_option maxRecDepth 4096

/-- Full earlier witness mass packing from the actual homogeneous source
frames, short-major cutoff and co-observed angle threshold. The common mask
and every original formatted event are retained unchanged. -/
theorem raw_witness_mass_packing {p : Data} (hp : Valid p) {k M D : ℕ}
    (W : Atlas p k) {κ r K q g E χ ds s m τ nw band u ζ r₀ : ℝ}
    (hc : ∀ e, Window.WChart p k W M D κ r e)
    (hκ : 0 ≤ κ) (hκK : κ ≤ K) (hK : 1 ≤ K) (hκsq : 2 * κ ^ 2 ≤ K)
    (hqtime : q = 1 / (2 : ℝ) ^ W.T)
    (hgpow : g = p.N k ^ (-nw - band)) (hEpow : E = p.N k ^ (2 * band + u))
    (hband0 : 0 ≤ band) (hu : 0 ≤ u) (hwindow : p.N k ^ (-m) ≤ q)
    (hpoly : 2097152 * Real.pi * K ^ (8 + 1) ≤ p.N k ^ ζ)
    (hprofile : p.f r - p.f 0 + τ + 4 * band + 2 * u + ζ ≤ ds * s + χ)
    (Good : Fin (p.W k) → Set Point) (γ : Fin (p.W k)) (I : Finset (Fin W.C))
    (hworld : ∀ e ∈ I, W.γ e = γ)
    (hknown : ∀ e z, z ∈ W.F e →
      e ∈ W.lst (W.γ e) (obs (p.B k (W.γ e)) (δ (p.N k) p.L) z))
    (hcard : ∀ o, ((W.lst γ o).card : ℝ) ≤ K)
    (hcap : Measure.map Window.basePt ((selected p k γ).restrict (Good γ)) ≤
      ENNReal.ofReal (64 * K ^ 2 * p.N k ^ (-p.f 0 + τ)) • volume)
    (width : Fin W.C → ℝ)
    (hexact : ∀ e ∈ I, p.N k ^ (-width e) = |(W.Q e).det| * (4 : ℝ) ^ W.T)
    (hband : ∀ e ∈ I, |width e - nw| ≤ band)
    (hcut : ∀ e ∈ I, q * p.N k ^ (-u) ≤ ‖longCol (W.Q e)‖)
    (hfloor : ∀ e ∈ I,
      ENNReal.ofReal (p.N k ^ (-p.f r) * |(W.Q e).det| / ((2 : ℝ) ^ W.T * K)) ≤
        Window.rawMass W (maskedWitnessEvents W Good) e)
    {n : Plane} (hn : ‖n‖ = 1) {t y₀ α β : ℝ}
    (hangle : ∀ e ∈ I, min ‖n - minorNormal (W.Q e)‖ ‖n + minorNormal (W.Q e)‖ ≤
      32 * κ * minorWidth (W.Q e) * p.N k ^ u / q)
    (hr₀ : r₀ ≤ K * q * g * E ^ 2)
    (hanchor : ∀ e ∈ I, ∃ z ∈ W.F e,
      |z.2 - t| ≤ p.N k ^ (-m) ∧
      |tangentValue (tangentOfNormal n) z.1 z.2 - y₀| ≤ p.N k ^ (-m) ∧
      |inner ℝ (y z.1 z.2 - α • n - z.2 • (β • n)) n| ≤ r₀ ∧
      ‖v z.1‖ ≤ K ∧ |inner ℝ n (v z.1 - β • n)| ≤ 2 * r₀) :
    ∃ v₀ : ℝ, 0 < v₀ ∧
      (∀ e ∈ I, ENNReal.ofReal v₀ ≤ Window.rawMass W (maskedWitnessEvents W Good) e) ∧
      (∑ e ∈ I, Window.rawMass W (maskedWitnessEvents W Good) e) ≤
        ENNReal.ofReal (v₀ * p.N k ^ (ds * s + χ)) := by
  have hN := hp.scale_ge_one k
  have hN0 := hp.scale_pos k
  have hK0 : 0 < K := by linarith
  have hq : 0 < q := by rw [hqtime]; positivity
  have hq1 : q ≤ 1 := by
    rw [hqtime, div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hg : 0 < g := by rw [hgpow]; positivity
  have hE : 1 ≤ E := by
    rw [hEpow]
    exact Real.one_le_rpow hN (by linarith)
  have hNuE : p.N k ^ u ≤ E := by
    rw [hEpow]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hdet (e : Fin W.C) (he : e ∈ I) :
      q ^ 2 * g ≤ |(W.Q e).det| ∧
        |(W.Q e).det| ≤ q ^ 2 * g * p.N k ^ (2 * band) := by
    simpa only [hgpow] using
      determinant_band_bounds hN hqtime (hexact e he) (hband e he)
  have hminor (e : Fin W.C) (he : e ∈ I) : minorWidth (W.Q e) ≤ q * g * E := by
    simpa only [hEpow] using minor_width_power_bound hN hq hg.le
      (hdet e he).2 (hcut e he)
  have hgeom (e : Fin W.C) (he : e ∈ I) :
      ‖W.u e‖ ≤ 3 * K ^ 2 ∧
        min ‖n - minorNormal (W.Q e)‖ ‖n + minorNormal (W.Q e)‖ ≤
          32 * K * g * E ^ 2 ∧
        |inner ℝ (W.u e - β • n) n| ≤ 64 * K ^ 2 * g * E ^ 2 := by
    obtain ⟨z, hz, ht, hy, hr, hv, hcv⟩ := hanchor e he
    exact compatible_frame_tube_bounds (hc e) ((hc e).sel hz).2.1
      hκ hκK hK hκsq hq hq1 hqtime hg.le hE
      (Real.rpow_nonneg hN0.le _) hNuE (hminor e he) (hangle e he) hv hr₀ hcv
  have hanchors : ∀ e ∈ I, ∃ z ∈ W.F e,
      |z.2 - t| ≤ p.N k ^ (-m) ∧
      |tangentValue (tangentOfNormal n) z.1 z.2 - y₀| ≤ p.N k ^ (-m) ∧
      |inner ℝ (y z.1 z.2 - α • n - z.2 • (β • n)) n| ≤ r₀ := by
    intro e he
    obtain ⟨z, hz, ht, hy, hr, -, -⟩ := hanchor e he
    exact ⟨z, hz, ht, hy, hr⟩
  have hupper := witness_window_mass_le_polynomial W hc hκ hκK hK hqtime hg hE
    (Real.rpow_nonneg hN0.le _) γ I hworld hknown hcard
    ((selected p k γ).restrict (Good γ)) hcap hn hwindow
    (fun e _ => chart_major_bound (hc e) hκK hqtime) hminor
    (fun e he => (hgeom e he).2.1) (fun e he => (hgeom e he).1)
    (fun e he => (hgeom e he).2.2) hr₀ hanchors
  have hmass_eq : (∑ e ∈ I, Window.rawMass W (maskedWitnessEvents W Good) e) =
      ∑ e ∈ I, ((selected p k γ).restrict (Good γ)) (W.F e) :=
    Finset.sum_congr rfl fun e he => masked_witness_mass_eq (hc e) Good (hworld e he)
  rw [← hmass_eq] at hupper
  have hpower : p.N k ^ (-p.f 0 + τ) * E ^ 2 =
      p.N k ^ (-p.f 0 + τ + 4 * band + 2 * u) := by
    rw [hEpow, pow_two, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1
    ring
  have hupper' : (∑ e ∈ I, Window.rawMass W (maskedWitnessEvents W Good) e) ≤
      ENNReal.ofReal (2097152 * Real.pi * K ^ 8 *
        p.N k ^ (-p.f 0 + τ + 4 * band + 2 * u) * (q ^ 3 * g)) := by
    convert hupper using 1
    congr 1
    rw [← hpower]
    ring
  have hfloor' : ∀ e ∈ I, ENNReal.ofReal (p.N k ^ (-p.f r) * (q ^ 3 * g) / K) ≤
      Window.rawMass W (maskedWitnessEvents W Good) e := by
    intro e he
    apply le_trans _ (hfloor e he)
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = p.N k ^ (-p.f r) * (q ^ 2 * g) * q / K := by ring
      _ ≤ p.N k ^ (-p.f r) * |(W.Q e).det| * q / K := by
        gcongr
        exact (hdet e he).1
      _ = _ := by rw [hqtime]; field_simp
  exact raw_mass_packing_of_power_bounds I
    (Window.rawMass W (maskedWitnessEvents W Good)) 8 hN hK0 (by positivity)
    hpoly (by linarith only [hprofile]) hfloor' hupper'

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
