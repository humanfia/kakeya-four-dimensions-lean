/- Adapted from this LOT tree, o197, session x0690, Packing/WitnessWindow.lean,
   branch snapshot 9f1b6476; preserving original attributions below. -/
import Submission.Obl.k4_raw_localized_native_systems.Packing.Mass
import Submission.Obl.k4_raw_localized_native_systems.Packing.Geometry
import Submission.Obl.k4_raw_localized_native_systems.Window.Witness

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option maxRecDepth 4096

theorem basePlane_basePt (z : Point) : basePlane (Window.basePt z) = y z.1 z.2 := by
  ext i
  fin_cases i <;> simp [basePlane, Window.basePt, y]

theorem basePt_time (z : Point) : Window.basePt z 0 = z.2 := rfl

/-- Full earlier witness masses of every family touched by one scalar window
are charged to its common enlarged base tube in the original law. -/
theorem witness_window_mass_le {p : Data} {k M D : ℕ} (W : Atlas p k)
    {κ r : ℝ} (hc : ∀ e, Window.WChart p k W M D κ r e)
    (γ : Fin (p.W k)) (I : Finset (Fin W.C))
    (hworld : ∀ e ∈ I, W.γ e = γ)
    (hknown : ∀ e z, z ∈ W.F e →
      e ∈ W.lst (W.γ e) (obs (p.B k (W.γ e)) (δ (p.N k) p.L) z))
    (Klist : ℝ) (hcard : ∀ o, ((W.lst γ o).card : ℝ) ≤ Klist)
    (μ : Measure Point) (Cbase : ENNReal)
    (hcap : Measure.map Window.basePt μ ≤ Cbase • volume)
    {n : Plane} (hn : ‖n‖ = 1) {t y₀ α β σ U V θ r₀ rt ry rn : ℝ}
    (hangle : ∀ e ∈ I, min ‖n - Pairing.minorNormal (W.Q e)‖
      ‖n + Pairing.minorNormal (W.Q e)‖ ≤ θ)
    (hU : ∀ e ∈ I, ‖W.u e‖ ≤ U)
    (hV : ∀ e ∈ I, |inner ℝ (W.u e - β • n) n| ≤ V)
    (hanchor : ∀ e ∈ I, ∃ z ∈ W.F e, |z.2 - t| ≤ σ ∧
      |tangentValue (tangentOfNormal n) z.1 z.2 - y₀| ≤ σ ∧
      |inner ℝ (y z.1 z.2 - α • n - z.2 • (β • n)) n| ≤ r₀)
    (htbudget : 1 / (2 : ℝ) ^ W.T + σ ≤ rt)
    (hybudget : ∀ e ∈ I,
      σ + 4 * κ * ‖Pairing.longCol (W.Q e)‖ + 1 / (2 : ℝ) ^ W.T * U ≤ ry)
    (hnbudget : ∀ e ∈ I,
      r₀ + 2 * κ * (Pairing.minorWidth (W.Q e) +
        2 * ‖Pairing.longCol (W.Q e)‖ * θ) + 1 / (2 : ℝ) ^ W.T * V ≤ rn)
    (hry : 0 < ry) (hrn : 0 < rn) :
    (∑ e ∈ I, μ (W.F e)) ≤
      ENNReal.ofReal Klist * Cbase * ENNReal.ofReal (8 * Real.pi * rt * ry * rn) := by
  classical
  let F (e : I) := W.F e.val
  let lst (z : Point) :=
    (W.lst γ (obs (p.B k γ) (δ (p.N k) p.L) z)).subtype (fun e => e ∈ I)
  have hF (e : I) : MeasurableSet (F e) := (hc e.val).measF
  have hmem (e : I) (z : Point) (hz : z ∈ F e) : e ∈ lst z := by
    have h := hknown e.val z hz
    simpa only [lst, Finset.mem_subtype, hworld e.val e.property] using h
  have hcard' (z : Point) : ((lst z).card : ENNReal) ≤ ENNReal.ofReal Klist := by
    calc
      ((lst z).card : ENNReal) ≤
          ((W.lst γ (obs (p.B k γ) (δ (p.N k) p.L) z)).card : ENNReal) := by
        rw [Finset.card_subtype]
        exact_mod_cast Finset.card_filter_le _ _
      _ ≤ ENNReal.ofReal Klist := by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (hcard _)
  have hFZ (e : I) : F e ⊆ Window.basePt ⁻¹' scalarWindowTube n t y₀ α β rt ry rn := by
    intro z hz
    obtain ⟨z₀, hz₀, ht₀, hy₀, hn₀⟩ := hanchor e.val e.property
    have hzt := ((hc e.val).sel hz).2.2.1
    have hz₀t := ((hc e.val).sel hz₀).2.2.1
    have he : (((W.j e.val : ℕ) : ℝ) + 1) / (2 : ℝ) ^ W.T =
        ((W.j e.val : ℕ) : ℝ) / (2 : ℝ) ^ W.T + 1 / (2 : ℝ) ^ W.T := by ring
    rw [he] at hzt hz₀t
    have hdt : |z.2 - z₀.2| ≤ 1 / (2 : ℝ) ^ W.T := by
      rw [abs_le]
      constructor <;> linarith [hzt.1, hzt.2, hz₀t.1, hz₀t.2]
    apply earlier_base_mem_scalarWindowTube (hc e.val).det_ne hn
      (hangle e.val e.property) (c := W.c e.val) (u := W.u e.val)
      (κ := κ) (q := 1 / (2 : ℝ) ^ W.T) (U := U) (V := V) (r₀ := r₀)
    · rw [basePlane_basePt]
      exact ((hc e.val).fit ((hc e.val).sel hz).2.1 ((hc e.val).sel hz).2.2.1).1
    · rw [basePlane_basePt]
      exact ((hc e.val).fit ((hc e.val).sel hz₀).2.1 ((hc e.val).sel hz₀).2.2.1).1
    · exact hdt
    · exact hU e.val e.property
    · exact hV e.val e.property
    · simpa only [basePlane_basePt, basePt_time] using hn₀
    · exact ht₀
    · simpa only [basePlane_basePt, tangentValue] using hy₀
    · exact htbudget
    · exact hybudget e.val e.property
    · exact hnbudget e.val e.property
    · exact hry
    · exact hrn
  have h := full_mass_le_base_volume μ volume Window.basePt Window.measurable_basePt F hF lst
    (ENNReal.ofReal Klist) Cbase hmem hcard' hcap
    (scalarWindowTube n t y₀ α β rt ry rn) (measurableSet_scalarWindowTube _ _ _ _ _ _ _ _) hFZ
  rw [volume_scalarWindowTube hn hry hrn] at h
  rw [← Finset.sum_coe_sort I]
  exact h

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
