import Submission.Obl.k4_raw_localized_native_systems.Packing.WitnessWindow
import Submission.Obl.k4_raw_localized_native_systems.Window.RawLaws

namespace Submission.Obl.k4_raw_localized_native_systems.Packing

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The entire earlier reference event under one common original-law mask. -/
def maskedWitnessEvents {p : Data} {k : ℕ} (W : Atlas p k)
    (Good : Fin (p.W k) → Set Point) (e : Fin W.C) : Set Point :=
  W.F e ∩ Good (W.γ e)

theorem masked_witness_mass_eq {p : Data} {k M D : ℕ} {W : Atlas p k}
    {κ r : ℝ} {e : Fin W.C} (hc : Window.WChart p k W M D κ r e)
    (Good : Fin (p.W k) → Set Point) {γ : Fin (p.W k)} (hγ : W.γ e = γ) :
    Window.rawMass W (maskedWitnessEvents W Good) e =
      ((selected p k γ).restrict (Good γ)) (W.F e) := by
  change priorMass p k (W.γ e) (W.F e ∩ Good (W.γ e)) = _
  rw [hγ, Measure.restrict_apply hc.measF, selected,
    Measure.restrict_eq_self _ ((inter_subset_left).trans (by
      intro z hz
      simpa only [← hγ] using (hc.sel hz).1))]

/-- The tube estimate charges full analytically masked earlier masses, while
all geometry and lists continue to refer to the original formatted atlas. -/
theorem masked_witness_window_mass_le {p : Data} {k M D : ℕ} (W : Atlas p k)
    {κ r : ℝ} (hc : ∀ e, Window.WChart p k W M D κ r e)
    (Good : Fin (p.W k) → Set Point)
    (γ : Fin (p.W k)) (I : Finset (Fin W.C))
    (hworld : ∀ e ∈ I, W.γ e = γ)
    (hknown : ∀ e z, z ∈ W.F e →
      e ∈ W.lst (W.γ e) (obs (p.B k (W.γ e)) (δ (p.N k) p.L) z))
    (Klist : ℝ) (hcard : ∀ o, ((W.lst γ o).card : ℝ) ≤ Klist)
    (Cbase : ENNReal)
    (hcap : Measure.map Window.basePt ((selected p k γ).restrict (Good γ)) ≤ Cbase • volume)
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
    (∑ e ∈ I, Window.rawMass W (maskedWitnessEvents W Good) e) ≤
      ENNReal.ofReal Klist * Cbase * ENNReal.ofReal (8 * Real.pi * rt * ry * rn) := by
  have hm := witness_window_mass_le W hc γ I hworld hknown Klist hcard
    ((selected p k γ).restrict (Good γ)) Cbase hcap hn hangle hU hV hanchor
    htbudget hybudget hnbudget hry hrn
  apply le_trans (le_of_eq ?_) hm
  exact Finset.sum_congr rfl fun e he => masked_witness_mass_eq (hc e) Good (hworld e he)

end
end Submission.Obl.k4_raw_localized_native_systems.Packing
