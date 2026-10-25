import Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog.DensityLaw
import Submission.Obl.k4_remainder_pure_profile_normalization.ComposedDepth

namespace Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
open MeasureTheory Filter Set
open scoped Topology ENNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles

theorem depthSum_eq_composedDepth (n r s : ℝ) :
    depthSum n r s = composedDepth n r s := by
  unfold depthSum composedDepth
  push_cast
  simp only [div_div_eq_mul_div]

theorem depthSum_tendsto {N : ℕ → ℝ} (hN : ∀ k, 1 < N k)
    (ht : Tendsto N atTop atTop) (r s : ℝ) :
    Tendsto (fun k => depthSum (N k) r s) atTop (𝓝 (r + s)) := by
  simpa only [depthSum_eq_composedDepth] using composedDepth_tendsto hN ht r s

/-- Removing a common fixed power from the density adds that power to its exponent. -/
theorem density_scale_window {n : ℝ} (hn : 0 < n) (m : ℕ) (e t : ℝ) :
    ENNReal.ofReal (n ^ m) * ENNReal.ofReal (n ^ (-(e + m) + t)) =
      ENNReal.ofReal (n ^ (-e + t)) := by
  rw [← ENNReal.ofReal_mul (pow_nonneg hn.le _), ← Real.rpow_natCast n m,
    ← Real.rpow_add hn]
  congr 2
  ring

/-- The encoded and decoded exceptional masses agree with the exponent shifted
by the common planar density factor. -/
theorem decoded_typical {S : ℕ → Sample} {D m : ℕ}
    (hS : ∀ k, (S k).Hyp)
    (hT : ∀ k, Tempered (S k).N (S k).K (S k).M D (S k).W
      (S k).ω (S k).ν (S k).E (S k).B)
    (hm : ∀ k, (S k).mL = m)
    (E : ℕ → Set Incidence) (hE : ∀ k, MeasurableSet (E k))
    (hsub : ∀ k, E k ⊆ (S k).event) (s e : ℝ)
    (g : (k : ℕ) → Fin (S k).W → Observation → ENNReal)
    (hg : ∀ k b, Measurable (g k b))
    (htyp : HasTypicalDensity (fun k => (S k).N)
      (fun k => ((S k).prior.prod volume).restrict (E k))
      (fun k z => (S k).encDensity (g k)
        (jointObs (S k).N (depthSum (S k).N (S k).s0 s) 0 z)) e) :
    ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ b, ENNReal.ofReal ((S k).ω b) * ((S k).decLaw (E k) b)
        {z | g k b (obs ((S k).B b) (δ (S k).N s) z) <
            ENNReal.ofReal ((S k).N ^ (-(e + m) - τ)) ∨
          ENNReal.ofReal ((S k).N ^ (-(e + m) + τ)) <
            g k b (obs ((S k).B b) (δ (S k).N s) z)}) ≤
        ENNReal.ofReal ((S k).N ^ (-c)) := by
  intro τ hτ
  obtain ⟨c,hc,hb⟩ := htyp τ hτ
  refine ⟨c,hc,hb.mono fun k hk => ?_⟩
  rw [(hS k).bad_mass (hT k) (hE k) (hsub k) s (hg k)]
  have he (t : ℝ) : ENNReal.ofReal (S k).Lam *
      ENNReal.ofReal ((S k).N ^ (-(e + m) + t)) =
        ENNReal.ofReal ((S k).N ^ (-e + t)) := by
    rw [Sample.Lam, hm k]
    exact density_scale_window (hS k).N_pos m e t
  simp only [show -(e + (m : ℝ)) - τ = -(e + (m : ℝ)) + -τ by ring,
    he, show -e + -τ = -e - τ by ring]
  exact hk

end Submission.Obl.k4_remainder_pure_profile_normalization.MultiHomog
