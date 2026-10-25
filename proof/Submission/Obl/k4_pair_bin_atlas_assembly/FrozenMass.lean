import Submission.Obl.k4_pair_bin_atlas_assembly.FrozenPairs
import Submission.Obl.k4_pair_bin_atlas_assembly.MergedMass
import Submission.Obl.k4_pair_bin_atlas_assembly.Retention

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory
open scoped ENNReal

namespace PairData.FrozenPairs

variable {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε : ℝ}
    {p : PairData Nk Wk ωk νk Ek Bk L a h M D ε}
    {Cs : ℕ} {k : BinKernel Cs} {CD : ℝ}
    {eligible : AnchorParameter → Fin p.J → (Fin k.d → ℤ) → Set Trajectory}
    (f : p.FrozenPairs k CD eligible)

theorem merged_mass_le {C : ℕ} (tag : Fin p.m → Fin C) (γ : Fin C → Fin Wk)
    (j : Fin C → Fin (2 ^ p.T)) (F : Fin C → Set Incidence)
    (hworld : ∀ s, γ (tag s) = p.world s)
    (htime : ∀ s, j (tag s) = p.timeIndex s)
    (hsub : ∀ s, f.F s ⊆ F (tag s)) :
    (∑ s, ENNReal.ofReal (ωk (p.world s)) * p.incidenceLaw s (f.F s)) ≤
      ∑ b, ENNReal.ofReal (ωk (γ b)) * ((νk (γ b)).prod volume) (F b) := by
  have hdisj (s s' : Fin p.m) (hne : s ≠ s') (htag : tag s = tag s') :
      Disjoint (f.F s) (f.F s') := by
    apply f.F_disjoint s s' hne
    · rw [← hworld s, ← hworld s', htag]
    · rw [← htime s, ← htime s', htag]
  have hm := weighted_merged_mass_le (fun b => (νk (γ b)).prod volume)
    (fun b => ENNReal.ofReal (ωk (γ b))) tag f.F F f.F_measurable hdisj hsub
  simpa only [hworld, PairData.incidenceLaw] using hm

theorem mass_merged {C : ℕ} (tag : Fin p.m → Fin C) (γ : Fin C → Fin Wk)
    (j : Fin C → Fin (2 ^ p.T)) (F : Fin C → Set Incidence)
    (hworld : ∀ s, γ (tag s) = p.world s)
    (htime : ∀ s, j (tag s) = p.timeIndex s)
    (hsub : ∀ s, f.F s ⊆ F (tag s)) :
    p.pairMass p.H ≤
      2 * (∑ b, ENNReal.ofReal (ωk (γ b)) * ((νk (γ b)).prod volume) (F b)) +
        ENNReal.ofReal (2 * Nk ^ (-(2 * a))) +
        ENNReal.ofReal (p.κ * (Nk ^ a)⁻¹) * p.pairMass p.H := by
  apply f.mass.trans
  gcongr
  exact f.merged_mass_le tag γ j F hworld htime hsub

/-- A fixed fraction of the original reciprocal-slack mass survives all
selection steps. -/
theorem mass_floor (hν : ∀ w, IsProbabilityMeasure (νk w))
    (hNk : 0 < Nk) (hA : 2 ≤ Nk ^ a)
    (hrel : p.κ * (Nk ^ a)⁻¹ ≤ 1 / 4) :
    ENNReal.ofReal (4 * p.κ)⁻¹ ≤
      ∑ s, ENNReal.ofReal (ωk (p.world s)) * p.incidenceLaw s (f.F s) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one p.κ_one
  exact retained_mass_floor hκ (p.pairMass_finite hν) p.mass_floor f.mass
    (ENNReal.ofReal_le_ofReal hrel)
    (ENNReal.ofReal_le_ofReal (power_absolute_error_le hNk hκ hA hrel))

theorem mass_floor_enlarged (hν : ∀ w, IsProbabilityMeasure (νk w))
    (hNk : 0 < Nk) (hA : 2 ≤ Nk ^ a)
    (hrel : p.κ * (Nk ^ a)⁻¹ ≤ 1 / 4) {K : ℝ} (hK : 4 ≤ K) :
    ENNReal.ofReal (K * p.κ)⁻¹ ≤
      ∑ s, ENNReal.ofReal (ωk (p.world s)) * p.incidenceLaw s (f.F s) := by
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) (f.mass_floor hν hNk hA hrel)
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one p.κ_one
  simpa only [one_div] using one_div_le_one_div_of_le
    (by positivity : 0 < 4 * p.κ) (mul_le_mul_of_nonneg_right hK hκ.le)

end PairData.FrozenPairs
end Submission.Obl.k4_pair_bin_atlas_assembly
