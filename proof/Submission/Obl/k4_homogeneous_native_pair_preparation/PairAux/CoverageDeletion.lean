-- Adapted from this LOT tree, o206, session x0709, commit 18669b18,
-- Submission/Obl/k4_coarse_pair_frame_preparation/CoverageDeletion.lean.
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux.JensenCoverage
import Submission.Obl.k4_homogeneous_native_pair_preparation.PairMeasure
import Submission.Obl.k4_quadratic_atlas_normalization.MassSelection

/-! Coverage after original-law analytic masks. -/

namespace Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

/-- Jensen coverage survives one-time exceptional sets and an additional
source-specific pair deletion budget. No conditioning of the pair laws occurs. -/
theorem source_pair_coverage_of_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (W T : ℕ) (ν : Fin W → Measure X) [∀ w, IsProbabilityMeasure (ν w)]
    (ω : Fin W → ℝ) (hω : ∀ w, 0 ≤ ω w) (hωsum : ∑ w, ω w = 1)
    (γ : ι → Fin W) (j : ι → Fin (2 ^ T))
    (S : ι → Set (X × ℝ)) (hS : ∀ s, MeasurableSet (S s))
    (hdisj : ∀ s s', s ≠ s' → γ s = γ s' → j s = j s' → Disjoint (S s) (S s'))
    (hblock : ∀ s p, p ∈ S s → p.2 ∈ I T (j s))
    (Sel : Fin W → Set (X × ℝ)) (hSel : ∀ w, MeasurableSet (Sel w))
    (hSSel : ∀ s, S s ⊆ Sel (γ s))
    (Q : Fin W → Set (X × ℝ)) (hQ : ∀ w, MeasurableSet (Q w))
    (Ret Del : ι → Set (X × (ℝ × ℝ))) {m e d κ : ℝ}
    (hm : 0 < m) (he : 0 ≤ e) (hd : 0 ≤ d) (hκ : 0 < κ)
    (hmass : ENNReal.ofReal m ≤ ∑ s, ENNReal.ofReal (ω (γ s)) *
      ((ν (γ s)).prod volume) (S s))
    (hcover : ∀ s, rawSourcePairs (S s) (I T (j s)) (Sel (γ s)) ⊆
      Ret s ∪ (rawSourcePairs (S s) (I T (j s)) (Sel (γ s)) ∩
        ({p | (p.1, p.2.1) ∈ Q (γ s) ∨ (p.1, p.2.2) ∈ Q (γ s)} ∪ Del s)))
    (hQmass : (∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (Q w)) ≤ ENNReal.ofReal e)
    (hDelmass : (∑ s, ENNReal.ofReal (ω (γ s) * (2 : ℝ) ^ T) *
      ((ν (γ s)).prod (volume.prod volume))
        (rawSourcePairs (S s) (I T (j s)) (Sel (γ s)) ∩ Del s)) ≤ ENNReal.ofReal d)
    (hbudget : 2 * e + d ≤ m ^ 2 / 2) (hκmass : 8 ≤ κ * m ^ 2) :
    ENNReal.ofReal (4 * κ⁻¹) ≤ ∑ s, ENNReal.ofReal (ω (γ s) * (2 : ℝ) ^ T) *
      ((ν (γ s)).prod (volume.prod volume)) (Ret s) := by
  let R (s : ι) := rawSourcePairs (S s) (I T (j s)) (Sel (γ s))
  let μ (s : ι) : Measure (X × (ℝ × ℝ)) := (ν (γ s)).prod (volume.prod volume)
  let a (s : ι) := ENNReal.ofReal (ω (γ s) * (2 : ℝ) ^ T)
  let B (s : ι) : Set (X × (ℝ × ℝ)) :=
    {p | (p.1, p.2.1) ∈ Q (γ s) ∨ (p.1, p.2.2) ∈ Q (γ s)}
  have hfreq : ENNReal.ofReal ((2 : ℝ) ^ T) = (2 ^ T : ℕ) := by
    norm_cast
  have ha (s : ι) : a s = ENNReal.ofReal (ω (γ s)) * (2 ^ T : ℕ) := by
    dsimp [a]
    rw [ENNReal.ofReal_mul' (by positivity), hfreq]
  have hωE : (∑ w, ENNReal.ofReal (ω w)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hω w), hωsum]
    norm_num
  have hlower : ENNReal.ofReal (m ^ 2) ≤ ∑ s, a s * μ s (R s) := by
    have h := source_indexed_pair_lower W T ν (fun w => ENNReal.ofReal (ω w)) hωE
      γ j S hS hdisj hblock Sel hSel hSSel ENNReal.ofReal_ne_top hmass
    simpa only [ENNReal.ofReal_pow hm.le, ha, μ, R] using h
  have hR (s : ι) : MeasurableSet (R s) :=
    measurableSet_rawSourcePairs (hS s)
      (Submission.Obl.k4_scalar_angular_pair_agreement.measurableSet_I _ _) (hSel (γ s))
  have htail : (∑ s, a s * μ s (R s ∩ B s)) ≤ 2 * ENNReal.ofReal e := by
    have h := source_indexed_pair_exception_le W T ν (fun _ => inferInstance) ω γ j S hdisj
      R hR (fun _ _ hp => hp.1)
      (fun s p hp => ⟨hblock s (p.1, p.2.1) hp.1, hp.2.1⟩) Q hQ
    exact h.trans (mul_le_mul' le_rfl hQmass)
  have hdeleted : (∑ s, a s * μ s (R s ∩ (B s ∪ Del s))) ≤
      ENNReal.ofReal (m ^ 2 / 2) := by
    calc
      _ ≤ ∑ s, a s * (μ s (R s ∩ B s) + μ s (R s ∩ Del s)) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul' le_rfl
        rw [inter_union_distrib_left]
        exact measure_union_le _ _
      _ = (∑ s, a s * μ s (R s ∩ B s)) + ∑ s, a s * μ s (R s ∩ Del s) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
      _ ≤ 2 * ENNReal.ofReal e + ENNReal.ofReal d := add_le_add htail hDelmass
      _ = ENNReal.ofReal (2 * e + d) := by
        rw [ENNReal.ofReal_add (by positivity) hd, ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbudget
  have hretained := Submission.Obl.k4_quadratic_atlas_normalization.retain_half_mass
    (∑ s, a s * μ s (R s)) (∑ s, a s * μ s (Ret s))
    (∑ s, a s * μ s (R s ∩ (B s ∪ Del s))) (m ^ 2) (sq_nonneg m) hlower
    (Submission.Obl.k4_quadratic_atlas_normalization.weighted_mass_le_retained_add_deleted
      μ a R Ret (fun s => R s ∩ (B s ∪ Del s)) hcover) hdeleted
  have hnum : 4 * κ⁻¹ ≤ m ^ 2 / 2 := by
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hκ).mpr
    nlinarith [hκmass]
  exact (ENNReal.ofReal_le_ofReal hnum).trans hretained

end Submission.Obl.k4_homogeneous_native_pair_preparation.PairAux
