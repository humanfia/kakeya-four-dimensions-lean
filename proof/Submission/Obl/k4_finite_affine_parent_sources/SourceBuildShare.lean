-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0812 f7bed5fb, x0891 a669339c, x0923 e8a77b3e, x0807 989bea46 (SourceParentPalette: x0812's version); namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.PathPaletteMasks
import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildNumerators

/-!
# The share mask of the selection residual

Before the window chooses its parent, the residual keeps only the incidences whose labels at
every band level retain the conditional share `θ` of their original observation cell (x0807's
`parentShareMask`). This costs at most `#levels ⌈κ⌉ θ` of the weighted original mass
(`share_masked`).

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4AngularCharge
open scoped ENNReal

noncomputable section

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **The share-masked residual.** -/
theorem share_masked [∀ w, IsProbabilityMeasure (ν w)]
    [hfin : ∀ w, IsFiniteMeasure (((ν w).prod volume).restrict (E w))]
    (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1) (hNk : 1 ≤ Nk)
    (levels : Finset ℕ) (hlev : ∀ i ∈ levels, 0 ≤ p.r i ∧ p.r i ≤ L) (θ : ℝ) (hθ : 0 ≤ θ)
    (H : Fin W → Set Incidence)
    (hH : ∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc W p.C m p.lev p.world p.counted w)
    {Z : ℝ} (hZ : 0 ≤ Z)
    (hmass : ENNReal.ofReal Z ≤ ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w))
    (hloss : (levels.card : ℝ) * (⌈p.κ⌉₊ : ℝ) * θ ≤ Z / 2) :
    ∃ S0 : Fin W → Set Incidence, (∀ w, MeasurableSet (S0 w) ∧ S0 w ⊆ H w) ∧
      ENNReal.ofReal (Z / 2) ≤ ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (S0 w) ∧
      ∀ w, ∀ z ∈ S0 w, ∀ b : Fin p.C, p.world b = w → p.lev b ∈ levels → z ∈ p.counted b →
        ENNReal.ofReal θ ≤ labelShare (((ν w).prod volume).restrict (E w))
          (obs (B w) (δ Nk L)) (p.counted b) z := by
  set μ : Fin W → Measure Incidence := fun w => ((ν w).prod volume).restrict (E w) with hμ
  set mask := fun w => p.parentShareMask μ Nk L B levels (ENNReal.ofReal θ) w with hmask
  have hmaskm : ∀ w, MeasurableSet (mask w) := fun w =>
    hp.measurableSet_parentShareMask μ levels (ENNReal.ofReal θ) w
  refine ⟨fun w => H w ∩ mask w, fun w => ⟨(hH w).1.inter (hmaskm w), inter_subset_left⟩,
    ?_, ?_⟩
  · -- the mass
    have hKc : p.κ ≤ (⌈p.κ⌉₊ : ℝ) := Nat.le_ceil _
    have hloss' := hp.parentShareMask_weighted_loss μ hNk levels hlev ⌈p.κ⌉₊ hKc
      (ENNReal.ofReal θ)
    have huniv : (∑ w, ENNReal.ofReal (ω w) * μ w univ) ≤ 1 := by
      have h := WorldPath.original_mass_le_one ν ω hω0 hω1 E hE
      rw [WorldPath.original_mass] at h
      refine le_trans (le_of_eq ?_) h
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hμ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    have hlossE : (∑ w, ENNReal.ofReal (ω w) * μ w (mask w)ᶜ) ≤ ENNReal.ofReal (Z / 2) := by
      refine hloss'.trans ?_
      calc ((levels.card : ENNReal) * (⌈p.κ⌉₊ : ENNReal) * ENNReal.ofReal θ) *
            ∑ w, ENNReal.ofReal (ω w) * μ w univ
          ≤ ((levels.card : ENNReal) * (⌈p.κ⌉₊ : ENNReal) * ENNReal.ofReal θ) * 1 := by
            gcongr
        _ = ENNReal.ofReal ((levels.card : ℝ) * (⌈p.κ⌉₊ : ℝ) * θ) := by
            rw [mul_one, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (Z / 2) := ENNReal.ofReal_le_ofReal hloss
    have hsplit : ∀ w, ((ν w).prod volume) (H w) ≤
        ((ν w).prod volume) (H w ∩ mask w) + μ w (mask w)ᶜ := by
      intro w
      have hHE : H w ⊆ E w := fun z hz => by
        obtain ⟨b, -, hb, hzb⟩ := (hH w).2 hz
        rw [← hb]
        exact (hp.counted_support b z hzb).1
      calc ((ν w).prod volume) (H w)
          ≤ ((ν w).prod volume) (H w ∩ mask w) + ((ν w).prod volume) (H w \ mask w) :=
            measure_le_inter_add_diff _ _ _
        _ ≤ ((ν w).prod volume) (H w ∩ mask w) + μ w (mask w)ᶜ := by
            refine add_le_add le_rfl ?_
            rw [hμ, Measure.restrict_apply (hmaskm w).compl]
            exact measure_mono fun z hz => ⟨hz.2, hHE hz.1⟩
    have htot : ENNReal.ofReal Z ≤ (∑ w, ENNReal.ofReal (ω w) *
        ((ν w).prod volume) (H w ∩ mask w)) + ENNReal.ofReal (Z / 2) := by
      calc ENNReal.ofReal Z ≤ ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w) := hmass
        _ ≤ ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume) (H w ∩ mask w) +
              μ w (mask w)ᶜ) := Finset.sum_le_sum fun w _ => by gcongr; exact hsplit w
        _ = (∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w ∩ mask w)) +
              ∑ w, ENNReal.ofReal (ω w) * μ w (mask w)ᶜ := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun w _ => by ring
        _ ≤ _ := by gcongr
    have hZ2 : ENNReal.ofReal Z = ENNReal.ofReal (Z / 2) + ENNReal.ofReal (Z / 2) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rw [hZ2] at htot
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp htot
  · -- the shares
    intro w z hz b hbw hblev hzb
    have hzm := mem_iInter.mp hz.2 ⟨p.lev b, hblev⟩
    exact PaletteMasks.share_of_mem (μ w) (obs (B w) (δ Nk L))
      (fun b' : {b' : Fin p.C // p.lev b' = p.lev b ∧ p.world b' = w} => p.counted b'.val)
      (ENNReal.ofReal θ) hzm ⟨b, rfl, hbw⟩ hzb

end

end

end Submission.Obl.k4_finite_affine_parent_sources
