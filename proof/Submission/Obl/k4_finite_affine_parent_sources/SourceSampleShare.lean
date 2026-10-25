import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildShare

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Submission.Lib.K4AngularCharge

noncomputable section

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- One original share mask simultaneously prepares every possible band parent,
while preserving half of the heavy terminal residual. -/
theorem sample_share_masked
    [∀ w, IsFiniteMeasure (((ν w).prod volume).restrict (E w))]
    (hν : ∀ w, IsProbabilityMeasure (ν w))
    (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1) (hNk : 1 ≤ Nk)
    (hL : 0 ≤ L) (hδ : δ₀ ≤ 1 / 64)
    (A : ℝ) (hA : 0 < A) (hcost : 16 * (m : ℝ) * p.κ ^ 3 ≤ A)
    (H : Fin W → Set Incidence)
    (hH : ∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc W p.C m p.lev p.world p.counted w)
    (hmass : ENNReal.ofReal (1 / (4 * p.κ ^ 2)) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H w)) :
    ∃ S0 : Fin W → Set Incidence, (∀ w, MeasurableSet (S0 w) ∧ S0 w ⊆ H w) ∧
      ENNReal.ofReal (1 / (8 * p.κ ^ 2)) ≤
        ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (S0 w) ∧
      ∀ w, ∀ z ∈ S0 w, ∀ b : Fin p.C, p.world b = w → sg (p.lev b) ≤ 1 / 4 →
        z ∈ p.counted b →
        ENNReal.ofReal A⁻¹ ≤ labelShare (((ν w).prod volume).restrict (E w))
          (obs (B w) (δ Nk L)) (p.counted b) z := by
  classical
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  have hκ : 1 ≤ p.κ := hp.one_le_slack
  have hκ0 : 0 < p.κ := by linarith
  let levels := (Finset.range m).filter (fun i => sg i ≤ 1 / 4)
  have hlev : ∀ i ∈ levels, 0 ≤ p.r i ∧ p.r i ≤ L := by
    intro i hi
    obtain ⟨him, hsi⟩ := Finset.mem_filter.mp hi
    have hi' : i < m := Finset.mem_range.mp him
    have hr := hp.level_bounds i hi'
    have hδL := mul_le_mul_of_nonneg_right hδ hL
    have hsiL := mul_le_mul_of_nonneg_right hsi hL
    exact ⟨hr.2.1.le, by linarith [(abs_le.mp hr.1).2]⟩
  have hcard : (levels.card : ℝ) ≤ m := by
    exact_mod_cast (show levels.card ≤ m from
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _))
  have hceil : (⌈p.κ⌉₊ : ℝ) ≤ 2 * p.κ := by
    have hc := Nat.ceil_lt_add_one hκ0.le
    linarith
  have hloss : (levels.card : ℝ) * (⌈p.κ⌉₊ : ℝ) * A⁻¹ ≤ (1 / (4 * p.κ ^ 2)) / 2 := by
    calc (levels.card : ℝ) * (⌈p.κ⌉₊ : ℝ) * A⁻¹ ≤ (m : ℝ) * (2 * p.κ) * A⁻¹ := by gcongr
      _ = (2 * (m : ℝ) * p.κ) / A := by ring
      _ ≤ 1 / (8 * p.κ ^ 2) := by
        rw [div_le_div_iff₀ hA (by positivity)]
        nlinarith [hcost]
      _ = _ := by ring
  obtain ⟨S0, hS0, hmass0, hshare⟩ := share_masked hp hω0 hω1 hE hNk levels hlev A⁻¹
    (by positivity) H hH (by positivity : 0 ≤ 1 / (4 * p.κ ^ 2)) hmass hloss
  refine ⟨S0, hS0, ?_, ?_⟩
  · convert hmass0 using 1 <;> congr 1 <;> ring
  · intro w z hz b hbw hband hzb
    apply hshare w z hz b hbw
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hp.label_level b), hband⟩
    · exact hzb

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
