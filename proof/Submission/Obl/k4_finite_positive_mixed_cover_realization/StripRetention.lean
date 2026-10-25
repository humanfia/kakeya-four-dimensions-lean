import Submission.Obl.k4_finite_positive_mixed_cover_realization.ActualAlignmentMass
import Submission.Obl.k4_fixed_menu_density_pruning.CandidatePruning

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Finset Submission.Lib.K4XInterface

section
variable {W m Mp Dp Mg Dg : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε gap : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hc

lemma CoverData.Valid.interiors_disjoint (a b : Fin c.n) (hne : a ≠ b)
    (hw : p.world (c.old a) = p.world (c.old b)) :
    Disjoint (c.interior a) (c.interior b) :=
  (hc.2.2.2.2.2.2.2.2.2.1 a b hne hw).mono inter_subset_left inter_subset_left

include hp

lemma CoverData.Valid.interior_subset_world (a : Fin c.n) :
    c.interior a ⊆ E (p.world (c.old a)) := by
  intro z hz
  exact (hp.counted_support (c.old a) z (hc.interior_subset_old hp a hz)).1

lemma CoverData.Valid.restricted_interior_mass (a : Fin c.n) :
    (((ν (p.world (c.old a))).prod volume).restrict (E (p.world (c.old a))))
        (c.interior a) = ((ν (p.world (c.old a))).prod volume) (c.counted a) := by
  rw [Measure.restrict_apply (hc.interior_measurable a),
    inter_eq_left.mpr (hc.interior_subset_world hp a), hc.interior_mass a]

lemma CoverData.Valid.restricted_aligned_mass (normal : Fin p.C → Plane)
    (bias : Fin p.C → ℝ) (j : ℕ) (a : Fin c.n) :
    (((ν (p.world (c.old a))).prod volume).restrict (E (p.world (c.old a))))
        (c.alignedWitness normal bias gap j a) =
      ((ν (p.world (c.old a))).prod volume) (c.alignedWitness normal bias gap j a) := by
  apply Measure.restrict_eq_self
  exact fun z hz => hc.interior_subset_world hp a hz.1

/-- The original mass splits into aligned mass, original world exceptions,
and a sum of good actual-pair charges. Exceptions are paid just once. -/
theorem CoverData.Valid.alignment_mass_ledger
    (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)
    {j : ℕ} (hij : c.level ≤ j) (hjm : j < m)
    (μ : Fin W → Measure Incidence) (weight : Fin W → ENNReal)
    (Good : Fin W → Set Incidence) :
    (∑ a : Fin c.n, weight (p.world (c.old a)) * μ (p.world (c.old a)) (c.interior a)) ≤
      (∑ a : Fin c.n, weight (p.world (c.old a)) * μ (p.world (c.old a))
        (c.alignedWitness normal bias gap j a)) +
      (∑ w : Fin W, weight w * μ w (Good w)ᶜ) +
      ∑ w : Fin W, weight w * ∑ bd : Fin c.n × Fin p.C,
        μ w (c.misalignedPair normal bias gap j w bd ∩ Good w) := by
  classical
  let γ : Fin c.n → Fin W := fun a => p.world (c.old a)
  let U : Fin c.n → Set Incidence := fun a =>
    (c.interior a \ c.alignedWitness normal bias gap j a) ∩ Good (γ a)
  have hgood : (∑ a, weight (γ a) * μ (γ a) (U a)) ≤
      ∑ w : Fin W, weight w * ∑ bd : Fin c.n × Fin p.C,
        μ w (c.misalignedPair normal bias gap j w bd ∩ Good w) := by
    rw [← sum_fiberwise univ γ]
    apply sum_le_sum
    intro w _
    calc
      _ = weight w * ∑ a : Fin c.n,
          μ w {z | (γ a = w ∧ z ∈ c.interior a ∧
            z ∉ c.alignedWitness normal bias gap j a) ∧ z ∈ Good w} := by
        rw [mul_sum]
        simp only [sum_filter]
        apply sum_congr rfl
        intro a _
        by_cases ha : γ a = w
        · simp only [ha, ↓reduceIte, true_and]
          congr 2
          ext z
          simp only [U, mem_inter_iff, mem_diff, mem_setOf_eq, ha]
        · simp [ha]
      _ ≤ _ := mul_le_mul' le_rfl (hc.unaligned_mass_le_pairs hp normal bias hij hjm (μ w) (Good w) w)
  have hbad := k4_fixed_menu_density_pruning.weighted_candidate_exception_le
    μ weight γ c.interior (fun w => (Good w)ᶜ) hc.interior_measurable hc.interiors_disjoint
  calc
    _ ≤ (∑ a, weight (γ a) * μ (γ a) (c.alignedWitness normal bias gap j a)) +
        ∑ a, weight (γ a) * μ (γ a) ((c.interior a ∩ (Good (γ a))ᶜ) ∪ U a) := by
      apply k4_quadratic_atlas_normalization.weighted_mass_le_retained_add_deleted
      intro a z hz
      by_cases hal : z ∈ c.alignedWitness normal bias gap j a
      · exact Or.inl hal
      · by_cases hg : z ∈ Good (γ a)
        · exact Or.inr (Or.inr ⟨⟨hz, hal⟩, hg⟩)
        · exact Or.inr (Or.inl ⟨hz, hg⟩)
    _ ≤ (∑ a, weight (γ a) * μ (γ a) (c.alignedWitness normal bias gap j a)) +
        ((∑ a, weight (γ a) * μ (γ a) (c.interior a ∩ (Good (γ a))ᶜ)) +
          ∑ a, weight (γ a) * μ (γ a) (U a)) := by
      gcongr
      calc
        _ ≤ ∑ a, weight (γ a) *
            (μ (γ a) (c.interior a ∩ (Good (γ a))ᶜ) + μ (γ a) (U a)) := by
          apply sum_le_sum
          intro a _
          exact mul_le_mul' le_rfl (measure_union_le _ _)
        _ = _ := by simp only [mul_add, sum_add_distrib]
    _ ≤ _ := by
      simpa only [add_assoc] using add_le_add
        (le_rfl : (∑ a, weight (γ a) * μ (γ a)
          (c.alignedWitness normal bias gap j a)) ≤ _) (add_le_add hbad hgood)

/-- A direct useful form of the mass ledger under the unchanged original law. -/
theorem CoverData.Valid.aligned_mass_floor
    (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ)
    {j : ℕ} (hij : c.level ≤ j) (hjm : j < m)
    (Good : Fin W → Set Incidence) (hNk : 0 ≤ Nk) {bad angular : ℝ}
    (hbad : (∑ w : Fin W, ENNReal.ofReal (ω w) *
      (((ν w).prod volume).restrict (E w)) (Good w)ᶜ) ≤ ENNReal.ofReal bad)
    (hangular : (∑ w : Fin W, ENNReal.ofReal (ω w) *
      ∑ bd : Fin c.n × Fin p.C, (((ν w).prod volume).restrict (E w))
        (c.misalignedPair normal bias gap j w bd ∩ Good w)) ≤ ENNReal.ofReal angular)
    (hbad0 : 0 ≤ bad) (hangular0 : 0 ≤ angular)
    (hsmall : bad + angular ≤ Nk ^ (-ε) / 2) :
    ENNReal.ofReal (Nk ^ (-ε) / 2) ≤ ∑ a : Fin c.n,
      ENNReal.ofReal (ω (p.world (c.old a))) * ((ν (p.world (c.old a))).prod volume)
        (c.alignedWitness normal bias gap j a) := by
  have hledger := hc.alignment_mass_ledger (gap := gap) hp normal bias hij hjm
    (fun w => ((ν w).prod volume).restrict (E w)) (fun w => ENNReal.ofReal (ω w)) Good
  simp_rw [hc.restricted_interior_mass hp, hc.restricted_aligned_mass hp] at hledger
  apply k4_quadratic_atlas_normalization.retain_half_mass
    _ _ _ (Nk ^ (-ε)) (Real.rpow_nonneg hNk _)
    hc.2.2.2.2.2.2.2.2.2.2
  · simpa only [add_assoc] using hledger
  · exact (add_le_add hbad hangular).trans
      ((ENNReal.ofReal_add hbad0 hangular0).symm.le.trans (ENNReal.ofReal_le_ofReal hsmall))

end

end Submission.Obl.k4_finite_positive_mixed_cover_realization
