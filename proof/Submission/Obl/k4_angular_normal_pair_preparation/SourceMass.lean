-- The original weighted-law argument follows this LOT tree, o114, session x0707,
-- commit c63b850d, Preparation/AngularCharge.lean; packet disjointness is imported from o170.
import Submission.Obl.k4_angular_normal_pair_preparation.Pruning
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

namespace Submission.Obl.k4_angular_normal_pair_preparation

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace NativeSample

variable {aligned : Prop} {lam Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ))}
    {Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Pk : Fin Wk → MvPolynomial (Fin 4) ℝ} {Bk : Fin Wk → ℝ} {f : ℝ → ℝ}
    {gk : Fin Wk → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal}
    {Gk : Fin Wk → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal}
    {L S a e u h : ℝ} {M D : ℕ} {depths : Finset ℝ} {ε : ℝ}

variable (q : NativeSample aligned lam Nk Wk ωk νk Ek Pk Bk f gk Gk L S a e u h M D depths ε)

/-- Half-open fine blocks make the old incidences disjoint within each world. -/
theorem source_disjoint (b b' : Fin q.C) (hne : b ≠ b') (hw : q.γ b = q.γ b') :
    Disjoint (q.F b) (q.F b') := by
  let I := {i : Fin q.C // q.γ i = q.γ b}
  have hd := Submission.Obl.k4_quadratic_finite_greedy_cover.halfOpen_packets_disjoint
    (fun i : I => q.A i.val) (fun i : I => (q.j i.val : ℕ)) ((2 : ℝ) ^ (q.T + q.s))
    (by positivity)
    (fun i i' hii' hj => q.disj i.val i'.val (fun h => hii' (Subtype.ext h))
      (i.property.trans i'.property.symm) (Fin.ext hj))
  have hd' := hd (show (⟨b, rfl⟩ : I) ≠ ⟨b', hw.symm⟩ from
    fun h => hne (congrArg Subtype.val h))
  apply hd'.mono
  · intro p hp
    have hc := ((q.charts b).2.2.2.2.2.2.2.2.2.2.1 p hp)
    exact ⟨hc.2.1, hc.2.2.1.1, q.halfopen b p hp⟩
  · intro p hp
    have hc := ((q.charts b').2.2.2.2.2.2.2.2.2.2.1 p hp)
    exact ⟨hc.2.1, hc.2.2.1.1, q.halfopen b' p hp⟩

/-- The true source floors spend at most one unit of the unchanged original weighted law. -/
theorem source_mass_budget [∀ γ₀, IsProbabilityMeasure (νk γ₀)]
    (hω : ∀ γ₀, 0 ≤ ωk γ₀) (hωsum : ∑ γ₀, ωk γ₀ = 1)
    (hE : ∀ γ₀, Ek γ₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (∑ b, ENNReal.ofReal (ωk (q.γ b)) * ((νk (q.γ b)).prod volume) (q.F b)) ≤ 1 := by
  classical
  have hFm : ∀ b, MeasurableSet (q.F b) := fun b =>
    (q.charts b).2.2.2.2.2.2.2.1
  have hFE : ∀ b, q.F b ⊆ Ek (q.γ b) := fun b p hp =>
    ((q.charts b).2.2.2.2.2.2.2.2.2.2.1 p hp).1
  have heq := Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
    (fun γ₀ => (νk γ₀).prod volume) (fun γ₀ => ENNReal.ofReal (ωk γ₀)) (fun _ => True)
    q.γ q.F (fun b _ => hFm b) (fun b b' _ _ hne hw => q.source_disjoint b b' hne hw)
  have hsum : (∑ b, ENNReal.ofReal (ωk (q.γ b)) * ((νk (q.γ b)).prod volume) (q.F b)) =
      ∑ γ₀, ENNReal.ofReal (ωk γ₀) * ((νk γ₀).prod volume)
        {p | ∃ b, q.γ b = γ₀ ∧ p ∈ q.F b} := by
    simpa only [true_and, ite_true] using heq.symm
  rw [hsum]
  calc
    _ ≤ ∑ γ₀, ENNReal.ofReal (ωk γ₀) := by
      apply Finset.sum_le_sum
      intro γ₀ _
      have hm : ((νk γ₀).prod volume) {p | ∃ b, q.γ b = γ₀ ∧ p ∈ q.F b} ≤ 1 := by
        calc
          _ ≤ ((νk γ₀).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := by
            apply measure_mono
            rintro p ⟨b, hb, hp⟩
            exact hE _ (hFE b hp)
          _ = 1 := by simp [Measure.prod_prod]
      simpa only [mul_one] using mul_le_mul' le_rfl hm
    _ = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun γ₀ _ => hω γ₀), hωsum]
      simp

end NativeSample
end Submission.Obl.k4_angular_normal_pair_preparation
