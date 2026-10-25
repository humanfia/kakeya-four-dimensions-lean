import Submission.Obl.k4_fixed_budget_quadratic_recovery.Coefficients

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set

/-- Convert lists of finite geometric labels into a disjoint atlas. Coefficient
rounding, clipping, Boolean format, and original-law success are all explicit. -/
theorem grouped_scalar_atlas
    {α X β : Type*} [MeasurableSpace X] [DecidableEq β]
    {n M D : ℕ} {R ρ H B error : ℝ}
    (hR : 1 ≤ R) (hρ : 0 ≤ ρ) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (b : α → Fin 5 → ℝ) (hb : ∀ l i, |b l i| ≤ R)
    (O : α × ℝ → X)
    (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (c : Fin n → Fin 6 → ℝ)
    (hc : ∀ i t y, MvPolynomial.eval ![t, y] (P i) = quadraticValue (c i) t y)
    (A : Fin n → Set (Fin 5 → ℝ))
    (hformat : ∀ i, fmt 5 B D (A i))
    (hfit : ∀ i, A i ⊆ scalarFit (P i) error)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (label : Fin n → β) (center : β → Fin 6 → ℝ)
    (hcenter : ∀ i j, |center (label i) j| ≤ H)
    (hdiff : ∀ i j, |c i j - center (label i) j| ≤ ρ)
    (L : X → Finset β) (hL : ∀ x, (L x).card ≤ M)
    (hLm : ∀ q, MeasurableSet {x | q ∈ L x}) :
    ∃ (k : ℕ) (Q : Fin k → MvPolynomial (Fin 2) ℝ)
      (C : Fin k → Set (Fin 5 → ℝ)) (K : X → Finset (Fin k)),
      k ≤ n ∧
      (∀ j, (Q j).totalDegree ≤ 2 ∧ (∀ e, |(Q j).coeff e| ≤ 6 * H) ∧
        MeasurableSet (C j) ∧ fmt 5 (10 + (n : ℝ) * B) (max 1 D) (C j) ∧
        C j ⊆ scalarFit (Q j) (error + 24 * ρ * R ^ 2)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ x, (K x).card ≤ M) ∧ (∀ j, MeasurableSet {x | j ∈ K x}) ∧
      {p | ∃ i, b p.1 ∈ A i ∧ label i ∈ L (O p)} =
        {p | ∃ j, b p.1 ∈ C j ∧ j ∈ K (O p)} := by
  classical
  obtain ⟨k, q, hkn, hq, hqrange⟩ := enumerate_occupied_labels label
  obtain ⟨K, hKmem, hKcard, hKmeas⟩ := reindex_lists q hq L hL hLm
  let Q : Fin k → MvPolynomial (Fin 2) ℝ := fun j => quadraticPolynomial (center (q j))
  let C : Fin k → Set (Fin 5 → ℝ) := fun j => groupedAssignment R label A (q j)
  refine ⟨k, Q, C, K, hkn, ?_, ?_, hKcard, hKmeas, ?_⟩
  · intro j
    obtain ⟨i, hi⟩ := (hqrange (q j)).mpr ⟨j, rfl⟩
    refine ⟨quadraticPolynomial_degree _, quadraticPolynomial_coeff_bound hH
      (fun e => by simpa only [hi] using hcenter i e),
      groupedAssignment_measurable hB R label A hformat _,
      groupedAssignment_format hB R label A hformat _, ?_⟩
    rintro z ⟨hz, i', hi', hz'⟩ t ht
    change |scalarX z t - MvPolynomial.eval ![t, scalarY z t]
      (quadraticPolynomial (center (q j)))| ≤ _
    rw [← hi']
    exact clipped_fit_perturbation hR hρ (hc i') (hdiff i') hz (hfit i' hz') ht
  · intro i j hij
    exact groupedAssignment_disjoint R label A hdisj (fun h => hij (hq h))
  · ext p
    constructor
    · rintro ⟨i, hi, hLi⟩
      obtain ⟨j, hj⟩ := (hqrange (label i)).mp ⟨i, rfl⟩
      refine ⟨j, ⟨hb p.1, i, hj.symm, hi⟩, (hKmem _ _).mpr ?_⟩
      rwa [hj]
    · rintro ⟨j, ⟨_, i, hi, hAi⟩, hKj⟩
      refine ⟨i, hAi, ?_⟩
      rw [hi]
      exact (hKmem _ _).mp hKj

end Submission.Obl.k4_fixed_budget_quadratic_recovery
