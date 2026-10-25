import Submission.Obl.k4_affine_skew_row_fit.Recovery

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_affine_skew_row_fit

/-- Projected cell errors and a planar strip error add with one factor of the slope. -/
theorem strip_error_transfer {K h X Y x y ℓ c : ℝ} (hK : 1 ≤ K) (hh : 0 ≤ h)
    (hℓ : |ℓ| ≤ K) (hx : |X - x| ≤ K * h) (hy : |Y - y| ≤ K * h)
    (hstrip : |y - ℓ * x - c| ≤ K * h) :
    |Y - ℓ * X - c| ≤ 3 * K ^ 2 * h := by
  have hKpos : 0 ≤ K := by linarith
  calc
    _ = |(Y - y) + (y - ℓ * x - c) - ℓ * (X - x)| := by congr 1; ring
    _ ≤ |Y - y| + |y - ℓ * x - c| + |ℓ * (X - x)| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K * h + K * h + K * (K * h) := by
      rw [abs_mul]
      exact add_le_add (add_le_add hy hstrip) (mul_le_mul hℓ hx
        (abs_nonneg _) hKpos)
    _ ≤ 3 * K ^ 2 * h := by
      have hKK : K ≤ K ^ 2 := by nlinarith [sq_nonneg (K - 1)]
      nlinarith [mul_le_mul_of_nonneg_right hKK hh]

/-- Counting retained edges is converted to original incidence mass by disjoint witnesses. -/
theorem retained_edge_mass {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : Finset ι) (W : ι → Set X)
    (hW : ∀ e ∈ G, MeasurableSet (W e))
    (hdisj : (G : Set ι).PairwiseDisjoint W)
    {K h : ℝ} (hK : 0 < K) (hh : 0 < h)
    (hcard : 1 / (K * h ^ 2) ≤ (G.card : ℝ))
    (hmass : ∀ e ∈ G, ENNReal.ofReal (h ^ 2 / K) ≤ μ (W e)) :
    ENNReal.ofReal (1 / K ^ 2) ≤ μ (⋃ e ∈ G, W e) := by
  classical
  have hlow : 1 / K ^ 2 ≤ (G.card : ℝ) * (h ^ 2 / K) := by
    calc
      _ = (1 / (K * h ^ 2)) * (h ^ 2 / K) := by field_simp
      _ ≤ (G.card : ℝ) * (h ^ 2 / K) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
  calc
    _ ≤ ENNReal.ofReal ((G.card : ℝ) * (h ^ 2 / K)) := ENNReal.ofReal_le_ofReal hlow
    _ = ∑ _e ∈ G, ENNReal.ofReal (h ^ 2 / K) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ ∑ e ∈ G, μ (W e) := Finset.sum_le_sum hmass
    _ = μ (⋃ e ∈ G, W e) := (measure_biUnion_finset hdisj hW).symm

/-- Retained original edges in parallel strips lift to an affine-skew incidence row. -/
theorem row_from_retained_edges {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (μ : Measure (α × ℝ))
    {K h E v₁ v₂ c₁ c₂ ℓ₀ : ℝ} (hK : 1 ≤ K) (hh : 0 < h)
    (hE : 0 < E) (hEone : E ≤ 1)
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume))
    (z T : α × ℝ → Fin 2 → ℝ) (hztime : ∀ p, z p 0 = p.2)
    (G : Finset ((ℝ × ℝ) × (ℝ × ℝ)))
    (W : ((ℝ × ℝ) × (ℝ × ℝ)) → Set (α × ℝ))
    (hW : ∀ e ∈ G, MeasurableSet (W e))
    (hdisj : (G : Set ((ℝ × ℝ) × (ℝ × ℝ))).PairwiseDisjoint W)
    (hcard : 1 / (K * h ^ 2) ≤ (G.card : ℝ))
    (hmass : ∀ e ∈ G, ENNReal.ofReal (h ^ 2 / K) ≤ μ (W e))
    (hdata : ∀ e ∈ G, ∀ p ∈ W e,
      |z p 0| ≤ 1 ∧ |z p 1| ≤ K ∧ (∀ j, |T p j| ≤ K))
    (hv₁ : |v₁| ≤ K) (hv₂ : |v₂| ≤ K) (hsep : 1 / K ≤ |v₂ - v₁|)
    (hℓ : |ℓ₀| ≤ K)
    (hproject : ∀ e ∈ G, ∀ p ∈ W e,
      |z p 1 - v₁ * z p 0 - e.1.1| ≤ K * h ∧
      |(h / E) * (T p 0 + v₁ * T p 1) - e.1.2| ≤ K * h ∧
      |z p 1 - v₂ * z p 0 - e.2.1| ≤ K * h ∧
      |(h / E) * (T p 0 + v₂ * T p 1) - e.2.2| ≤ K * h)
    (hstrips : ∀ e ∈ G,
      |e.1.2 - ℓ₀ * e.1.1 - c₁| + |e.2.2 - ℓ₀ * e.2.1 - c₂| ≤ K * h) :
    ∃ B : Fin 2 → ℝ, ∃ ℓ : ℝ,
      |B 0| + |B 1| + |ℓ| ≤ 23328 * K ^ 12 ∧
      ENNReal.ofReal (1 / (3 * K ^ 2)) ≤ μ {p |
        |T p 0 - B 0 + ℓ * z p 1| ≤ 81 * K ^ 6 * E ∧
        |T p 1 - B 1 - ℓ * z p 0| ≤ 81 * K ^ 6 * E} := by
  have hKpos : 0 < K := by linarith
  let D : ℝ := 3 * K ^ 2
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [sq_nonneg (K - 1)]
  have hKD : K ≤ D := by dsimp [D]; nlinarith [sq_nonneg (K - 1)]
  let A := ⋃ e ∈ G, W e
  have hmA : ENNReal.ofReal (1 / D) ≤ μ A := by
    have hKsq : 0 < K ^ 2 := by positivity
    apply (ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le hKsq (by dsimp [D]; nlinarith))).trans
    exact retained_edge_mass μ G W hW hdisj hKpos hh hcard hmass
  have hdomD : μ ≤ ENNReal.ofReal D • (ν.prod volume) := by
    apply hdom.trans
    intro s
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hKD)
      (zero_le : (0 : ENNReal) ≤ (ν.prod volume) s)
  have hAdata : ∀ p ∈ A, |z p 0| ≤ 1 ∧ |z p 1| ≤ D ∧ (∀ j, |T p j| ≤ D) := by
    intro p hp
    obtain ⟨e, hp⟩ := mem_iUnion.mp hp
    obtain ⟨he, hp⟩ := mem_iUnion.mp hp
    have hd := hdata e he p hp
    exact ⟨hd.1, hd.2.1.trans hKD, fun j => (hd.2.2 j).trans hKD⟩
  have hstrip₁ : ∀ p ∈ A,
      |(h / E) * T p 0 + v₁ * ((h / E) * T p 1) -
        ℓ₀ * (z p 1 - v₁ * z p 0) - c₁| ≤ D * h := by
    intro p hp
    obtain ⟨e, hp⟩ := mem_iUnion.mp hp
    obtain ⟨he, hp⟩ := mem_iUnion.mp hp
    have hproj := hproject e he p hp
    have hstrip : |e.1.2 - ℓ₀ * e.1.1 - c₁| ≤ K * h :=
      (le_add_of_nonneg_right (abs_nonneg _)).trans (hstrips e he)
    convert strip_error_transfer hK hh.le hℓ hproj.1 hproj.2.1 hstrip using 1
    congr 1
    ring
  have hstrip₂ : ∀ p ∈ A,
      |(h / E) * T p 0 + v₂ * ((h / E) * T p 1) -
        ℓ₀ * (z p 1 - v₂ * z p 0) - c₂| ≤ D * h := by
    intro p hp
    obtain ⟨e, hp⟩ := mem_iUnion.mp hp
    obtain ⟨he, hp⟩ := mem_iUnion.mp hp
    have hproj := hproject e he p hp
    have hstrip : |e.2.2 - ℓ₀ * e.2.1 - c₂| ≤ K * h :=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hstrips e he)
    convert strip_error_transfer hK hh.le hℓ hproj.2.2.1 hproj.2.2.2 hstrip using 1
    congr 1
    ring
  have hsepD : 1 / D ≤ |v₂ - v₁| :=
    (one_div_le_one_div_of_le hKpos hKD).trans hsep
  obtain ⟨B, ℓ, hB, hfit⟩ := recover_dense_row ν μ hD hh hE hEone hdomD z T hztime A hmA
    (fun p hp => (hAdata p hp).1) (fun p hp => (hAdata p hp).2.1)
    (fun p hp => (hAdata p hp).2.2) (hv₁.trans hKD) (hv₂.trans hKD) hsepD hstrip₁ hstrip₂
  refine ⟨B, ℓ, ?_, ?_⟩
  · convert hB using 1
    dsimp [D]
    ring
  · have hiden : 3 * D ^ 3 * E = 81 * K ^ 6 * E := by dsimp [D]; ring
    simpa only [hiden] using hfit

end Submission.Obl.k4_affine_skew_row_fit
