import Submission.Obl.k4_scalar_normalized_exact_refinement.Basic

/-!
# Facts of a chart system and of a Refinement certificate at one index

* projections of `Spec.ChartData`;
* the normalization constant `c = (dt ν(A))⁻¹` is positive and finite, and
  `ω_q c = ω_p / Z` for the Refinement weights;
* the density factor `c (dt J) = J / ν(A)`;
* `Z ≥ N^(-ε)` from the chart's retained mass;
* within one original world a point lies in at most two selected sets.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set Filter
open scoped ENNReal

section ChartFacts

variable {p : Code} {B : ℕ} {r b h ε : ℝ} {isTrue : Bool} {k T n : ℕ}
  {γ : Fin n → Fin (p.1 k)} {j : Fin n → Fin (2 ^ T)} {A : Fin n → Set Line}
  {C : Fin n → Set Inc} {u v J : Fin n → ℝ} {P : Fin n → MvPolynomial (Fin 2) ℝ}
  {Λ : Fin (p.1 k) → Base → Finset (Fin n)}

lemma ChartData.measA (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (i : Fin n) : MeasurableSet (A i) := (hc.2.2.1 i).1
lemma ChartData.measC (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (i : Fin n) : MeasurableSet (C i) := (hc.2.2.1 i).2
lemma ChartData.disj (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) :
    ∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i') := hc.2.2.2.1
lemma ChartData.sub (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (i : Fin n) : C i ⊆ p.E k (γ i) ∩ (A i ×ˢ Spec.I T (j i)) := hc.2.2.2.2.1 i
lemma ChartData.mu_pos (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (i : Fin n) : 0 < p.mu k (γ i) (C i) := (hc.2.2.2.2.2.1 i).1
lemma ChartData.J_pos (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (i : Fin n) : 0 < J i := (hc.2.2.2.2.2.1 i).2.1
lemma ChartData.J_le (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (i : Fin n) : J i ≤ p.N k ^ ε / (2 : ℝ) ^ T := (hc.2.2.2.2.2.1 i).2.2.2.1
lemma ChartData.Λcard (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) :
    ∀ a z, ((Λ a z).card : ℝ) ≤ p.N k ^ ε := hc.2.2.2.2.2.2.1
lemma ChartData.Λmeas (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) :
    ∀ a i, MeasurableSet {z | i ∈ Λ a z} := hc.2.2.2.2.2.2.2.1
lemma ChartData.Λae (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (i : Fin n) : p.mu k (γ i) {q | q ∈ C i ∧ i ∉ Λ (γ i) (obs (p.N k) b q)} = 0 :=
  hc.2.2.2.2.2.2.2.2.1 i
lemma ChartData.mass (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) :
    ENNReal.ofReal (p.N k ^ (-ε)) ≤
      ∑ a : Fin (p.1 k), ENNReal.ofReal (p.ω k a) * p.mu k a {q | ∃ i, γ i = a ∧ q ∈ C i} :=
  hc.2.2.2.2.2.2.2.2.2

/-- Selected masses are bounded by the prior mass of the assignment times the block length. -/
lemma ChartData.mu_le (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ)
    (i : Fin n) (X : Set Inc) :
    p.mu k (γ i) (C i ∩ X) ≤ p.ν k (γ i) (A i) * ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) := by
  calc p.mu k (γ i) (C i ∩ X) ≤ p.mu k (γ i) (A i ×ˢ Spec.I T (j i)) :=
        measure_mono (inter_subset_left.trans (((ChartData.sub hc) i).trans inter_subset_right))
    _ ≤ ((p.ν k (γ i)).prod volume) (A i ×ˢ Spec.I T (j i)) := Measure.restrict_apply_le _ _
    _ = p.ν k (γ i) (A i) * volume (Spec.I T (j i)) := Measure.prod_prod _ _
    _ = p.ν k (γ i) (A i) * ENNReal.ofReal (((2 : ℝ) ^ T)⁻¹) := by
        congr 1
        rw [Spec.I, Real.volume_Icc]
        congr 1
        field_simp
        ring

open Classical in
/-- A point lies in at most two selected sets of one world. -/
lemma ChartData.card_mem_le_two
    (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) (a : Fin (p.1 k))
    (z : Inc) : (Finset.univ.filter (fun i => γ i = a ∧ z ∈ C i)).card ≤ 2 := by
  classical
  set F := Finset.univ.filter (fun i => γ i = a ∧ z ∈ C i)
  have hinj : Set.InjOn (fun i => ((j i : ℕ) : ℤ)) (F : Set (Fin n)) := by
    intro i hi i' hi' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq, F] at hi hi'
    by_contra hne
    have heq' : ((j i : ℕ) : ℤ) = ((j i' : ℕ) : ℤ) := heq
    have hj : j i = j i' := Fin.ext (by exact_mod_cast heq')
    have hd := (ChartData.disj hc) i i' hne (hi.1.trans hi'.1.symm) hj
    have h1 := ((ChartData.sub hc) i hi.2).2
    have h2 := ((ChartData.sub hc) i' hi'.2).2
    exact Set.disjoint_left.mp hd h1.1 h2.1
  set t := z.2 * (2 : ℝ) ^ T
  have hmem : ∀ i ∈ F, ((j i : ℕ) : ℤ) ∈ Finset.Icc (⌊t⌋ - 1) ⌊t⌋ := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, F] at hi
    have hI := (((ChartData.sub hc) i hi.2).2).2
    simp only [Spec.I, mem_Icc] at hI
    have h2T : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
    have hlo : ((j i : ℕ) : ℝ) ≤ t := by
      have := (div_le_iff₀ h2T).mp hI.1
      simpa [t] using this
    have hhi : t ≤ ((j i : ℕ) : ℝ) + 1 := by
      have := (le_div_iff₀ h2T).mp hI.2
      simpa [t] using this
    rw [Finset.mem_Icc]
    constructor
    · have : ⌊t⌋ ≤ ((j i : ℕ) : ℤ) + 1 := by
        apply Int.floor_le_iff.mpr
        push_cast
        linarith
      omega
    · exact Int.le_floor.mpr (by exact_mod_cast hlo)
  calc F.card = (F.image (fun i => ((j i : ℕ) : ℤ))).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc (⌊t⌋ - 1) ⌊t⌋).card := Finset.card_le_card (by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact hmem i hi)
    _ = 2 := by simp

open Classical in
/-- Selected sets of one world overlap at most twice. -/
lemma ChartData.sum_mu_le_two
    (hc : Spec.ChartData p B r b h ε isTrue k T n γ j A C u v J P Λ) (a : Fin (p.1 k))
    {X : Set Inc} (hX : MeasurableSet X) :
    ∑ i ∈ Finset.univ.filter (fun i => γ i = a), p.mu k a (C i ∩ X) ≤ 2 * p.mu k a X := by
  classical
  have hind : ∀ z, ∑ i ∈ Finset.univ.filter (fun i => γ i = a),
      (C i ∩ X).indicator (fun _ => (1 : ℝ≥0∞)) z ≤ 2 * X.indicator (fun _ => (1 : ℝ≥0∞)) z := by
    intro z
    by_cases hz : z ∈ X
    · simp only [indicator_of_mem hz, mul_one]
      calc ∑ i ∈ Finset.univ.filter (fun i => γ i = a),
            (C i ∩ X).indicator (fun _ => (1 : ℝ≥0∞)) z
          = ∑ i ∈ Finset.univ.filter (fun i => γ i = a), (if z ∈ C i then (1 : ℝ≥0∞) else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hzi : z ∈ C i
            · simp [Set.indicator, hzi, hz]
            · simp [Set.indicator, hzi]
        _ = ((Finset.univ.filter (fun i => γ i = a)).filter (fun i => z ∈ C i)).card := by
            rw [Finset.sum_boole]
        _ ≤ 2 := by
            rw [Finset.filter_filter]
            exact_mod_cast (ChartData.card_mem_le_two hc) a z
    · simp only [indicator_of_notMem hz, mul_zero, nonpos_iff_eq_zero]
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (fun h => hz h.2) _
  calc ∑ i ∈ Finset.univ.filter (fun i => γ i = a), p.mu k a (C i ∩ X)
      = ∑ i ∈ Finset.univ.filter (fun i => γ i = a),
          ∫⁻ z, (C i ∩ X).indicator (fun _ => (1 : ℝ≥0∞)) z ∂(p.mu k a) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [lintegral_indicator_const (((ChartData.measC hc) i).inter hX), one_mul]
    _ = ∫⁻ z, ∑ i ∈ Finset.univ.filter (fun i => γ i = a),
          (C i ∩ X).indicator (fun _ => (1 : ℝ≥0∞)) z ∂(p.mu k a) := by
        rw [lintegral_finsetSum]
        intro i _
        exact measurable_const.indicator (((ChartData.measC hc) i).inter hX)
    _ ≤ ∫⁻ z, 2 * X.indicator (fun _ => (1 : ℝ≥0∞)) z ∂(p.mu k a) := lintegral_mono hind
    _ = 2 * p.mu k a X := by
        rw [lintegral_const_mul _ (measurable_const.indicator hX), lintegral_indicator_const hX,
          one_mul]

end ChartFacts

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
