import Submission.Obl.k4_scalar_pair_atlas_assembly.Dyadic
import Submission.Obl.k4_scalar_pair_atlas_assembly.SourceSelection
set_option autoImplicit false
namespace Submission.Obl.k4_scalar_pair_atlas_assembly
open MeasureTheory Set
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
noncomputable section

/-- Later incidences compatible with a full source assignment from one fixed fine block. -/
def laterEvent (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k))
    (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (a e : ℝ) (T₁ : ℕ) (w : Fin (W p k)) (b : Fin (2 ^ T₁))
    (s : Fin (2 ^ T)) : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  {q | ∃ i i' : Fin n, γ i = w ∧ γ i' = w ∧ j i = s ∧
    I T (j i) ⊆ I T₁ b ∧ I T (j i') ⊆ I T₁ b ∧
    q.1 ∈ A i ∧ q ∈ C i' ∧ Agrees p k T₁ n u v P a e b i i'}

lemma measurable_laterEvent (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k))
    (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (a e : ℝ) (T₁ : ℕ) (w : Fin (W p k)) (b : Fin (2 ^ T₁))
    (s : Fin (2 ^ T)) (hA : ∀ i, MeasurableSet (A i))
    (hC : ∀ i, MeasurableSet (C i)) :
    MeasurableSet (laterEvent p k T n γ j A C u v P a e T₁ w b s) := by
  classical
  unfold laterEvent
  simp only [ofPred_exists, ofPred_and]
  apply MeasurableSet.iUnion fun i => ?_
  apply MeasurableSet.iUnion fun i' => ?_
  have hAi : MeasurableSet {q : (ℕ × (Fin 5 → ℝ)) × ℝ | q.1 ∈ A i} :=
    (hA i).preimage measurable_fst
  measurability

lemma laterEvent_subset (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k))
    (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (a e : ℝ) (T₁ : ℕ) (w : Fin (W p k)) (b : Fin (2 ^ T₁))
    (s : Fin (2 ^ T))
    (hC : ∀ i, C i ⊆ E p k (γ i) ∩ (A i ×ˢ I T (j i))) :
    laterEvent p k T n γ j A C u v P a e T₁ w b s ⊆
      E p k w ∩ {q | q.2 ∈ I T₁ b} := by
  rintro q ⟨i, i', hi, hi', hjs, hIs, hIw, hAi, hCi, hAg⟩
  have hq := hC i' hCi
  exact ⟨by simpa [hi'] using hq.1, hIw hq.2.2⟩

/-- Choosing one fine source block in every world/coarse block loses no normalized pair mass. -/
theorem exists_source_block (p : Code) (k T n : ℕ) (γ : Fin n → Fin (W p k))
    (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set (ℕ × (Fin 5 → ℝ)))
    (C : Fin n → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (a e : ℝ) (T₁ : ℕ) (ht : T₁ ≤ T) (w : Fin (W p k)) (b : Fin (2 ^ T₁))
    (hA : ∀ i, MeasurableSet (A i)) (hC : ∀ i, MeasurableSet (C i))
    (hsub : ∀ i, C i ⊆ E p k (γ i) ∩ (A i ×ˢ I T (j i))) :
    ∃ s : Fin (2 ^ T), I T s ⊆ I T₁ b ∧
      ENNReal.ofReal ((2 : ℝ) ^ T₁) *
        ((ν p k w).prod (volume.prod volume))
          (goodPairs p k T n γ j C u v P a e T₁ w b) ≤
      mu p k w (laterEvent p k T n γ j A C u v P a e T₁ w b s) := by
  classical
  let U := fun r : Fin (2 ^ (T-T₁)) =>
    laterEvent p k T n γ j A C u v P a e T₁ w b (child ht b r)
  have hU (r) : MeasurableSet (U r) :=
    measurable_laterEvent p k T n γ j A C u v P a e T₁ w b _ hA hC
  have hcover : goodPairs p k T n γ j C u v P a e T₁ w b ⊆
      ⋃ r : Fin (2 ^ (T-T₁)), {z | z.2.1 ∈ I T (child ht b r) ∧ (z.1, z.2.2) ∈ U r} := by
    rintro z ⟨hs, ht', i, i', hi, hi', hIs, hIw, hCi, hCi', hAg⟩
    obtain ⟨r, hr⟩ := exists_child_of_subset ht b (j i) hIs
    refine mem_iUnion.mpr ⟨r, ?_, i, i', hi, hi', hr, hIs, hIw, (hsub i hCi).2.1, hCi', hAg⟩
    simpa [← hr] using (hsub i hCi).2.2
  have hscale : ENNReal.ofReal ((2 : ℝ) ^ T₁) *
      (Fintype.card (Fin (2 ^ (T-T₁))) : ENNReal) * ENNReal.ofReal (width T) = 1 := by
    rw [Fintype.card_fin, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have h : (2 : ℝ) ^ T₁ * (2 ^ (T-T₁) : ℕ) * width T = 1 := by
      push_cast
      rw [mul_assoc, width_split ht]
      simp [width]
    rw [h, ENNReal.ofReal_one]
  obtain ⟨r, hr⟩ := finite_source_selection (ν p k w)
    (fun r => I T (child ht b r)) U
    (fun r => measurableSet_Icc) hU _ hcover
    (ENNReal.ofReal (width T)) (ENNReal.ofReal ((2 : ℝ) ^ T₁))
    (fun r => volume_I _ _) hscale
  refine ⟨child ht b r, child_interval_subset ht b r, ?_⟩
  have heq : mu p k w (U r) = ((ν p k w).prod volume) (U r) := by
    rw [mu, Measure.restrict_apply (hU r), inter_eq_left.mpr
      (fun q hq => (laterEvent_subset p k T n γ j A C u v P a e T₁ w b _ hsub hq).1)]
  simpa [← heq] using hr

end
end Submission.Obl.k4_scalar_pair_atlas_assembly
