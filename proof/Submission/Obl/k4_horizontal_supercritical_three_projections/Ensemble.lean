import Submission.Obl.k4_horizontal_supercritical_three_projections.Refinement
import Submission.Obl.k4_horizontal_supercritical_three_projections.ScalarUse

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory
open scoped ENNReal BigOperators
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable def chartWeight (π : Measure ℝ) (χ D : ℝ) (q : Fin 3 → ℤ) : ℝ :=
  (π (Ico ((q 0 : ℝ) * χ) (((q 0 : ℝ) + 1) * χ))).toReal * D ^ 2

/-- Assemble every scalar packet in every retained chart, with the original
chart prior weights restored. No chart, scalar label or prior is reweighted. -/
theorem coarse_layer_of_scalar_ensemble {α ι : Type} [MeasurableSpace α] [Fintype ι]
    {N d s m τ χ D H E : ℝ} (hN : 1 ≤ N) (hτ : 0 ≤ τ)
    (ν : Measure α) [IsFiniteMeasure ν] (ζ : Measure (α × ℝ))
    (π : Measure ℝ) (b : α → Fin 6 → ℝ) (G : ι → Set α) (q : ι → Fin 3 → ℤ)
    (hν : ∀ i, ν (G i) ≠ 0)
    (hdisj : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hcorner : ∀ i, |(q i 0 : ℝ) * χ| + |(q i 1 : ℝ) * D| + |(q i 2 : ℝ) * D| ≤ H)
    (hcoords : ∀ i l, l ∈ G i →
      ⌊b l 3 / χ⌋ = q i 0 ∧ ⌊b l 1 / D⌋ = q i 2 ∧
      b l 0 ∈ Ico ((q i 1 : ℝ) * D) ((q i 1 : ℝ) * D + D) ∧
      |b l 1 - (q i 2 : ℝ) * D| ≤ D ∧ (∀ e, |b l e| ≤ H) ∧ |b l 4 + b l 0| ≤ E)
    (hpalette : ∀ i, 0 < π (Ico ((q i 0 : ℝ) * χ) (((q i 0 : ℝ) + 1) * χ)))
    (F : (i : ι) → ScalarPackets N d s m (chartWeight π χ D (q i) / (ν (G i)).toReal) τ
      (chartLaw ν ζ (G i))
      (fun l => ![(b l 1 - (q i 2 : ℝ) * D) / D,
        -2 * ((b l 0 - (q i 1 : ℝ) * D) / D), b l 2, b l 5, 0]))
    (hsub : ∀ i j, (F i).A j ⊆ G i) :
    ∃ L : CoarseProjectionLayer α,
      L.Certified b χ D H E (240 * (N ^ τ) ^ 5) (N ^ τ * N ^ (-s)) ∧
      (∀ j, 0 < π (Ico ((L.q j 0 : ℝ) * χ) (((L.q j 0 : ℝ) + 1) * χ))) ∧
      (∀ j, ENNReal.ofReal (L.weight π χ D (N ^ (-s)) d j * N ^ (-τ) / N ^ τ) ≤
        ζ (L.A j ×ˢ Icc (0 : ℝ) 1)) ∧
      (∑ i, ENNReal.ofReal ((ν (G i)).toReal * N ^ (-τ))) ≤
        ζ {p | ∃ j, p.1 ∈ L.A j} := by
  classical
  let J := (i : ι) × Fin (F i).n
  let e := (Fintype.equivFin J).symm
  let L : CoarseProjectionLayer α := {
    n := Fintype.card J
    A := fun j => (F (e j).1).A (e j).2
    q := fun j => q (e j).1
    P := fun j => ((F (e j).1).candidate (e j).2).P }
  have hdisj' : Pairwise (fun ij ij' : J =>
      Disjoint ((F ij.1).A ij.2) ((F ij'.1).A ij'.2)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    by_cases hi : i = i'
    · subst i'
      exact (F i).disjoint j j' (fun hj => hij (by subst j'; rfl))
    · exact (hdisj i i' hi).mono (hsub i j) (hsub i' j')
  have hfit' (i : ι) (j : Fin (F i).n) (l : α) (hl : l ∈ (F i).A j)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |b l 2 + t * b l 5 - MvPolynomial.eval
        ![t, (b l 1 - (q i 2 : ℝ) * D) / D -
          2 * t * ((b l 0 - (q i 1 : ℝ) * D) / D)] ((F i).candidate j).P| ≤
        N ^ τ * N ^ (-s) := by
    have hf := (F i).fit j l hl t ht
    have hy : (b l 1 - (q i 2 : ℝ) * D) / D +
        t * (-2 * ((b l 0 - (q i 1 : ℝ) * D) / D)) =
        (b l 1 - (q i 2 : ℝ) * D) / D - 2 * t * ((b l 0 - (q i 1 : ℝ) * D) / D) := by ring
    change |b l 2 + t * b l 5 + t ^ 2 * 0 - MvPolynomial.eval
      ![t, (b l 1 - (q i 2 : ℝ) * D) / D +
        t * (-2 * ((b l 0 - (q i 1 : ℝ) * D) / D))] ((F i).candidate j).P| ≤ _ at hf
    simpa only [mul_zero, add_zero, hy] using hf
  have hrestore (i : ι) := (F i).restore ν ζ (G i) (hν i) _
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · refine {
      measurable := fun j => (F (e j).1).measurable (e j).2
      disjoint := fun j j' hj => hdisj' (fun h => hj (e.injective h))
      corner := fun j => hcorner (e j).1
      degree := fun j => ((F (e j).1).candidate (e j).2).degree
      coeff := fun j mon => ((F (e j).1).candidate (e j).2).coeff_bound hN hτ mon
      coordinates := fun j l hl => hcoords (e j).1 l (hsub _ _ hl)
      fit := fun j l hl t ht => hfit' _ _ l hl t ht }
  · exact fun j => hpalette (e j).1
  · intro j
    simpa only [L, CoarseProjectionLayer.weight, chartWeight, mul_assoc] using
      (hrestore (e j).1).1 (e j).2
  · let A := fun i : ι => {p : α × ℝ | ∃ j, p.1 ∈ (F i).A j}
    have hA (i) : MeasurableSet (A i) := by
      simp only [A, Set.ofPred_exists]
      exact MeasurableSet.iUnion fun j => ((F i).measurable j).preimage measurable_fst
    have hdA : Pairwise (fun i j => Disjoint (A i) (A j)) := by
      intro i j hij
      apply disjoint_left.mpr
      rintro p ⟨a, ha⟩ ⟨a', ha'⟩
      exact disjoint_left.mp (hdisj i j hij) (hsub i a ha) (hsub j a' ha')
    have hcov : {p : α × ℝ | ∃ j, p.1 ∈ L.A j} = ⋃ i, A i := by
      ext p
      constructor
      · rintro ⟨j, hj⟩
        exact mem_iUnion.mpr ⟨(e j).1, (e j).2, hj⟩
      · intro hp
        obtain ⟨i, j, hj⟩ := mem_iUnion.mp hp
        refine ⟨e.symm ⟨i, j⟩, ?_⟩
        change p.1 ∈ (F (e (e.symm ⟨i, j⟩)).1).A (e (e.symm ⟨i, j⟩)).2
        rw [e.apply_symm_apply]
        exact hj
    calc
      _ ≤ ∑ i, ζ (A i) := Finset.sum_le_sum fun i _ => (hrestore i).2
      _ = ζ (⋃ i, A i) := by rw [measure_iUnion hdA hA, tsum_fintype]
      _ = _ := congrArg ζ hcov.symm

end Submission.Obl.k4_horizontal_supercritical_three_projections
