import Mathlib
import Submission.Lib.K4XInterface.Basic

/-!
# Boolean formats and list counts for outputs of the frozen interface X

* `gfmt_inter`, `gfmt_union`, `gfmt_compl`, `gfmt_nonneg`, `gfmt_univ`: the frozen Boolean
  polynomial format is closed under Boolean operations (test counts add, degrees take the
  maximum); `measurableSet_of_gfmt`: sets in format are measurable.
* `card_filter_le_of_fibers`: refined labels over a list of old labels.
* `path_charts_met_subset`: the level-`i` path charts of a world met by a terminal
  observation lie in the level-`i` list of the coarsened observation.
-/

namespace Submission.Lib.K4XInterface

/-- Intersections add the test counts. -/
theorem gfmt_inter {n : ℕ} {H₁ H₂ : ℝ} {D₁ D₂ : ℕ} {A₁ A₂ : Set (Fin n → ℝ)}
    (h₁ : gfmt n H₁ D₁ A₁) (h₂ : gfmt n H₂ D₂ A₂) :
    gfmt n (H₁ + H₂) (max D₁ D₂) (A₁ ∩ A₂) := by
  obtain ⟨m₁, hm₁, p₁, hp₁, b₁, hb₁⟩ := h₁
  obtain ⟨m₂, hm₂, p₂, hp₂, b₂, hb₂⟩ := h₂
  refine ⟨m₁ + m₂, by push_cast; linarith, Fin.addCases p₁ p₂, ?_,
    fun v => b₁ (fun i => v (Fin.castAdd m₂ i)) && b₂ (fun i => v (Fin.natAdd m₁ i)), ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.addCases_left] using (hp₁ i).trans (le_max_left _ _)
    · simpa only [Fin.addCases_right] using (hp₂ i).trans (le_max_right _ _)
  · intro x
    simp only [Set.mem_inter_iff, Fin.addCases_left, Fin.addCases_right, Bool.and_eq_true]
    exact and_congr (hb₁ x) (hb₂ x)

/-- Unions add the test counts. -/
theorem gfmt_union {n : ℕ} {H₁ H₂ : ℝ} {D₁ D₂ : ℕ} {A₁ A₂ : Set (Fin n → ℝ)}
    (h₁ : gfmt n H₁ D₁ A₁) (h₂ : gfmt n H₂ D₂ A₂) :
    gfmt n (H₁ + H₂) (max D₁ D₂) (A₁ ∪ A₂) := by
  obtain ⟨m₁, hm₁, p₁, hp₁, b₁, hb₁⟩ := h₁
  obtain ⟨m₂, hm₂, p₂, hp₂, b₂, hb₂⟩ := h₂
  refine ⟨m₁ + m₂, by push_cast; linarith, Fin.addCases p₁ p₂, ?_,
    fun v => b₁ (fun i => v (Fin.castAdd m₂ i)) || b₂ (fun i => v (Fin.natAdd m₁ i)), ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.addCases_left] using (hp₁ i).trans (le_max_left _ _)
    · simpa only [Fin.addCases_right] using (hp₂ i).trans (le_max_right _ _)
  · intro x
    simp only [Set.mem_union, Fin.addCases_left, Fin.addCases_right, Bool.or_eq_true]
    exact or_congr (hb₁ x) (hb₂ x)

/-- Complements keep the tests. -/
theorem gfmt_compl {n : ℕ} {H : ℝ} {D : ℕ} {A : Set (Fin n → ℝ)} (h : gfmt n H D A) :
    gfmt n H D Aᶜ := by
  obtain ⟨m, hm, p, hp, b, hb⟩ := h
  refine ⟨m, hm, p, hp, fun v => !b v, fun x => ?_⟩
  simp only [Set.mem_compl_iff, Bool.not_eq_true', hb x]
  cases b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) <;> simp

/-- One polynomial sign condition. -/
theorem gfmt_nonneg {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    gfmt n 1 p.totalDegree {x | 0 ≤ MvPolynomial.eval x p} := by
  refine ⟨1, by norm_num, fun _ => p, fun _ => le_rfl, fun v => v 0, fun x => ?_⟩
  simp

/-- The whole space and the empty set. -/
theorem gfmt_univ (n : ℕ) (H : ℝ) (hH : 0 ≤ H) (D : ℕ) : gfmt n H D Set.univ :=
  ⟨0, by simpa using hH, Fin.elim0, fun i => i.elim0, fun _ => true, fun x => by simp⟩

/-- Sets in Boolean format are measurable. -/
theorem measurableSet_of_gfmt {n : ℕ} {H : ℝ} {D : ℕ} {A : Set (Fin n → ℝ)}
    (h : gfmt n H D A) : MeasurableSet A := by
  obtain ⟨m, -, p, -, b, hb⟩ := h
  have hA : A = (fun x => (fun i => decide (0 ≤ MvPolynomial.eval x (p i)))) ⁻¹'
      {v | b v = true} := by
    ext x
    simp [hb x]
  rw [hA]
  have hm : Measurable fun x : Fin n → ℝ => (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) := by
    refine Measurable.of_eval fun i => ?_
    have hc : Measurable fun x : Fin n → ℝ => MvPolynomial.eval x (p i) :=
      (MvPolynomial.continuous_eval (p i)).measurable
    refine measurable_to_bool ?_
    have : (fun x : Fin n → ℝ => decide (0 ≤ MvPolynomial.eval x (p i))) ⁻¹' {true} =
        {x | 0 ≤ MvPolynomial.eval x (p i)} := by
      ext x
      simp
    rw [this]
    exact measurableSet_le measurable_const hc
  exact hm (Set.toFinite _).measurableSet

end Submission.Lib.K4XInterface

namespace Submission.Lib.K4XInterface

open Classical in
/-- Counting refined labels: labels over a list `S` of old labels, with at most `K'` refined
labels per old label, number at most `|S| K'`. -/
theorem card_filter_le_of_fibers {ι β : Type} [Fintype ι] (π : ι → β) (P Q : ι → Prop)
    (S : Finset β) (hPQ : ∀ i, P i → π i ∈ S ∧ Q i) (K' : ℕ)
    (hfib : ∀ b ∈ S, (Finset.univ.filter (fun i => π i = b ∧ Q i)).card ≤ K') :
    (Finset.univ.filter P).card ≤ S.card * K' := by
  have hsub : Finset.univ.filter P ⊆
      S.biUnion (fun b => Finset.univ.filter (fun i => π i = b ∧ Q i)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hS, hQ⟩ := hPQ i hi
    exact Finset.mem_biUnion.mpr ⟨π i, hS, by simp [hQ]⟩
  calc (Finset.univ.filter P).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ S, (Finset.univ.filter (fun i => π i = b ∧ Q i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ S, K' := Finset.sum_le_sum hfib
    _ = S.card * K' := by rw [Finset.sum_const, smul_eq_mul]

/-- Path lists read through the terminal observation: the level-`i` path charts of a world met
by a terminal observation `o` lie in the level-`i` list of the coarsened observation. -/
theorem path_charts_met_subset {C : ℕ} {W : ℕ} (lev : Fin C → ℕ) (γ : Fin C → Fin W)
    (Bw : Fin W → ℝ) (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (r : ℕ → ℝ)
    (lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)) {N L : ℝ}
    (hN : 1 ≤ N)
    (hlst : ∀ b, ∀ p ∈ F b, b ∈ lst (lev b) (γ b) (gobs (Bw (γ b)) (gδ N (r (lev b))) p))
    (i : ℕ) (hr : 0 ≤ r i) (hrL : r i ≤ L) (γ₁ : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ)
    (b : Fin C) (hb : lev b = i ∧ γ b = γ₁ ∧ ∃ p ∈ F b, gobs (Bw γ₁) (gδ N L) p = o) :
    b ∈ lst i γ₁ (coarsenObs (depthIdx N L - depthIdx N (r i)) o) := by
  obtain ⟨hlev, hγ, p, hp, hpo⟩ := hb
  have h := hlst b p hp
  rw [hlev, hγ, gobs_coarsen hN hr hrL, hpo] at h
  exact h

end Submission.Lib.K4XInterface
