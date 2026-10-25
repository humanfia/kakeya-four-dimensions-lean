import Submission.Lib.K4FinitePlankAtlases.Assignments

namespace Submission.Obl.k4_stable_native_signal_oscillation
open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4FinitePlankAtlases

/-- Remove light candidates and assign every surviving point to its first retained candidate.
The mass is charged to the original candidates, before priority assignment. -/
lemma retain_heavy_cover {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {n : ℕ} (U : Fin n → Set X)
    (hU : ∀ i, MeasurableSet (U i)) (η δ : ℝ≥0∞)
    (hcover : μ (⋃ i, U i)ᶜ ≤ δ) :
    ∃ E : Fin n → Set X,
      (∀ i, MeasurableSet (E i)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (∀ i, E i ⊆ U i) ∧
      (∀ i, (E i).Nonempty → η ≤ μ (U i)) ∧
      μ (⋃ i, E i)ᶜ ≤ δ + (n : ℝ≥0∞) * η := by
  classical
  let V : Fin n → Set X := fun i => if η ≤ μ (U i) then U i else ∅
  have hV (i : Fin n) : MeasurableSet (V i) := by
    dsimp [V]
    split_ifs <;> simp_all
  refine ⟨firstAssignment V, measurableSet_firstAssignment V hV,
    firstAssignment_disjoint V, ?_, ?_, ?_⟩
  · intro i x hx
    have hv := hx.1
    dsimp [V] at hv
    split_ifs at hv with hi
    · exact hv
    · exact False.elim hv
  · intro i ⟨x, hx⟩
    have hv := hx.1
    dsimp [V] at hv
    split_ifs at hv with hi
    · exact hi
    · exact False.elim hv
  · rw [iUnion_firstAssignment]
    let W : Fin n → Set X := fun i => if η ≤ μ (U i) then ∅ else U i
    have hW (i : Fin n) : μ (W i) ≤ η := by
      dsimp [W]
      split_ifs with hi
      · simp
      · exact le_of_lt (lt_of_not_ge hi)
    have hsub : (⋃ i, V i)ᶜ ⊆ (⋃ i, U i)ᶜ ∪ ⋃ i, W i := by
      intro x hx
      by_cases hxu : x ∈ ⋃ i, U i
      · right
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxu
        apply mem_iUnion.mpr
        refine ⟨i, ?_⟩
        have hlight : ¬η ≤ μ (U i) := by
          intro hh
          exact hx (mem_iUnion.mpr ⟨i, by simpa [V, hh] using hi⟩)
        simpa [W, hlight] using hi
      · exact Or.inl hxu
    calc
      μ (⋃ i, V i)ᶜ ≤ μ ((⋃ i, U i)ᶜ ∪ ⋃ i, W i) := measure_mono hsub
      _ ≤ μ (⋃ i, U i)ᶜ + μ (⋃ i, W i) := measure_union_le _ _
      _ ≤ δ + ∑ i, μ (W i) := by
        exact add_le_add hcover (by simpa using measure_iUnion_le W)
      _ ≤ δ + ∑ _i : Fin n, η := by gcongr with i; exact hW i
      _ = δ + (n : ℝ≥0∞) * η := by simp

/-- Approximation to one Lipschitz graph gives the required pairwise signal estimate. -/
lemma signal_oscillation_of_graph {X Y : Type*} [SeminormedAddCommGroup Y]
    (base : X → Y) (signal : X → ℝ) (graph : Y → ℝ) {p q : X} {M L a : ℝ}
    (hp : |signal p - graph (base p)| ≤ M * a)
    (hq : |signal q - graph (base q)| ≤ M * a)
    (hgraph : |graph (base p) - graph (base q)| ≤ L * ‖base p - base q‖) :
    |signal p - signal q| ≤ 2 * M * a + L * ‖base p - base q‖ := by
  calc
    _ = |(signal p - graph (base p)) + (graph (base p) - graph (base q)) +
        (graph (base q) - signal q)| := by congr 1; ring
    _ ≤ |signal p - graph (base p)| + |graph (base p) - graph (base q)| +
        |graph (base q) - signal q| := (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M * a + L * ‖base p - base q‖ + M * a := by
      rw [abs_sub_comm (graph (base q)) (signal q)]
      gcongr
    _ = 2 * M * a + L * ‖base p - base q‖ := by ring

/-- Convert locally fitted graphs on heavy original candidates into a disjoint
measurable partition, losing at most the number of candidates times the mass threshold. -/
lemma partition_of_signal_graphs {X Y : Type*} [MeasurableSpace X]
    [SeminormedAddCommGroup Y] (μ : Measure X) {n : ℕ}
    (U : Fin n → Set X) (hU : ∀ i, MeasurableSet (U i))
    (η δ : ℝ≥0∞) (hcover : μ (⋃ i, U i)ᶜ ≤ δ)
    (base : X → Y) (signal : X → ℝ) (M L a : ℝ)
    (hfit : ∀ i, η ≤ μ (U i) → ∃ graph : Y → ℝ,
      (∀ p ∈ U i, |signal p - graph (base p)| ≤ M * a) ∧
      ∀ p ∈ U i, ∀ q ∈ U i,
        |graph (base p) - graph (base q)| ≤ L * ‖base p - base q‖) :
    ∃ E : Fin n → Set X,
      (∀ i, MeasurableSet (E i)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      μ (⋃ i, E i)ᶜ ≤ δ + (n : ℝ≥0∞) * η ∧
      ∀ i, ∀ p ∈ E i, ∀ q ∈ E i,
        |signal p - signal q| ≤ 2 * M * a + L * ‖base p - base q‖ := by
  obtain ⟨E, hEm, hEd, hEU, hEh, hmass⟩ := retain_heavy_cover μ U hU η δ hcover
  refine ⟨E, hEm, hEd, hmass, ?_⟩
  intro i p hp q hq
  obtain ⟨graph, hgraph, hlip⟩ := hfit i (hEh i ⟨p, hp⟩)
  exact signal_oscillation_of_graph base signal graph
    (hgraph p (hEU i hp)) (hgraph q (hEU i hq))
    (hlip p (hEU i hp) q (hEU i hq))

end Submission.Obl.k4_stable_native_signal_oscillation
