/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/SourceSheetFamilies.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetJets

/-! Stable sheet families built at actual points of original witnesses. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

/-- An almost-everywhere source property may be imposed pointwise on a
measurable full-mass core, even if the predicate itself is not measurable. -/
theorem measurable_full_source {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Ω → Prop) (hP : ∀ᵐ p ∂μ, P p) :
    ∃ G : Set Ω, MeasurableSet G ∧ μ Gᶜ = 0 ∧ ∀ p ∈ G, P p := by
  let E : Set Ω := {p | ¬ P p}
  refine ⟨(toMeasurable μ E)ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · simpa only [compl_compl, measure_toMeasurable] using ae_iff.mp hP
  · intro p hp
    by_contra h
    exact hp (subset_toMeasurable μ E h)

structure OriginalSheetFamily {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D : ℕ) (a : ℝ) (K : NNReal)
    (base : Ω → EuclideanSpace ℝ (Fin 3)) (signal : Ω → ℝ) where
  n : ℕ
  index : Ω → Fin n
  measurable_index : Measurable index
  witness : Fin n → Set Ω
  measurable_witness : ∀ i, MeasurableSet (witness i)
  disjoint_witness : Pairwise (fun i j => Disjoint (witness i) (witness j))
  assigned : ∀ᵐ p ∂μ, p ∈ witness (index p)
  source_norm : ∀ i p, p ∈ witness i → ‖base p‖ ≤ 1 / 8
  f : Fin n → EuclideanSpace ℂ (Fin 3) → ℂ
  sheet : ∀ i, IsSheet D (f i)
  lipschitz : ∀ i, LipschitzOnWith K (fun x => f i (emb x)) (closedBall 0 (1 / 2))
  fit : ∀ i p, p ∈ witness i → ‖(signal p : ℂ) - f i (emb (base p))‖ ≤ a / 4

/-- Impose an additional measurable full source core without changing any
candidate function, index or original family count. -/
def OriginalSheetFamily.trim {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {D : ℕ} {a : ℝ} {K : NNReal}
    {base : Ω → EuclideanSpace ℝ (Fin 3)} {signal : Ω → ℝ}
    (F : OriginalSheetFamily μ D a K base signal) (G : Set Ω) (hG : MeasurableSet G)
    (hfull : ∀ᵐ p ∂μ, p ∈ G) : OriginalSheetFamily μ D a K base signal :=
  { F with
    witness := fun i => F.witness i ∩ G
    measurable_witness := fun i => (F.measurable_witness i).inter hG
    disjoint_witness := fun i j hij => Set.disjoint_left.mpr fun p hp hq =>
      Set.disjoint_left.mp (F.disjoint_witness hij) hp.1 hq.1
    assigned := F.assigned.and hfull
    source_norm := fun i p hp => F.source_norm i p hp.1
    fit := fun i p hp => F.fit i p hp.1 }

def witnessCandidate {Ω : Type*} {n : ℕ} (W : Fin n → Set Ω)
    (candidate : Fin n → EuclideanSpace ℂ (Fin 3) → ℂ) (i : Fin n) :
    EuclideanSpace ℂ (Fin 3) → ℂ := by
  classical
  exact if (W i).Nonempty then candidate i else fun _ => 0

theorem witnessCandidate_eq {Ω : Type*} {n : ℕ} (W : Fin n → Set Ω)
    (candidate : Fin n → EuclideanSpace ℂ (Fin 3) → ℂ) {i : Fin n} {p : Ω} (hp : p ∈ W i) :
    witnessCandidate W candidate i = candidate i := by
  classical
  simp only [witnessCandidate, ite_eq_left (show (W i).Nonempty from ⟨p, hp⟩)]

/-- A local stable-sheet constructor at one actual witness point supplies the
whole finite family. Empty witnesses use the zero sheet and add no source mass. -/
def originalSheetFamilyOfPointRules {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {D n : ℕ} (hD : 1 ≤ D) (a : ℝ) (K : NNReal)
    (base : Ω → EuclideanSpace ℝ (Fin 3)) (signal : Ω → ℝ)
    (index : Ω → Fin n) (hindex : Measurable index)
    (W : Fin n → Set Ω) (hW : ∀ i, MeasurableSet (W i))
    (hdisj : Pairwise (fun i j => Disjoint (W i) (W j)))
    (hassigned : ∀ᵐ p ∂μ, p ∈ W (index p))
    (hnorm : ∀ i p, p ∈ W i → ‖base p‖ ≤ 1 / 8)
    (candidate : Fin n → EuclideanSpace ℂ (Fin 3) → ℂ)
    (hrule : ∀ i p₀, p₀ ∈ W i →
      IsSheet D (candidate i) ∧ LipschitzOnWith K (fun x => candidate i (emb x)) (closedBall 0 (1 / 2)) ∧
      ∀ p ∈ W i, ‖(signal p : ℂ) - candidate i (emb (base p))‖ ≤ a / 4) :
    OriginalSheetFamily μ D a K base signal := by
  classical
  let f := witnessCandidate W candidate
  have hproperties (i : Fin n) :
      IsSheet D (f i) ∧ LipschitzOnWith K (fun x => f i (emb x)) (closedBall 0 (1 / 2)) ∧
      ∀ p ∈ W i, ‖(signal p : ℂ) - f i (emb (base p))‖ ≤ a / 4 := by
    dsimp only [f]
    by_cases hi : (W i).Nonempty
    · obtain ⟨p₀, hp₀⟩ := hi
      rw [witnessCandidate_eq W candidate hp₀]
      exact hrule i p₀ hp₀
    · simp only [witnessCandidate, ite_eq_right hi]
      refine ⟨isSheet_zero hD, ?_, ?_⟩
      · apply LipschitzOnWith.of_dist_le_mul
        intro x hx y hy
        simpa only [dist_self] using mul_nonneg (NNReal.coe_nonneg K) (dist_nonneg : 0 ≤ dist x y)
      · intro p hp
        exact (hi ⟨p, hp⟩).elim
  exact
    { n := n
      index := index
      measurable_index := hindex
      witness := W
      measurable_witness := hW
      disjoint_witness := hdisj
      assigned := hassigned
      source_norm := hnorm
      f := f
      sheet := fun i => (hproperties i).1
      lipschitz := fun i => (hproperties i).2.1
      fit := fun i => (hproperties i).2.2 }

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
