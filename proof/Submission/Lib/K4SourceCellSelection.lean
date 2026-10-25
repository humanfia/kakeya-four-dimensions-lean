-- Adapted from: here:o049
-- Original cell-selection and decoder-count kernels by x0147.
import Mathlib
import Submission.Lib.K4RefinedLabelFloors

/-!
# Original source cell selection

Certify arbitrary finite cell tables while charging their uncovered ORIGINAL
source mass once; use original positive-mass witnesses to pass from an a.e.
cell decoder to a finite group-cell count. No posterior normalization occurs.
-/

namespace Submission.Lib.K4SourceCellSelection

/- Adapted from here:o049, x0147, commit ae53374,
   Submission/Obl/k4_cap_class_terminal_charts/CellGroupCount.lean. -/
open Set
open scoped BigOperators

/-- Cellwise compatible lists bound the total number of group-cell pairs,
regardless of the total number of groups. -/
theorem compatible_cell_pairs_card {G C : Type*} (F : Finset C)
    (pairs : Finset (G × C)) (L : C → Finset G) {R : ℝ}
    (hcover : ∀ p ∈ pairs, p.2 ∈ F ∧ p.1 ∈ L p.2)
    (hlist : ∀ c ∈ F, ((L c).card : ℝ) ≤ R) :
    (pairs.card : ℝ) ≤ R * (F.card : ℝ) := by
  classical
  let S := (F.sigma L).image (fun p : (c : C) × G => (p.2, p.1))
  have hsub : pairs ⊆ S := by
    intro p hp
    have h := hcover p hp
    exact Finset.mem_image.mpr ⟨⟨p.2, p.1⟩, Finset.mem_sigma.mpr h, rfl⟩
  have hc : pairs.card ≤ (F.sigma L).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  calc
    (pairs.card : ℝ) ≤ ((F.sigma L).card : ℝ) := by exact_mod_cast hc
    _ = ∑ c ∈ F, ((L c).card : ℝ) := by rw [Finset.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _c ∈ F, R := Finset.sum_le_sum hlist
    _ = R * (F.card : ℝ) := by simp [mul_comm]

/- Adapted from here:o049, x0147, commit ae53374,
   Submission/Obl/k4_cap_class_terminal_charts/CertifiedCellPairs.lean. -/
open Set MeasureTheory

/-- A positive original source cell has a witness outside every null
exception, so an a.e. decoder also covers every certified cell label. -/
theorem cell_label_mem_of_nonzero_mass {Z I J : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (code : Z → I) (cell : Z → J) (L : J → Finset I)
    (hsrc : ∀ᵐ z ∂μ, code z ∈ L (cell z)) (i : I) (j : J)
    (hmass : μ {z | code z = i ∧ cell z = j} ≠ 0) : i ∈ L j := by
  classical
  by_contra hi
  apply hmass
  apply measure_mono_null ?_ (ae_iff.mp hsrc)
  intro z hz
  change code z = i ∧ cell z = j at hz
  change code z ∉ L (cell z)
  rw [hz.1, hz.2]
  exact hi

/-- Original positive-mass witnesses turn an a.e. cell decoder into the
finite group-cell count, without exposing the null pruning mask. -/
theorem positive_cell_pairs_card {Z I J : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (code : Z → I) (cell : Z → J) (L : J → Finset I)
    (hsrc : ∀ᵐ z ∂μ, code z ∈ L (cell z))
    (F : Finset J) (pairs : Finset (I × J))
    (hcover : ∀ p ∈ pairs, p.2 ∈ F)
    (hmass : ∀ p ∈ pairs, μ {z | code z = p.1 ∧ cell z = p.2} ≠ 0)
    {R : ℝ} (hlist : ∀ j ∈ F, ((L j).card : ℝ) ≤ R) :
    (pairs.card : ℝ) ≤ R * (F.card : ℝ) := by
  apply compatible_cell_pairs_card F pairs L ?_ hlist
  intro p hp
  exact ⟨hcover p hp, cell_label_mem_of_nonzero_mass μ code cell L hsrc p.1 p.2 (hmass p hp)⟩

/- Adapted from here:o049, x0147, commit ae53374,
   Submission/Obl/k4_cap_class_terminal_charts/SourceCellTails.lean. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
open Submission.Lib.K4RefinedLabelFloors

/-- Cell certification on an arbitrary finite table loses its uncovered
ORIGINAL source mass once. No density law for a renormalized restriction is
needed, and the averaging error is not divided by cell volume. -/
theorem refined_original_source_cells_with_tail {Z X I J : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [Fintype I]
    (μ : Measure Z) [IsFiniteMeasure μ] (lam : Measure X) [SigmaFinite lam]
    (obs : Z → X) (hobs : Measurable obs)
    (code : Z → I) (hcode : ∀ i, MeasurableSet {z | code z = i})
    (g h : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (hh : ∀ i, Measurable (h i))
    (hg0 : ∀ i x, 0 ≤ g i x)
    (hlaw : ∀ i, (μ.restrict {z | code z = i}).map obs =
      lam.withDensity (fun x => ENNReal.ofReal (g i x)))
    (G : X → ENNReal) (hG : Measurable G) (hfull : μ.map obs = lam.withDensity G)
    (L : X → Finset I) (hmL : ∀ i, MeasurableSet {x | i ∈ L x})
    {R : ℝ} (hR : 0 < R) (hL : ∀ x, ((L x).card : ℝ) ≤ R)
    (hcompat : ∀ᵐ z ∂μ, code z ∈ L (obs z))
    (F : I → Finset J) (C : I → J → Set X)
    (hC : ∀ i j, j ∈ F i → MeasurableSet (C i j))
    (hdisj : ∀ i, (↑(F i) : Set J).PairwiseDisjoint (C i))
    (a v : I → J → ℝ) (hv : ∀ i j, j ∈ F i → 0 ≤ v i j)
    (hvolume : ∀ i j, j ∈ F i → lam (C i j) = ENNReal.ofReal (v i j))
    (hconstant : ∀ i j, j ∈ F i → ∀ x ∈ C i j, h i x = a i j)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ Good : I → Finset J,
      (∀ i, Good i ⊆ F i) ∧
      (∀ i j, j ∈ Good i → ENNReal.ofReal (ε * ρ * v i j / (4 * R)) ≤
        μ {z | code z = i ∧ obs z ∈ C i j}) ∧
      μ {z | ENNReal.ofReal ρ ≤ G (obs z) ∧ obs z ∉ ⋃ j ∈ Good (code z), C (code z) j} ≤
        ENNReal.ofReal ε * μ univ +
          3 * ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam +
            μ {z | obs z ∉ ⋃ j ∈ F (code z), C (code z) j} := by
  classical
  let τ := ε * ρ / (2 * R)
  let UF (i : I) := ⋃ j ∈ F i, C i j
  let Err := ∑ i, ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hcert (i : I) : ∃ Good : Finset J, Good ⊆ F i ∧
      (∀ j ∈ Good, ENNReal.ofReal (τ * v i j / 2) ≤
        (lam.withDensity (fun x => ENNReal.ofReal (g i x))) (C i j)) ∧
      (lam.withDensity (fun x => ENNReal.ofReal (g i x)))
        {x | x ∈ UF i ∧ τ ≤ h i x ∧ x ∉ ⋃ j ∈ Good, C i j} ≤
          ∫⁻ x, ENNReal.ofReal |g i x - h i x| ∂lam := by
    haveI : IsFiniteMeasure (lam.withDensity (fun x => ENNReal.ofReal (g i x))) := by
      rw [← hlaw i]
      infer_instance
    exact exists_original_cell_certificates lam (g i) (h i) (hg i) (hg0 i)
      (F i) (C i) (hC i) (hdisj i) (a i) (hconstant i) hτ.le (v i) (hv i) (hvolume i)
  choose Good hGood hfloor herr using hcert
  let UG (i : I) := ⋃ j ∈ Good i, C i j
  refine ⟨Good, hGood, ?_, ?_⟩
  · intro i j hj
    have heq : (lam.withDensity (fun x => ENNReal.ofReal (g i x))) (C i j) =
        μ {z | code z = i ∧ obs z ∈ C i j} := by
      rw [← hlaw i, Measure.map_apply hobs (hC i j (hGood i hj)),
        Measure.restrict_apply (hobs (hC i j (hGood i hj)))]
      congr 1
      ext z
      change (obs z ∈ C i j ∧ code z = i) ↔ (code z = i ∧ obs z ∈ C i j)
      exact and_comm
    calc
      _ = ENNReal.ofReal (τ * v i j / 2) := by
        congr 1
        dsimp [τ]
        field_simp <;> ring
      _ ≤ _ := (hfloor i j hj).trans_eq heq
  · let Low : Set Z := {z | ENNReal.ofReal ρ ≤ G (obs z) ∧ h (code z) (obs z) < τ}
    let ErrorCells : Set Z :=
      {z | obs z ∈ UF (code z) ∧ τ ≤ h (code z) (obs z) ∧ obs z ∉ UG (code z)}
    let Outside : Set Z := {z | obs z ∉ UF (code z)}
    have hlow : μ Low ≤ ENNReal.ofReal ε * μ univ + 2 * Err :=
      refined_label_source_floor_ennreal μ lam obs hobs code hcode g h hg hh hg0 hlaw
        G hG hfull L hmL hR hL hcompat hε hρ
    have hmeas (i : I) : MeasurableSet {x | x ∈ UF i ∧ τ ≤ h i x ∧ x ∉ UG i} := by
      have hUF : MeasurableSet (UF i) := MeasurableSet.biUnion (F i).countable_toSet (hC i)
      have hUG : MeasurableSet (UG i) := MeasurableSet.biUnion (Good i).countable_toSet
        (fun j hj => hC i j (hGood i hj))
      exact hUF.inter ((measurableSet_le measurable_const (hh i)).inter hUG.compl)
    have herror : μ ErrorCells ≤ Err := by
      change μ {z | obs z ∈ {x | x ∈ UF (code z) ∧ τ ≤ h (code z) x ∧ x ∉ UG (code z)}} ≤ _
      rw [finite_label_source_formula μ lam obs hobs code hcode g hlaw
        (fun i => {x | x ∈ UF i ∧ τ ≤ h i x ∧ x ∉ UG i}) hmeas]
      exact Finset.sum_le_sum (fun i _ => herr i)
    have hsub : {z | ENNReal.ofReal ρ ≤ G (obs z) ∧ obs z ∉ UG (code z)} ⊆
        (Low ∪ ErrorCells) ∪ Outside := by
      intro z hz
      change ENNReal.ofReal ρ ≤ G (obs z) ∧ obs z ∉ UG (code z) at hz
      by_cases hF : obs z ∈ UF (code z)
      · by_cases hs : h (code z) (obs z) < τ
        · exact Or.inl (Or.inl ⟨hz.1, hs⟩)
        · exact Or.inl (Or.inr ⟨hF, le_of_not_gt hs, hz.2⟩)
      · exact Or.inr hF
    calc
      _ ≤ μ ((Low ∪ ErrorCells) ∪ Outside) := measure_mono hsub
      _ ≤ (μ Low + μ ErrorCells) + μ Outside :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ((ENNReal.ofReal ε * μ univ + 2 * Err) + Err) + μ Outside :=
        add_le_add (add_le_add hlow herror) le_rfl
      _ = _ := by dsimp [Err, Outside, UF]; ring

end Submission.Lib.K4SourceCellSelection
