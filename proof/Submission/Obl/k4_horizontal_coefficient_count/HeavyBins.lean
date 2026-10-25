import Submission.Obl.k4_horizontal_coefficient_count.Binning

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

def horizontalCell {α : Type*} (b : α → Fin 6 → ℝ) (G : Set α) (χ a : ℝ)
    (q : Fin 5 → ℤ) : Set α := {l | l ∈ G ∧ horizontalCode χ a (b l) = q}

def codeWeight (π : Measure ℝ) (χ a d Z : ℝ) (q : Fin 5 → ℤ) : ENNReal :=
  ENNReal.ofReal (a ^ 2 * a ^ d / Z) *
    π (Ico ((q 0 : ℝ) * χ) (((q 0 : ℝ) + 1) * χ))

def lightCells {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (π : Measure ℝ) (b : α → Fin 6 → ℝ) (G : Set α) (χ a d Z : ℝ) : Set (α × ℝ) :=
  {p | p.1 ∈ G ∧ μ (horizontalCell b G χ a (horizontalCode χ a (b p.1)) ×ˢ univ) <
    codeWeight π χ a d Z (horizontalCode χ a (b p.1))}

/-- Any finite set of occupied heavy cells provides a heavy predictor
family. Empty and null cells need no special convention. -/
theorem heavy_binned_family {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (π : Measure ℝ) (b : α → Fin 6 → ℝ) (hb : Measurable b)
    (G : Set α) (hG : MeasurableSet G)
    {χ a L C M d Z : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hC : L ≤ C)
    (hM : 2 * L ≤ M) (hM2 : 2 ≤ M)
    (hbound : ∀ l ∈ G, |b l 2| ≤ L ∧ |b l 5| ≤ L)
    (hfinite : (horizontalCode χ a ∘ b '' G).Finite)
    (htime : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0)
    (hgood : μ (Prod.fst ⁻¹' G)ᶜ = 0) :
    ∃ f : PredictorFamily b χ a a C M, f.Floors π d Z μ ∧
      μ {p | ∃ i, p.1 ∈ f.A i}ᶜ ≤ μ (lightCells μ π b G χ a d Z) := by
  classical
  let Q₀ : Finset (Fin 5 → ℤ) := hfinite.toFinset
  let Q : Finset (Fin 5 → ℤ) := Q₀.filter (fun q => codeWeight π χ a d Z q ≤
    μ (horizontalCell b G χ a q ×ˢ univ))
  have hQ : (Q : Set (Fin 5 → ℤ)) ⊆ horizontalCode χ a ∘ b '' G := by
    intro q hq
    exact hfinite.mem_toFinset.mp (Finset.mem_filter.mp hq).1
  let f := binnedFamily b hb G hG ha hL hC hM hM2 hbound Q hQ
  refine ⟨f, ?_, ?_⟩
  · intro i
    let q : Q := Q.equivFin.symm i
    have hheavy := (Finset.mem_filter.mp q.property).2
    have htimecell : μ (horizontalCell b G χ a q.val ×ˢ univ) =
        μ (horizontalCell b G χ a q.val ×ˢ Icc (0 : ℝ) 1) := by
      have h := measure_inter_conull (s := horizontalCell b G χ a q.val ×ˢ univ) htime
      simpa only [prod_inter_prod, inter_univ, univ_inter] using h.symm
    rw [htimecell] at hheavy
    exact hheavy
  · have hsub : {p | ∃ i, p.1 ∈ f.A i}ᶜ ⊆
        (Prod.fst ⁻¹' G)ᶜ ∪ lightCells μ π b G χ a d Z := by
      intro p hp
      by_cases hpg : p.1 ∈ G
      · right
        refine ⟨hpg, ?_⟩
        have hnot : horizontalCode χ a (b p.1) ∉ Q := by
          intro hcode
          exact hp ((binnedFamily_cover b hb G hG ha hL hC hM hM2 hbound Q hQ p.1).mpr
            ⟨hpg, hcode⟩)
        have hmem : horizontalCode χ a (b p.1) ∈ Q₀ :=
          hfinite.mem_toFinset.mpr ⟨p.1, hpg, rfl⟩
        exact lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hmem, h⟩))
      · exact Or.inl hpg
    calc
      _ ≤ μ ((Prod.fst ⁻¹' G)ᶜ ∪ lightCells μ π b G χ a d Z) := measure_mono hsub
      _ ≤ μ (Prod.fst ⁻¹' G)ᶜ + μ (lightCells μ π b G χ a d Z) := measure_union_le _ _
      _ = _ := by rw [hgood, zero_add]

end
end Submission.Obl.k4_horizontal_coefficient_count
