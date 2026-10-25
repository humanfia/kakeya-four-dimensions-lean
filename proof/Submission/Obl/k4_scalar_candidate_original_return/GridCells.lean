import Submission.Obl.k4_scalar_candidate_original_return.Prepared

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open Set MeasureTheory

noncomputable section

/-- Half-open base cells for the exact pure grid cap. -/
def scalarGridCell (h : ℝ) (q : Fin 2 → ℤ) : Set (Fin 2 → ℝ) :=
  {z | (fun i => (⌊z i / h⌋ : ℤ)) = q}

lemma scalarGridCell_eq_pi {h : ℝ} (hh : 0 < h) (q : Fin 2 → ℤ) :
    scalarGridCell h q = Set.pi univ
      (fun i => Ico ((q i : ℝ) * h) (((q i : ℝ) + 1) * h)) := by
  ext z
  simp only [scalarGridCell, mem_ofPred_eq, funext_iff, mem_pi, mem_univ, forall_const]
  apply forall_congr'
  intro i
  rw [Int.floor_eq_iff, le_div_iff₀ hh, div_lt_iff₀ hh]
  exact Iff.rfl

lemma scalarGridCell_measurable (h : ℝ) (q : Fin 2 → ℤ) :
    MeasurableSet (scalarGridCell h q) := by
  have hm : Measurable (fun z : Fin 2 → ℝ => fun i : Fin 2 => (⌊z i / h⌋ : ℤ)) := by
    fun_prop
  exact (measurableSet_singleton q).preimage hm

lemma scalarGridCell_disjoint (h : ℝ) :
    Pairwise (fun q q' : Fin 2 → ℤ => Disjoint (scalarGridCell h q) (scalarGridCell h q')) := by
  intro q q' hne
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact hne (hz.symm.trans hz')

lemma scalarGridCell_cover (h : ℝ) : (⋃ q : Fin 2 → ℤ, scalarGridCell h q) = univ := by
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨fun i => ⌊z i / h⌋, rfl⟩

lemma scalarGridCell_volume {h : ℝ} (hh : 0 < h) (q : Fin 2 → ℤ) :
    volume (scalarGridCell h q) = ENNReal.ofReal (h ^ 2) := by
  rw [scalarGridCell_eq_pi hh, Real.volume_pi_Ico]
  have hlen : ∀ i, (((q i : ℝ) + 1) * h - (q i : ℝ) * h) = h := by intro i; ring
  simp only [hlen, Fin.prod_univ_two, pow_two, ENNReal.ofReal_mul hh.le]

lemma scalarGridCell_distance {h : ℝ} (hh : 0 < h) {q : Fin 2 → ℤ}
    {z z' : Fin 2 → ℝ} (hz : z ∈ scalarGridCell h q) (hz' : z' ∈ scalarGridCell h q)
    (i : Fin 2) : |z i - z' i| ≤ h := by
  have hzi := Int.floor_eq_iff.mp (congrFun hz i)
  have hz'i := Int.floor_eq_iff.mp (congrFun hz' i)
  rw [le_div_iff₀ hh, div_lt_iff₀ hh] at hzi hz'i
  rw [abs_le]
  constructor <;> nlinarith only [hzi.1, hzi.2, hz'i.1, hz'i.2]

lemma baseBin_eq_iff_gridCell (N r : ℝ) (p : Inc) (q : Fin 2 → ℤ) :
    baseBin N r p = q ↔ (![p.2, y p.1 p.2] : Fin 2 → ℝ) ∈ scalarGridCell (N ^ (-r)) q := Iff.rfl

/-- Passing between a two-coordinate vector and an ordered pair preserves
outer Lebesgue mass, including sets assembled from charged cells. -/
lemma finTwoArrow_image_volume (S : Set (Fin 2 → ℝ)) :
    volume (MeasurableEquiv.finTwoArrow '' S : Set (ℝ × ℝ)) = volume S := by
  let e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.finTwoArrow
  have hpre : e ⁻¹' (e '' S) = S := e.injective.preimage_image S
  have h := (volume_preserving_finTwoArrow ℝ).measure_preimage_emb e.measurableEmbedding (e '' S)
  change volume (e ⁻¹' (e '' S)) = volume (e '' S) at h
  rw [hpre] at h
  exact h.symm

end

end Submission.Obl.k4_scalar_candidate_original_return
