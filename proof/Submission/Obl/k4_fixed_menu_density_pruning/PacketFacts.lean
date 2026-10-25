import Submission.Obl.k4_fixed_menu_density_pruning.ParentIncidences

namespace Submission.Obl.k4_fixed_menu_density_pruning

open MeasureTheory Set

/-- Open time blocks and same-block line disjointness make a whole level disjoint. -/
theorem level_interior_disjoint {X Γ : Type*} {C : ℕ}
    (lev : Fin C → ℕ) (γ : Fin C → Γ) (j : Fin C → ℕ) (T : ℕ → ℕ)
    (A : Fin C → Set X) (F : Fin C → Set (X × ℝ)) (i : ℕ)
    (hF : ∀ b, ∀ p ∈ F b, p.1 ∈ A b)
    (hd : ∀ b b', b ≠ b' → lev b = lev b' → γ b = γ b' → j b = j b' →
      Disjoint (A b) (A b')) :
    ∀ b b', b ≠ b' → γ b = γ b' →
      Disjoint
        (if lev b = i then F b ∩ {p | p.2 ∈ Ioo ((j b : ℝ) / (2 : ℝ) ^ T i)
          (((j b : ℝ) + 1) / (2 : ℝ) ^ T i)} else ∅)
        (if lev b' = i then F b' ∩ {p | p.2 ∈ Ioo ((j b' : ℝ) / (2 : ℝ) ^ T i)
          (((j b' : ℝ) + 1) / (2 : ℝ) ^ T i)} else ∅) := by
  intro b b' hne hγ
  split_ifs with hb hb'
  · apply Set.disjoint_left.mpr
    intro p hp hp'
    have hj : j b = j b' := time_cell_unique (by positivity) hp.2
      ⟨hp'.2.1.le, hp'.2.2.le⟩
    exact Set.disjoint_left.mp (hd b b' hne (hb.trans hb'.symm) hγ hj)
      (hF b p hp.1) (hF b' p hp'.1)
  all_goals simp

/-- A finite time block has finite mass under a probability trajectory law. -/
theorem mass_ne_top_of_time_block {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] {S : Set (X × ℝ)} {a b : ℝ}
    (hS : ∀ p ∈ S, p.2 ∈ Icc a b) : (ν.prod volume) S ≠ ⊤ := by
  apply ne_top_of_le_ne_top (b := (ν.prod volume) (univ ×ˢ Icc a b))
  · rw [Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  · exact measure_mono (fun p hp => ⟨Set.mem_univ _, hS p hp⟩)

/-- Halving the scalar floor places the factor two in the full time denominator. -/
theorem ofReal_half_div (a b : ℝ) :
    ENNReal.ofReal (a / (2 * b)) =
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (a / b) := by
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

/-- The same subset relation lets a retained original law inherit a cap. -/
theorem retained_map_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) {E Good S : Set X} (hGood : MeasurableSet Good)
    (hsub : S ⊆ E ∩ Good)
    (o : X → Y) (ho : Measurable o) (ref : Measure Y) (H : ENNReal)
    (hcap : ((μ.restrict E).restrict Good).map o ≤ H • ref) :
    (μ.restrict S).map o ≤ H • ref := by
  apply le_trans ?_ hcap
  apply Measure.map_mono
  · rw [Measure.restrict_restrict hGood]
    exact Measure.restrict_mono
      (show S ⊆ Good ∩ E from fun _ hp => ⟨(hsub hp).2, (hsub hp).1⟩) le_rfl
  · exact ho

end Submission.Obl.k4_fixed_menu_density_pruning
