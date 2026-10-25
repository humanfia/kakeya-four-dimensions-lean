-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/FloorCounting.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 3be7d21a,
-- Submission/Obl/k4_terminal_time_extension/FloorCounting.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_adapted_affine_cube_cover.Assembly

/-!
Counting old terminal labels using their original true floors.
No floor on a subsequently restricted paired-incidence entry is needed.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open MeasureTheory Set
open scoped ENNReal

variable {X T ι : Type*} [MeasurableSpace X] [MeasurableSpace T] [Fintype ι]

/-- In one old time block, disjoint trajectory assignments imply disjoint selected
incidences.  Their total mass is at most the mass of the original time block. -/
theorem sum_selectedMass_le_timeMass
    (ν : Measure X) (ρ : Measure T) [IsProbabilityMeasure ν] [SFinite ρ]
    (A : ι → Set X) (F : ι → Set (X × T)) (I : Set T)
    (hF : ∀ i, MeasurableSet (F i))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hsub : ∀ i, F i ⊆ A i ×ˢ I) :
    ∑ i, (ν.prod ρ) (F i) ≤ ρ I := by
  have hd : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact Set.disjoint_left.mp (hA hij) (hsub i hpi).1 (hsub j hpj).1
  have hb : ∀ i, F i ⊆ univ ×ˢ I := by
    intro i p hp
    exact ⟨mem_univ _, (hsub i hp).2⟩
  have hm := Submission.Obl.k4_adapted_affine_cube_cover.sum_restrict_le_of_disjoint
    (ν.prod ρ) F (univ ×ˢ I) hF hd hb
  have hh := hm univ
  simpa only [Measure.finsetSum_apply, Measure.restrict_apply_univ,
    Measure.prod_prod, measure_univ, one_mul] using hh

/-- A uniform positive original floor counts all old labels, regardless of the
masses of their later pair restrictions. -/
theorem card_mul_floor_le_timeMass
    (ν : Measure X) (ρ : Measure T) [IsProbabilityMeasure ν] [SFinite ρ]
    (A : ι → Set X) (F : ι → Set (X × T)) (I : Set T)
    (hF : ∀ i, MeasurableSet (F i))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hsub : ∀ i, F i ⊆ A i ×ˢ I)
    (a : ℝ≥0∞) (hfloor : ∀ i, a ≤ (ν.prod ρ) (F i)) :
    (Fintype.card ι : ℝ≥0∞) * a ≤ ρ I := by
  calc
    _ = ∑ _i : ι, a := by simp [nsmul_eq_mul]
    _ ≤ ∑ i, (ν.prod ρ) (F i) := Finset.sum_le_sum (fun i _ => hfloor i)
    _ ≤ ρ I := sum_selectedMass_le_timeMass ν ρ A F I hF hA hsub

/-- Real-valued label count.  In Lemma 3.5 the floor is `q₀*n_Q/K₀`,
and the time mass is `q₀`, so this gives the count `K₀/n_Q`. -/
theorem card_le_timeMass_div_floor
    (ν : Measure X) (ρ : Measure T) [IsProbabilityMeasure ν] [SFinite ρ]
    (A : ι → Set X) (F : ι → Set (X × T)) (I : Set T)
    (hF : ∀ i, MeasurableSet (F i))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hsub : ∀ i, F i ⊆ A i ×ˢ I)
    (hI : ρ I ≠ ∞) {a : ℝ} (ha : 0 < a)
    (hfloor : ∀ i, ENNReal.ofReal a ≤ (ν.prod ρ) (F i)) :
    (Fintype.card ι : ℝ) ≤ (ρ I).toReal / a := by
  have hh := card_mul_floor_le_timeMass ν ρ A F I hF hA hsub _ hfloor
  have hh' := ENNReal.toReal_mono hI hh
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal ha.le] at hh'
  exact (le_div_iff₀ ha).mpr hh'

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
