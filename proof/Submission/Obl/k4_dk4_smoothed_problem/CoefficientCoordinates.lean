/- Adapted within this LOT tree from o006/x0006, Submission/Obl/k4_core/Framework/CoefficientCoordinates.lean,
commit c0ee4c6. Prior attributions are retained below. -/

import Mathlib

/-!
# Packing independent intercept and slope coordinates into the native prior

The finite smoothing construction uses a pair of coordinate vectors. The frozen
native model uses one six-coordinate vector, optionally with an unobserved index.
The coordinate packing below preserves Lebesgue measure exactly.
-/

namespace Submission.Obl.k4_dk4_smoothed_problem.Framework

open Set MeasureTheory

/-- Concatenate the first and second coordinate blocks in their natural order. -/
noncomputable def concatenateCoefficients (m n : ℕ) :
    ((Fin m → ℝ) × (Fin n → ℝ)) ≃ᵐ (Fin (m + n) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv)

theorem concatenateCoefficients_castAdd {m n : ℕ}
    (p : (Fin m → ℝ) × (Fin n → ℝ)) (j : Fin m) :
    concatenateCoefficients m n p (Fin.castAdd n j) = p.1 j := by
  change (Equiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv)
    ((Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm p)
    (finSumFinEquiv (Sum.inl j)) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

theorem concatenateCoefficients_natAdd {m n : ℕ}
    (p : (Fin m → ℝ) × (Fin n → ℝ)) (j : Fin n) :
    concatenateCoefficients m n p (Fin.natAdd m j) = p.2 j := by
  change (Equiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv)
    ((Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm p)
    (finSumFinEquiv (Sum.inr j)) = _
  rw [Equiv.piCongrLeft_apply_apply]
  rfl

theorem measurePreserving_concatenateCoefficients (m n : ℕ) :
    MeasurePreserving (concatenateCoefficients m n) (volume.prod volume) volume := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin (m + n) => ℝ)
    finSumFinEquiv).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n => ℝ))

theorem concatenateCoefficients_symm_fst {m n : ℕ} (x : Fin (m + n) → ℝ) (j : Fin m) :
    ((concatenateCoefficients m n).symm x).1 j = x (Fin.castAdd n j) := by
  simpa using (concatenateCoefficients_castAdd ((concatenateCoefficients m n).symm x) j).symm

theorem concatenateCoefficients_symm_snd {m n : ℕ} (x : Fin (m + n) → ℝ) (j : Fin n) :
    ((concatenateCoefficients m n).symm x).2 j = x (Fin.natAdd m j) := by
  simpa using (concatenateCoefficients_natAdd ((concatenateCoefficients m n).symm x) j).symm

/-- Packing two coordinate boxes produces one coordinate box in the native model. -/
theorem preimage_prod_Icc_concatenateCoefficients {m n : ℕ}
    (b0 b1 : Fin m → ℝ) (s0 s1 : Fin n → ℝ) :
    (concatenateCoefficients m n).symm ⁻¹' (Icc b0 b1 ×ˢ Icc s0 s1) =
      Icc (concatenateCoefficients m n (b0, s0)) (concatenateCoefficients m n (b1, s1)) := by
  ext x
  change (((concatenateCoefficients m n).symm x).1 ∈ Icc b0 b1 ∧
    ((concatenateCoefficients m n).symm x).2 ∈ Icc s0 s1) ↔ _
  constructor
  · rintro ⟨⟨hb0, hb1⟩, ⟨hs0, hs1⟩⟩
    constructor
    · intro i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      cases j with
      | inl j => simpa [concatenateCoefficients_castAdd,
          concatenateCoefficients_symm_fst] using hb0 j
      | inr j => simpa [concatenateCoefficients_natAdd,
          concatenateCoefficients_symm_snd] using hs0 j
    · intro i
      obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
      cases j with
      | inl j => simpa [concatenateCoefficients_castAdd,
          concatenateCoefficients_symm_fst] using hb1 j
      | inr j => simpa [concatenateCoefficients_natAdd,
          concatenateCoefficients_symm_snd] using hs1 j
  · rintro ⟨h0, h1⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro j
      simpa [concatenateCoefficients_castAdd, concatenateCoefficients_symm_fst] using
        h0 (Fin.castAdd n j)
    · intro j
      simpa [concatenateCoefficients_castAdd, concatenateCoefficients_symm_fst] using
        h1 (Fin.castAdd n j)
    · intro j
      simpa [concatenateCoefficients_natAdd, concatenateCoefficients_symm_snd] using
        h0 (Fin.natAdd m j)
    · intro j
      simpa [concatenateCoefficients_natAdd, concatenateCoefficients_symm_snd] using
        h1 (Fin.natAdd m j)

/-- Independent Lebesgue restrictions become a single native coefficient-volume
restriction under coordinate concatenation. -/
theorem map_prod_restrict_concatenateCoefficients {m n : ℕ}
    (A : Set (Fin m → ℝ)) (B : Set (Fin n → ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((volume.restrict A).prod (volume.restrict B)).map (concatenateCoefficients m n) =
      volume.restrict ((concatenateCoefficients m n).symm ⁻¹' (A ×ˢ B)) := by
  let e := concatenateCoefficients m n
  have hS : MeasurableSet (e.symm ⁻¹' (A ×ˢ B)) := e.symm.measurable (hA.prod hB)
  have he := measurePreserving_concatenateCoefficients m n
  rw [Measure.prod_restrict]
  have h := Measure.restrict_map (μ := (volume : Measure (Fin m → ℝ)).prod volume) e.measurable hS
  rw [he.map_eq] at h
  have hp : e ⁻¹' (e.symm ⁻¹' (A ×ˢ B)) = A ×ˢ B := by
    ext p
    simp
  rw [hp] at h
  exact h.symm

/-- Packing independent constant-density pieces multiplies their density heights. -/
theorem map_weighted_prod_restrict_concatenateCoefficients {m n : ℕ}
    (A : Set (Fin m → ℝ)) (B : Set (Fin n → ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (c d : ENNReal) :
    ((c • volume.restrict A).prod (d • volume.restrict B)).map
      (concatenateCoefficients m n) =
      (c * d) • volume.restrict ((concatenateCoefficients m n).symm ⁻¹' (A ×ˢ B)) := by
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul _ (concatenateCoefficients m n).measurable.aemeasurable,
    map_prod_restrict_concatenateCoefficients A B hA hB]

/-- A packed component at an unobserved natural index has exactly the finite
coefficient-volume representation required by the native model. -/
theorem map_labeled_prod_restrict_concatenateCoefficients {m n : ℕ}
    (i : ℕ) (A : Set (Fin m → ℝ)) (B : Set (Fin n → ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((volume.restrict A).prod (volume.restrict B)).map
      (fun p => (i, concatenateCoefficients m n p)) =
      (volume.restrict ((concatenateCoefficients m n).symm ⁻¹' (A ×ˢ B))).map
        (fun x => (i, x)) := by
  rw [← map_prod_restrict_concatenateCoefficients A B hA hB]
  have hf : Measurable (fun x : Fin (m + n) → ℝ => (i, x)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using
    (Measure.map_map (μ := (volume.restrict A).prod (volume.restrict B))
      (f := concatenateCoefficients m n) (g := fun x => (i, x)) hf
      (concatenateCoefficients m n).measurable).symm

/-- Finite constant-density mixtures on independent intercept/slope boxes
become finite sums of coefficient-volume restrictions, with the same weights. -/
theorem map_finite_product_prior {m n h : ℕ} (i : ℕ)
    (A : Fin h → Set (Fin m → ℝ)) (B : Fin h → Set (Fin n → ℝ))
    (hA : ∀ j, MeasurableSet (A j)) (hB : ∀ j, MeasurableSet (B j)) (c : Fin h → ENNReal) :
    (∑ j : Fin h, c j • (volume.restrict (A j)).prod (volume.restrict (B j))).map
      (fun p => (i, concatenateCoefficients m n p)) =
      ∑ j : Fin h, c j •
        (volume.restrict ((concatenateCoefficients m n).symm ⁻¹' (A j ×ˢ B j))).map
          (fun x => (i, x)) := by
  have hf : Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      (i, concatenateCoefficients m n p)) :=
    measurable_const.prodMk (concatenateCoefficients m n).measurable
  rw [Measure.map_finset_sum' hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_smul _ hf.aemeasurable,
    map_labeled_prod_restrict_concatenateCoefficients i (A j) (B j) (hA j) (hB j)]

end Submission.Obl.k4_dk4_smoothed_problem.Framework
