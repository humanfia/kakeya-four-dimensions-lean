-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Switch/LinearSplit.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/-
x1037 (o287). General linear endpoint-cell volume bound.

Adapted from `Submission.Lib.K4ScalarSwitching.EndpointChange`
(`scalar_linear_endpoint_cells_volume_le`, original proof by session x0212,
there in three active parameters split at the last coordinate). Here the
dimension and the separated coordinate are arbitrary.
-/
import Submission.Lib.K4PolynomialPotential.TransverseFibers

namespace Submission.Obl.k4_physical_row_packet_potential.Switch

open Set MeasureTheory

/-- Separate the coordinate `p` of a real tuple as the last factor. -/
noncomputable def splitAt (n : ℕ) (p : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p).trans MeasurableEquiv.prodComm

theorem splitAt_apply (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → ℝ) :
    splitAt n p x = (p.removeNth x, x p) := rfl

theorem splitAt_symm_apply (n : ℕ) (p : Fin (n + 1)) (z : (Fin n → ℝ) × ℝ) :
    (splitAt n p).symm z = p.insertNth z.2 z.1 := rfl

theorem splitAt_volume_preserving (n : ℕ) (p : Fin (n + 1)) :
    MeasurePreserving (splitAt n p) volume (volume.prod volume) :=
  (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin n → ℝ)))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) p)

/-- In base-plus-fiber coordinates after an invertible linear change, a
lower bound on the full Jacobian (the determinant times the fiber derivative)
gives the base-volume times height-width estimate. -/
theorem linear_endpoint_cells_volume_le {ι : Type*} (n : ℕ) (p : Fin (n + 1))
    (L : (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
    (hL : LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) ≠ 0)
    (P : (Fin n → ℝ) → Polynomial ℝ) (S : Set (Fin (n + 1) → ℝ))
    (F : Finset ι) (E : ι → Set (Fin n → ℝ)) (c : ι → ℝ) (D : ℕ)
    {ε κ : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hE : ∀ i ∈ F, MeasurableSet (E i))
    (heval : Measurable (fun z : (Fin n → ℝ) × ℝ => (P z.1).eval z.2))
    (hdegree : ∀ x, (P x).natDegree ≤ D)
    (hcover : ∀ z ∈ S, ∃ i ∈ F,
      (splitAt n p (L z)).1 ∈ E i ∧
        |(P (splitAt n p (L z)).1).eval (splitAt n p (L z)).2 - c i| ≤ ε)
    (hjac : ∀ z ∈ S, κ ≤
      |LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))| *
        |(P (splitAt n p (L z)).1).derivative.eval (splitAt n p (L z)).2|) :
    volume S ≤ (∑ i ∈ F, volume (E i)) *
      ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / κ) := by
  let a : ℝ := |LinearMap.det (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))|
  have ha : 0 < a := abs_pos.mpr hL
  let e : (Fin (n + 1) → ℝ) ≃ᵐ ((Fin n → ℝ) × ℝ) :=
    L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.trans (splitAt n p)
  let S' : Set ((Fin n → ℝ) × ℝ) := e '' S
  have hS' : MeasurableSet S' := e.measurableSet_image.mpr hS
  have himage : S' = splitAt n p '' (L '' S) := by
    rw [Set.image_image]
    rfl
  have hLimage : MeasurableSet (L '' S) :=
    L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hS
  have hsplit_image := (splitAt_volume_preserving n p).measure_preimage
    ((splitAt n p).measurableSet_image.mpr hLimage).nullMeasurableSet
  rw [(splitAt n p).injective.preimage_image] at hsplit_image
  have hvolume : (volume.prod volume) S' = ENNReal.ofReal a * volume S := by
    rw [himage, ← hsplit_image]
    exact volume.addHaar_image_linearMap (L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) S
  have hcover' : ∀ z ∈ S', ∃ i ∈ F, z.1 ∈ E i ∧ |(P z.1).eval z.2 - c i| ≤ ε := by
    rintro z ⟨w, hw, rfl⟩
    exact hcover w hw
  have hderiv' : ∀ z ∈ S', κ / a ≤ |(P z.1).derivative.eval z.2| := by
    rintro z ⟨w, hw, rfl⟩
    apply (div_le_iff₀ ha).mpr
    have hh : κ ≤ a * |(P (e w).1).derivative.eval (e w).2| := hjac w hw
    exact hh.trans_eq (mul_comm _ _)
  have hbound := Submission.Lib.K4PolynomialPotential.polynomial_regular_endpoint_cells_mass_le
    volume P S' F E c D hε (div_pos hκ ha) hS' hE heval hdegree hcover' hderiv'
  have hfactor : 4 * ((D : ℝ) + 1) * ε / (κ / a) =
      a * (4 * ((D : ℝ) + 1) * ε / κ) := by
    field_simp [ha.ne', hκ.ne']
  rw [hvolume, hfactor, ENNReal.ofReal_mul ha.le] at hbound
  have hscaled : volume S * ENNReal.ofReal a ≤
      ((∑ i ∈ F, volume (E i)) * ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / κ)) *
        ENNReal.ofReal a := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hbound
  exact (ENNReal.mul_le_mul_iff_left (ne_of_gt (ENNReal.ofReal_pos.mpr ha))
    ENNReal.ofReal_ne_top).mp hscaled

end Submission.Obl.k4_physical_row_packet_potential.Switch
