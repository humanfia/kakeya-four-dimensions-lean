import Submission.Lib.K4PolynomialPotential.TransverseFibers

/-!
Adapted from: here:o062
Original proof: x0212, commit 16a6c49,
Submission/Obl/k4_scalar_mesh_projection/EndpointChange.lean.

The linear base-coordinate Jacobian cancels the corresponding rescaling of
the regular height derivative. This is the scalar endpoint-cell volume
estimate in three active switching parameters.
-/

namespace Submission.Lib.K4ScalarSwitching

open Set MeasureTheory

noncomputable def scalarEndpointSplit :
    (Fin 3 → ℝ) ≃ᵐ ((Fin 2 → ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3)).trans
    MeasurableEquiv.prodComm

theorem scalarEndpointSplit_apply (z : Fin 3 → ℝ) :
    scalarEndpointSplit z = (![z 0, z 1], z 2) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

theorem scalarEndpointSplit_volume_preserving :
    MeasurePreserving scalarEndpointSplit volume (volume.prod volume) :=
  (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin 2 → ℝ)))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (2 : Fin 3))

/-- In base-plus-fiber coordinates, a lower bound on the full endpoint
Jacobian gives the full base-area times height-width estimate. The
determinant of the base change cancels exactly. -/
theorem scalar_linear_endpoint_cells_volume_le {ι : Type*}
    (L : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (hL : LinearMap.det (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) ≠ 0)
    (P : (Fin 2 → ℝ) → Polynomial ℝ) (S : Set (Fin 3 → ℝ))
    (F : Finset ι) (E : ι → Set (Fin 2 → ℝ)) (c : ι → ℝ) (D : ℕ)
    {ε κ : ℝ} (hε : 0 ≤ ε) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hE : ∀ i ∈ F, MeasurableSet (E i))
    (heval : Measurable (fun z : (Fin 2 → ℝ) × ℝ => (P z.1).eval z.2))
    (hdegree : ∀ x, (P x).natDegree ≤ D)
    (hcover : ∀ z ∈ S, ∃ i ∈ F,
      (scalarEndpointSplit (L z)).1 ∈ E i ∧
        |(P (scalarEndpointSplit (L z)).1).eval (scalarEndpointSplit (L z)).2 - c i| ≤ ε)
    (hjac : ∀ z ∈ S, κ ≤
      |LinearMap.det (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))| *
        |(P (scalarEndpointSplit (L z)).1).derivative.eval (scalarEndpointSplit (L z)).2|) :
    volume S ≤ (∑ i ∈ F, volume (E i)) *
      ENNReal.ofReal (4 * ((D : ℝ) + 1) * ε / κ) := by
  let a : ℝ := |LinearMap.det (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))|
  have ha : 0 < a := abs_pos.mpr hL
  let e : (Fin 3 → ℝ) ≃ᵐ ((Fin 2 → ℝ) × ℝ) :=
    L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.trans scalarEndpointSplit
  let S' : Set ((Fin 2 → ℝ) × ℝ) := e '' S
  have hS' : MeasurableSet S' := e.measurableSet_image.mpr hS
  have himage : S' = scalarEndpointSplit '' (L '' S) := by
    rw [Set.image_image]
    rfl
  have hLimage : MeasurableSet (L '' S) :=
    L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hS
  have hsplit_image := scalarEndpointSplit_volume_preserving.measure_preimage
    (scalarEndpointSplit.measurableSet_image.mpr hLimage).nullMeasurableSet
  rw [scalarEndpointSplit.injective.preimage_image] at hsplit_image
  have hvolume : (volume.prod volume) S' = ENNReal.ofReal a * volume S := by
    rw [himage, ← hsplit_image]
    exact volume.addHaar_image_linearMap (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) S
  have hcover' : ∀ z ∈ S', ∃ i ∈ F, z.1 ∈ E i ∧ |(P z.1).eval z.2 - c i| ≤ ε := by
    rintro z ⟨w, hw, rfl⟩
    exact hcover w hw
  have hderiv' : ∀ z ∈ S', κ / a ≤ |(P z.1).derivative.eval z.2| := by
    rintro z ⟨w, hw, rfl⟩
    apply (div_le_iff₀ ha).mpr
    have hh : κ ≤ a * |(P (e w).1).derivative.eval (e w).2| := hjac w hw
    exact hh.trans_eq (mul_comm _ _)
  have hbound := Submission.Lib.K4PolynomialPotential.polynomial_regular_endpoint_cells_mass_le volume P S' F E c D
    hε (div_pos hκ ha) hS' hE heval hdegree hcover' hderiv'
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

end Submission.Lib.K4ScalarSwitching
