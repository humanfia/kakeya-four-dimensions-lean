import Mathlib

namespace Submission.Obl.k4_algebraic_sheet_remez

open Set Metric MeasureTheory
open scoped ENNReal

/-- Polar coordinates bound the volume of a set by a uniform bound for its rays. -/
theorem volume_le_sphere_mul_ray_bound
    {n : ℕ} [Nonempty (Fin n)]
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : MeasurableSet E)
    (x : EuclideanSpace ℝ (Fin n))
    (hsub : E ⊆ closedBall x 1) (b : ℝ)
    (hray : ∀ v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ x + t • (v : EuclideanSpace ℝ (Fin n)) ∈ E}
        ≤ ENNReal.ofReal b) :
    volume E ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ *
      ENNReal.ofReal b := by
  let X := EuclideanSpace ℝ (Fin n)
  let A : Set X := (fun y => x + y) ⁻¹' E
  have hA : MeasurableSet A := hE.preimage (by fun_prop)
  let B : Set (sphere (0 : X) 1 × Ioi (0 : ℝ)) :=
    {p | (p.2 : ℝ) • (p.1 : X) ∈ A}
  have hB : MeasurableSet B := hA.preimage (by fun_prop)
  have hpolar : volume E =
      ((volume : Measure X).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ X - 1))) B := by
    rw [← (volume : Measure X).measurePreserving_homeomorphUnitSphereProd.measure_preimage
      hB.nullMeasurableSet]
    have hpre : homeomorphUnitSphereProd X ⁻¹' B =
        (Subtype.val : ({0}ᶜ : Set X) → X) ⁻¹' A := by
      ext y
      change ((homeomorphUnitSphereProd X y).2 : ℝ) •
        ((homeomorphUnitSphereProd X y).1 : X) ∈ A ↔ y.1 ∈ A
      have he := congrArg Subtype.val ((homeomorphUnitSphereProd X).symm_apply_apply y)
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using Iff.of_eq (congrArg (· ∈ A) he)
    rw [hpre, comap_subtype_coe_apply (measurableSet_singleton (0 : X)).compl]
    have him : Subtype.val '' ((Subtype.val : ({0}ᶜ : Set X) → X) ⁻¹' A) = A \ {0} := by
      ext y
      simp only [mem_image, mem_preimage, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨⟨z, hz⟩, hzA, rfl⟩
        exact ⟨hzA, hz⟩
      · rintro ⟨hyA, hy⟩
        exact ⟨⟨y, hy⟩, hyA, rfl⟩
    rw [him, measure_sdiff_null (measure_singleton (0 : X))]
    exact (measure_preimage_add volume x E).symm
  rw [hpolar, Measure.prod_apply hB]
  have hslice (v : sphere (0 : X) 1) :
      Measure.volumeIoiPow (Module.finrank ℝ X - 1) (Prod.mk v ⁻¹' B) ≤
        ENNReal.ofReal b := by
    let T : Set (Ioi (0 : ℝ)) := Prod.mk v ⁻¹' B
    have hT : MeasurableSet T := hB.preimage (by fun_prop)
    have ht (r : Ioi (0 : ℝ)) (hr : r ∈ T) : (r : ℝ) ≤ 1 := by
      have hz := hsub hr
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hz
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos r.2.out,
        mem_sphere_zero_iff_norm.mp v.2, mul_one] using hz
    rw [Measure.volumeIoiPow, withDensity_apply _ hT]
    calc
      _ ≤ ∫⁻ _r in T, (1 : ENNReal) ∂(volume.comap Subtype.val) := by
        apply setLIntegral_mono' hT
        intro r hr
        exact (ENNReal.ofReal_le_one.mpr (pow_le_one₀ r.2.le (ht r hr)))
      _ = volume (Subtype.val '' T) := by
        rw [setLIntegral_subtype measurableSet_Ioi T (fun _ : ℝ => (1 : ENNReal))]
        simp
      _ ≤ volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ x + t • (v : X) ∈ E} := by
        apply measure_mono
        rintro t ⟨r, hr, rfl⟩
        exact ⟨⟨r.2.le, ht r hr⟩, hr⟩
      _ ≤ ENNReal.ofReal b := hray v
  calc
    _ ≤ ∫⁻ _v, ENNReal.ofReal b ∂(volume : Measure X).toSphere := lintegral_mono hslice
    _ = _ := by rw [lintegral_const, mul_comm]

/-- Every positive relative-volume subset of the half-ball has a long ray from
any prescribed point of that ball. The proportionality constant only depends
on dimension. -/
theorem exists_volume_ray_constant (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ (E : Set (EuclideanSpace ℝ (Fin n))) (θ : ℝ),
        MeasurableSet E → E ⊆ closedBall 0 (1 / 2) → 0 < θ →
        ENNReal.ofReal θ * volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2))
          ≤ volume E →
        ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 →
          ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 ∧
            ENNReal.ofReal (c * θ) ≤
              volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ x + t • v ∈ E} := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let X := EuclideanSpace ℝ (Fin n)
  let H := volume (closedBall (0 : X) (1 / 2))
  let K := (volume : Measure X).toSphere univ
  have hHtop : H ≠ ⊤ := measure_closedBall_lt_top.ne
  have hH : 0 < H.toReal := ENNReal.toReal_pos
    (measure_closedBall_pos volume (0 : X) (by norm_num)).ne' hHtop
  have hKtop : K ≠ ⊤ := measure_ne_top _ _
  let c := min 1 (H.toReal / (2 * (K.toReal + 1)))
  have hc : 0 < c := lt_min zero_lt_one (by positivity)
  have hcH : 2 * (K.toReal + 1) * c ≤ H.toReal := by
    have hden : 0 < 2 * (K.toReal + 1) := by positivity
    have hh := (le_div_iff₀ hden).mp (min_le_right 1 (H.toReal / (2 * (K.toReal + 1))))
    simpa only [mul_comm] using hh
  refine ⟨c, hc, min_le_left _ _, ?_⟩
  intro E θ hE hsub hθ hmass x hx
  by_contra h
  have hle : ∀ v : sphere (0 : X) 1,
      volume {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ x + t • (v : X) ∈ E}
        ≤ ENNReal.ofReal (c * θ) := by
    intro v
    have hv : ‖(v : X)‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
    exact (lt_of_not_ge (fun hh => h ⟨v, hv, hh⟩)).le
  have hsub' : E ⊆ closedBall x 1 := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm]
    have hy' := mem_closedBall_zero_iff.mp (hsub hy)
    exact (norm_sub_le y x).trans (by linarith)
  have hupper := volume_le_sphere_mul_ray_bound E hE x hsub' (c * θ) hle
  have htotal : ENNReal.ofReal θ * H ≤ K * ENNReal.ofReal (c * θ) := hmass.trans hupper
  have hfinite : K * ENNReal.ofReal (c * θ) ≠ ⊤ :=
    ENNReal.mul_ne_top hKtop ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfinite htotal
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ.le,
    ENNReal.toReal_ofReal (mul_pos hc hθ).le] at hreal
  have hsmall : K.toReal * c < H.toReal := by
    nlinarith [ENNReal.toReal_nonneg (a := K)]
  exact (not_le_of_gt (mul_lt_mul_of_pos_left hsmall hθ)) (by nlinarith [hreal])

end Submission.Obl.k4_algebraic_sheet_remez
