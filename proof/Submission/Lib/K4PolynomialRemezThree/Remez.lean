import Submission.Lib.K4PolynomialRemezThree.PolynomialNorm
import Submission.Lib.K4PolynomialRemez

/-!
# Polynomial Remez comparison in three real dimensions

Adapted from: here:o114

The discriminant argument uses a three-dimensional real base box. Extend the
accepted one- and two-dimensional polynomial comparison estimates by one Fubini
step, always retaining the original, unnormalized mass of the witness set.
-/

namespace Submission.Lib.K4PolynomialRemezThree

open Set MeasureTheory
open Submission.Lib.K4PolynomialRemez

/-- Fixed-degree Remez on a three-dimensional unit box. -/
theorem separately_polynomial_remez_cube (f : ℝ × (ℝ × ℝ) → ℝ) (D : ℕ)
    (hfirst : ∀ y : ℝ × ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ x, p.eval x = f (x, y))
    (hsecond : ∀ x z : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ y, p.eval y = f (x, (y, z)))
    (hthird : ∀ x y : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ z, p.eval z = f (x, (y, z)))
    (S : Set (ℝ × (ℝ × ℝ))) (hSmeas : MeasurableSet S)
    {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ z ∈ S, |f z| ≤ E) :
    ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
      |f z| ≤ (32 * ((D : ℝ) + 1) / η) ^ (3 * D) * E := by
  let I : Set ℝ := Icc 0 1
  let J : Set (ℝ × ℝ) := I ×ˢ I
  let μ : Measure ℝ := volume.restrict I
  let ν : Measure (ℝ × ℝ) := volume.restrict J
  have hI : MeasurableSet I := measurableSet_Icc
  have hJ : MeasurableSet J := hI.prod hI
  haveI : IsProbabilityMeasure μ := ⟨by simp [μ, I]⟩
  haveI : IsProbabilityMeasure ν := by
    constructor
    dsimp only [ν]
    rw [Measure.restrict_apply_univ]
    change (volume.prod volume) (I ×ˢ I) = 1
    rw [Measure.prod_prod]
    simp [I]
  have hμνS : (μ.prod ν) S = volume S := by
    dsimp only [μ, ν]
    rw [Measure.prod_restrict, Measure.restrict_apply hSmeas]
    rw [Set.inter_eq_left.mpr hS]
    rfl
  have hlarge := probability_large_fibers μ ν S hSmeas hη.le
    (hmass.trans_eq hμνS.symm)
  let H : Set ℝ := {x | ENNReal.ofReal (η / 2) ≤ ν (Prod.mk x ⁻¹' S)}
  have hH : MeasurableSet H := measurableSet_le measurable_const
    (measurable_measure_prodMk_left hSmeas)
  have hHmass : ENNReal.ofReal (η / 2) ≤ volume (H ∩ I) := by
    change ENNReal.ofReal (η / 2) ≤ μ H at hlarge
    simpa only [μ, Measure.restrict_apply hH] using hlarge
  let A : ℝ := 32 * ((D : ℝ) + 1) / η
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfactor : 16 * ((D : ℝ) + 1) / (η / 2) = A := by dsimp [A]; ring
  have hfiber : ∀ x ∈ H ∩ I, ∀ y ∈ J, |f (x, y)| ≤ A ^ (2 * D) * E := by
    intro x hx y hy
    have hslice : Prod.mk x ⁻¹' S ⊆ J := by
      intro z hz
      exact (hS hz).2
    have hsliceMeas : MeasurableSet (Prod.mk x ⁻¹' S) :=
      hSmeas.preimage (measurable_const.prodMk measurable_id)
    have hsliceMass : ENNReal.ofReal (η / 2) ≤ volume (Prod.mk x ⁻¹' S) := by
      have hh := hx.1
      change ENNReal.ofReal (η / 2) ≤ ν (Prod.mk x ⁻¹' S) at hh
      simpa only [ν, Measure.restrict_apply hsliceMeas,
        Set.inter_eq_left.mpr hslice] using hh
    have hh := separately_polynomial_remez_square (fun z => f (x, z)) D
      (hthird x) (hsecond x) (Prod.mk x ⁻¹' S) hsliceMeas
      (by positivity : 0 < η / 2) (by linarith : η / 2 ≤ 1) hE
      hslice hsliceMass (fun z hz => hbound (x, z) hz) y hy
    simpa only [hfactor] using hh
  intro z hz
  obtain ⟨p, hp, heval⟩ := hfirst z.2
  have hh := polynomial_remez_unit p D hp (H ∩ I)
    (by positivity : 0 < η / 2) (by linarith : η / 2 ≤ 1)
    (mul_nonneg (pow_nonneg hA _) hE) Set.inter_subset_right hHmass
    (by intro x hx; simpa only [heval] using hfiber x hx z.2 hz.2) z.1 hz.1
  have hfactor_le : 8 * ((D : ℝ) + 1) / (η / 2) ≤ A := by
    calc
      _ ≤ 16 * ((D : ℝ) + 1) / (η / 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ (D : ℝ))]
      _ = A := hfactor
  have hpow : (8 * ((D : ℝ) + 1) / (η / 2)) ^ D ≤ A ^ D :=
    pow_le_pow_left₀ (by positivity) hfactor_le D
  have heq : A ^ D * (A ^ (2 * D) * E) = A ^ (3 * D) * E := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  calc
    |f z| ≤ (8 * ((D : ℝ) + 1) / (η / 2)) ^ D * (A ^ (2 * D) * E) := by
      simpa only [heval] using hh
    _ ≤ A ^ D * (A ^ (2 * D) * E) :=
      mul_le_mul_of_nonneg_right hpow (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := heq

/-- The witness set may be arbitrary: a continuous sublevel superset gives the
same estimate from its outer volume. -/
theorem separately_polynomial_remez_cube_of_outer_measure
    (f : ℝ × (ℝ × ℝ) → ℝ) (hf : Continuous f) (D : ℕ)
    (hfirst : ∀ y : ℝ × ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ x, p.eval x = f (x, y))
    (hsecond : ∀ x z : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ y, p.eval y = f (x, (y, z)))
    (hthird : ∀ x y : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ z, p.eval z = f (x, (y, z)))
    (S : Set (ℝ × (ℝ × ℝ))) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1))
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |f z| ≤ E) :
    ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1),
      |f z| ≤ (32 * ((D : ℝ) + 1) / η) ^ (3 * D) * E := by
  let B : Set (ℝ × (ℝ × ℝ)) :=
    (Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) ∩ {z | |f z| ≤ E}
  have hB : MeasurableSet B :=
    (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)).inter
      (isClosed_le hf.abs continuous_const).measurableSet
  have hSB : S ⊆ B := fun z hz => ⟨hS hz, hbound z hz⟩
  exact separately_polynomial_remez_cube f D hfirst hsecond hthird B hB hη hη1 hE
    Set.inter_subset_left (hmass.trans (measure_mono hSB)) (fun _ hz => hz.2)

/-- Splitting the three coordinates preserves Lebesgue outer measure. -/
noncomputable def cubeEquiv : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)

theorem cubeEquiv_apply (x : Fin 3 → ℝ) : cubeEquiv x = (x 0, (x 1, x 2)) := rfl

theorem cubeEquiv_measurePreserving : MeasurePreserving cubeEquiv volume volume :=
  ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_finTwoArrow ℝ)).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

/-- The Remez estimate in the three base coordinates of a quadratic sheet. The
witness set need not be measurable. -/
theorem separately_polynomial_remez_fin3 (f : (Fin 3 → ℝ) → ℝ)
    (hf : Continuous f) (D : ℕ)
    (hslice : ∀ (v : Fin 3 → ℝ) (i : Fin 3), ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ t, p.eval t = f (Function.update v i t))
    (S : Set (Fin 3 → ℝ)) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (0 : Fin 3 → ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |f z| ≤ E) :
    ∀ z ∈ Icc (0 : Fin 3 → ℝ) 1,
      |f z| ≤ (32 * ((D : ℝ) + 1) / η) ^ (3 * D) * E := by
  let g : ℝ × (ℝ × ℝ) → ℝ := fun z => f ![z.1, z.2.1, z.2.2]
  have hg : Continuous g := hf.comp (by apply continuous_pi; intro i; fin_cases i <;> fun_prop)
  have hvec (x : Fin 3 → ℝ) : (![x 0, x 1, x 2] : Fin 3 → ℝ) = x := by
    ext i
    fin_cases i <;> rfl
  have hfirst : ∀ y : ℝ × ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ x, p.eval x = g (x, y) := by
    intro y
    obtain ⟨p, hp, heval⟩ := hslice ![0, y.1, y.2] 0
    refine ⟨p, hp, fun t => ?_⟩
    rw [heval]
    dsimp [g]
    congr 1
    ext i
    fin_cases i <;> simp
  have hsecond : ∀ x z : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ y, p.eval y = g (x, (y, z)) := by
    intro x z
    obtain ⟨p, hp, heval⟩ := hslice ![x, 0, z] 1
    refine ⟨p, hp, fun t => ?_⟩
    rw [heval]
    dsimp [g]
    congr 1
    ext i
    fin_cases i <;> simp
  have hthird : ∀ x y : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ z, p.eval z = g (x, (y, z)) := by
    intro x y
    obtain ⟨p, hp, heval⟩ := hslice ![x, y, 0] 2
    refine ⟨p, hp, fun t => ?_⟩
    rw [heval]
    dsimp [g]
    congr 1
    ext i
    fin_cases i <;> simp
  have hpre : cubeEquiv ⁻¹' (cubeEquiv '' S) = S := by
    ext x
    simp only [mem_preimage, mem_image, cubeEquiv.injective.eq_iff]
    simp
  have himage : volume (cubeEquiv '' S) = volume S := by
    have hh := cubeEquiv_measurePreserving.measure_preimage_emb
      cubeEquiv.measurableEmbedding (cubeEquiv '' S)
    rw [hpre] at hh
    exact hh.symm
  have hsubset : cubeEquiv '' S ⊆
      Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨(hS hx).1 0, (hS hx).2 0⟩,
      ⟨⟨(hS hx).1 1, (hS hx).2 1⟩, ⟨(hS hx).1 2, (hS hx).2 2⟩⟩⟩
  have hbound' : ∀ z ∈ cubeEquiv '' S, |g z| ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [g, cubeEquiv_apply, hvec] using hbound x hx
  have hh := separately_polynomial_remez_cube_of_outer_measure g hg D hfirst hsecond
    hthird (cubeEquiv '' S) hη hη1 hE hsubset (hmass.trans_eq himage.symm) hbound'
  intro z hz
  have hz' : cubeEquiv z ∈
      Icc (0 : ℝ) 1 ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    ⟨⟨hz.1 0, hz.2 0⟩, ⟨⟨hz.1 1, hz.2 1⟩, ⟨hz.1 2, hz.2 2⟩⟩⟩
  simpa only [g, cubeEquiv_apply, hvec] using hh (cubeEquiv z) hz'

/-- A single large value forces the small-value region to have small outer
volume. This form avoids choosing a fractional-power sublevel constant. -/
theorem volume_sublevel_lt_of_remez_gap (f : (Fin 3 → ℝ) → ℝ)
    (hf : Continuous f) (D : ℕ)
    (hslice : ∀ (v : Fin 3 → ℝ) (i : Fin 3), ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ t, p.eval t = f (Function.update v i t))
    {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    {x : Fin 3 → ℝ} (hx : x ∈ Icc (0 : Fin 3 → ℝ) 1)
    (hgap : (32 * ((D : ℝ) + 1) / η) ^ (3 * D) * E < |f x|) :
    volume (Icc (0 : Fin 3 → ℝ) 1 ∩ {z | |f z| ≤ E}) < ENNReal.ofReal η := by
  by_contra h
  have hmass := le_of_not_gt h
  have hh := separately_polynomial_remez_fin3 f hf D hslice
    (Icc (0 : Fin 3 → ℝ) 1 ∩ {z | |f z| ≤ E}) hη hη1 hE
    Set.inter_subset_left hmass (fun _ hz => hz.2) x hx
  exact (not_le_of_gt hgap) hh

end Submission.Lib.K4PolynomialRemezThree
