import Mathlib

/-
Adapted from: here:o003
Original proofs by session x0004 in this LOT tree, obligation o003,
Submission/Obl/k4_multilinear_kakeya/ProductOscillation.lean.
-/

namespace Submission.Lib.K4PolynomialGeometry

open MeasureTheory Set
open scoped ENNReal

/-- Swap a chosen set of coordinates between two independent samples. -/
def swapCoordinates {ι X : Type*} (s : Set ι) [DecidablePred (· ∈ s)]
    (p : (ι → X) × (ι → X)) : (ι → X) × (ι → X) :=
  (s.piecewise p.2 p.1, s.piecewise p.1 p.2)

theorem measurePreserving_swapCoordinates {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] (μ : ι → Measure X) [∀ i, SigmaFinite (μ i)]
    (s : Set ι) [DecidablePred (· ∈ s)] :
    MeasurePreserving (swapCoordinates (X := X) s) ((Measure.pi μ).prod (Measure.pi μ))
      ((Measure.pi μ).prod (Measure.pi μ)) := by
  let E := MeasurableEquiv.arrowProdEquivProdArrow X X ι
  have hE := measurePreserving_arrowProdEquivProdArrow X X ι μ μ
  let T : (ι → X × X) → ι → X × X := fun p i => if i ∈ s then (p i).swap else p i
  have hT : MeasurePreserving T (Measure.pi (fun i => (μ i).prod (μ i)))
      (Measure.pi (fun i => (μ i).prod (μ i))) := by
    apply measurePreserving_pi (fun i => (μ i).prod (μ i))
      (fun i => (μ i).prod (μ i)) (f := fun i p => if i ∈ s then p.swap else p)
    intro i
    by_cases hi : i ∈ s
    · simpa only [ite_eq_left hi] using (Measure.measurePreserving_swap (μ := μ i) (ν := μ i))
    · convert MeasurePreserving.id ((μ i).prod (μ i)) using 1
      funext p
      simp [hi]
  have h := hE.comp (hT.comp (hE.symm E))
  convert h using 1
  funext p
  apply Prod.ext <;> funext i <;> by_cases hi : i ∈ s <;>
    simp [swapCoordinates, E, T, MeasurableEquiv.arrowProdEquivProdArrow,
      Equiv.arrowProdEquivProdArrow, hi]

/-- The first `k` coordinates come from `x` and all others from `y`. -/
def coordinateHybrid {n : ℕ} {X : Type*} (k : ℕ) (x y : Fin n → X) : Fin n → X :=
  fun j => if (j : ℕ) < k then x j else y j

lemma coordinateHybrid_zero {n : ℕ} {X : Type*} (x y : Fin n → X) :
    coordinateHybrid 0 x y = y := by
  funext j
  simp [coordinateHybrid]

lemma coordinateHybrid_all {n : ℕ} {X : Type*} (x y : Fin n → X) :
    coordinateHybrid n x y = x := by
  funext j
  simp [coordinateHybrid, j.isLt]

lemma coordinateHybrid_step {n : ℕ} {X : Type*} (x y : Fin n → X) (i : Fin n) :
    coordinateHybrid ((i : ℕ) + 1) x y = Function.update (coordinateHybrid i x y) i (x i) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [coordinateHybrid]
  · have hne : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
    have hiff : (j : ℕ) < (i : ℕ) + 1 ↔ (j : ℕ) < i := by omega
    simp [coordinateHybrid, hji, hiff]

theorem dist_le_sum_coordinate_updates {n : ℕ} {X Y : Type*} [PseudoMetricSpace Y]
    (f : (Fin n → X) → Y) (x y : Fin n → X) :
    dist (f x) (f y) ≤ ∑ i : Fin n,
      dist (f (Function.update (coordinateHybrid i x y) i (x i)))
        (f (coordinateHybrid i x y)) := by
  have h := dist_le_range_sum_dist (fun k => f (coordinateHybrid k x y)) n
  rw [coordinateHybrid_zero, coordinateHybrid_all, dist_comm] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [coordinateHybrid_step, dist_comm] using h

theorem measurePreserving_coordinateHybrid {n : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (k : ℕ) :
    MeasurePreserving (fun p : (Fin n → X) × (Fin n → X) => coordinateHybrid k p.1 p.2)
      ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := by
  have h := measurePreserving_snd.comp
    (measurePreserving_swapCoordinates μ {i | (i : ℕ) < k})
  exact h

/-- Tensorization of an integral bound for coordinate oscillations. -/
theorem lintegral_oscillation_le_of_update_bound {n : ℕ} {X Y : Type*}
    [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ : Fin n → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → X) → Y) (g : Fin n → (Fin n → X) → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i))
    (hbound : ∀ᵐ p ∂(Measure.pi μ).prod (Measure.pi μ), ∀ i : Fin n,
      ENNReal.ofReal (dist (f (Function.update (coordinateHybrid i p.1 p.2) i (p.1 i)))
        (f (coordinateHybrid i p.1 p.2))) ≤ g i (coordinateHybrid i p.1 p.2)) :
    (∫⁻ p : (Fin n → X) × (Fin n → X), ENNReal.ofReal (dist (f p.1) (f p.2))
      ∂(Measure.pi μ).prod (Measure.pi μ)) ≤ ∑ i, ∫⁻ x, g i x ∂Measure.pi μ := by
  calc
    _ ≤ ∫⁻ p : (Fin n → X) × (Fin n → X),
        ∑ i : Fin n, g i (coordinateHybrid i p.1 p.2) ∂(Measure.pi μ).prod (Measure.pi μ) := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with p hp
      calc
        _ ≤ ENNReal.ofReal (∑ i : Fin n,
            dist (f (Function.update (coordinateHybrid i p.1 p.2) i (p.1 i)))
              (f (coordinateHybrid i p.1 p.2))) :=
          ENNReal.ofReal_le_ofReal (dist_le_sum_coordinate_updates f p.1 p.2)
        _ = ∑ i : Fin n, ENNReal.ofReal
            (dist (f (Function.update (coordinateHybrid i p.1 p.2) i (p.1 i)))
              (f (coordinateHybrid i p.1 p.2))) :=
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => dist_nonneg)
        _ ≤ ∑ i : Fin n, g i (coordinateHybrid i p.1 p.2) := Finset.sum_le_sum (fun i _ => hp i)
    _ = ∑ i : Fin n, ∫⁻ p : (Fin n → X) × (Fin n → X),
        g i (coordinateHybrid i p.1 p.2) ∂(Measure.pi μ).prod (Measure.pi μ) := by
      apply lintegral_finsetSum
      intro i _
      exact (hg i).comp (measurePreserving_coordinateHybrid μ i).measurable
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (measurePreserving_coordinateHybrid μ i).lintegral_comp (hg i)

theorem lintegral_update_fiber {ι X : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace X] (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (F : (ι → X) → ℝ≥0∞) (hF : Measurable F) (i : ι) :
    (∫⁻ x, ∫⁻ t, F (Function.update x i t) ∂μ i ∂Measure.pi μ) =
      ∫⁻ x, F x ∂Measure.pi μ := by
  let G := lmarginal μ {i} F
  have hG : Measurable G := hF.lmarginal μ
  have hGG : lmarginal μ {i} G = G := by
    funext x
    rw [lmarginal_singleton]
    have hconst (t : X) : G (Function.update x i t) = G x :=
      lmarginal_update_of_mem μ (Finset.mem_singleton_self i) F x t
    simp_rw [hconst]
    simp
  have h := lintegral_eq_of_lmarginal_eq {i} hG hF hGG
  simpa only [G, lmarginal_singleton] using h

lemma norm_sub_le_integral_norm_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    ‖f b - f a‖ ≤ ∫ t in Set.Icc (0 : ℝ) 1, ‖deriv f t‖ := by
  have hcont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hbound {u v : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1)
      (hv : v ∈ Set.Icc (0 : ℝ) 1) (huv : u ≤ v) :
      ‖f v - f u‖ ≤ ∫ t in Set.Icc (0 : ℝ) 1, ‖deriv f t‖ := by
    calc
      ‖f v - f u‖ = ‖∫ t in u..v, deriv f t‖ := by
        rw [intervalIntegral.integral_deriv_eq_sub
          (fun _ _ => hf.differentiable one_ne_zero _) (hcont.intervalIntegrable u v)]
      _ ≤ ∫ t in u..v, ‖deriv f t‖ := intervalIntegral.norm_integral_le_integral_norm huv
      _ ≤ ∫ t in (0 : ℝ)..1, ‖deriv f t‖ :=
        intervalIntegral.integral_mono_interval hu.1 huv hv.2
          (Filter.Eventually.of_forall fun _ => norm_nonneg _) (hcont.norm.intervalIntegrable 0 1)
      _ = ∫ t in Set.Icc (0 : ℝ) 1, ‖deriv f t‖ := by
        rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rcases le_total a b with hab | hba
  · exact hbound ha hb hab
  · rw [norm_sub_rev]
    exact hbound hb ha hba

noncomputable def unitIntervalVolume : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

local instance : IsProbabilityMeasure unitIntervalVolume := ⟨by
  simp [unitIntervalVolume, Real.volume_Icc]⟩

noncomputable def unitCubeVolume (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => unitIntervalVolume

local instance (n : ℕ) : IsProbabilityMeasure (unitCubeVolume n) := by
  unfold unitCubeVolume
  infer_instance

lemma ae_mem_unitCube (n : ℕ) :
    ∀ᵐ x ∂unitCubeVolume n, ∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1 := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin n => unitIntervalVolume) i).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Icc)

lemma contDiff_update_line {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    ContDiff ℝ 1 (fun t : ℝ => Function.update x i t) := by
  apply contDiff_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    convert (contDiff_id : ContDiff ℝ 1 (fun t : ℝ => t)) using 1
    funext t
    simp
  · simpa [Function.update, hji] using (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => x j))

lemma hasDerivAt_update_line {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Function.update x i t) (Pi.single i 1) t := by
  apply hasDerivAt_pi.mpr
  intro j
  by_cases hji : j = i
  · subst j
    convert (hasDerivAt_id t) using 1
    · funext u
      simp
    · simp
  · simpa [Function.update, Pi.single_apply, hji] using (hasDerivAt_const t (x j))

lemma deriv_update_line {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    deriv (fun t : ℝ => f (Function.update x i t)) t =
      fderiv ℝ f (Function.update x i t) (Pi.single i 1) := by
  exact ((hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_update_line x i t)).deriv

/-- The L1 oscillation of a C1 function on the unit cube is bounded by the sum of its
coordinate directional derivatives. The cube measure has total mass one. -/
theorem cube_oscillation_le {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫⁻ p : (Fin n → ℝ) × (Fin n → ℝ), ENNReal.ofReal |f p.1 - f p.2|
      ∂(unitCubeVolume n).prod (unitCubeVolume n)) ≤
      ∑ i : Fin n, ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ f x (Pi.single i 1)‖
        ∂unitCubeVolume n := by
  let F (i : Fin n) (x : Fin n → ℝ) := ENNReal.ofReal ‖fderiv ℝ f x (Pi.single i 1)‖
  let g (i : Fin n) := lmarginal (fun _ : Fin n => unitIntervalVolume) {i} (F i)
  have hF (i : Fin n) : Measurable (F i) :=
    (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm).measurable.ennreal_ofReal
  have hg (i : Fin n) : Measurable (g i) := (hF i).lmarginal _
  have hpair : ∀ᵐ p ∂(unitCubeVolume n).prod (unitCubeVolume n),
      (∀ i, p.1 i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, p.2 i ∈ Set.Icc (0 : ℝ) 1) :=
    (measurePreserving_fst.quasiMeasurePreserving.ae (ae_mem_unitCube n)).and
      (measurePreserving_snd.quasiMeasurePreserving.ae (ae_mem_unitCube n))
  have h := lintegral_oscillation_le_of_update_bound (fun _ : Fin n => unitIntervalVolume) f g hg ?_
  · simpa only [Real.dist_eq, g, lmarginal_singleton, unitCubeVolume,
      lintegral_update_fiber _ (F _) (hF _)] using h
  filter_upwards [hpair] with p hp
  intro i
  let x := coordinateHybrid i p.1 p.2
  have hx : x i ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [x, coordinateHybrid, lt_self_iff_false, ite_false]
    exact hp.2 i
  have hpath : ContDiff ℝ 1 (fun t : ℝ => f (Function.update x i t)) :=
    hf.comp (contDiff_update_line x i)
  have hnorm := norm_sub_le_integral_norm_deriv hpath hx (hp.1 i)
  simp only [Function.update_eq_self] at hnorm
  calc
    ENNReal.ofReal (dist (f (Function.update x i (p.1 i))) (f x))
        ≤ ENNReal.ofReal (∫ t in Set.Icc (0 : ℝ) 1,
          ‖deriv (fun t => f (Function.update x i t)) t‖) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [dist_eq_norm] using hnorm
    _ = ∫⁻ t in Set.Icc (0 : ℝ) 1,
        ENNReal.ofReal ‖deriv (fun t => f (Function.update x i t)) t‖ :=
      ofReal_integral_eq_lintegral_ofReal
        (hpath.continuous_deriv le_rfl).norm.integrableOn_Icc
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ = g i x := by
      simp only [g, lmarginal_singleton, unitIntervalVolume, F, deriv_update_line f hf]

theorem affine_cube_oscillation_le {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : (Fin n → ℝ) →L[ℝ] E) (c : E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) :
    (∫⁻ p : (Fin n → ℝ) × (Fin n → ℝ),
      ENNReal.ofReal |f (c + A p.1) - f (c + A p.2)|
        ∂(unitCubeVolume n).prod (unitCubeVolume n)) ≤
      ∑ i : Fin n, ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ f (c + A x) (A (Pi.single i 1))‖
        ∂unitCubeVolume n := by
  have hcomp : ContDiff ℝ 1 (fun x => f (c + A x)) :=
    hf.comp (contDiff_const.add A.contDiff)
  have hd (x : Fin n → ℝ) :
      fderiv ℝ (fun x => f (c + A x)) x = (fderiv ℝ f (c + A x)).comp A := by
    have h : HasFDerivAt (fun x => f (c + A x)) ((fderiv ℝ f (c + A x)).comp A) x :=
      (hf.differentiable one_ne_zero _).hasFDerivAt.comp x (A.hasFDerivAt.const_add c)
    exact h.fderiv
  simpa only [hd, ContinuousLinearMap.comp_apply] using
    cube_oscillation_le (fun x => f (c + A x)) hcomp

end Submission.Lib.K4PolynomialGeometry
