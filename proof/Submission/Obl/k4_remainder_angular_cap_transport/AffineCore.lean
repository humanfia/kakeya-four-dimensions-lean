/- Adapted from this LOT tree, o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758.
Sources: Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/;
original file names are recorded beside each adapted group.
Basic.lean in that branch attributes its graph, block, format and chart-system
definitions to this LOT tree, o049, session x0147,
Submission/Obl/k4_cap_class_terminal_charts/Charts.lean. -/
import Mathlib

namespace Submission.Obl.k4_remainder_angular_cap_transport.Geometry
open MeasureTheory MvPolynomial Set

abbrev Trajectory := ℕ × (Fin 6 → ℝ)

abbrev Incidence := Trajectory × ℝ

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def graphPoint (l : Trajectory) (t : ℝ) : Fin 4 → ℝ :=
  ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]

def planarPoint (l : Trajectory) (t : ℝ) : Plane :=
  WithLp.toLp 2 ![l.2 0 + t * l.2 3, l.2 1 + t * l.2 4]

def timeBlock (T : ℕ) (j : Fin (2 ^ T)) : Set ℝ :=
  Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) ((((j : ℕ) : ℝ) + 1) / (2 : ℝ) ^ T)

structure ChartSystem (W T : ℕ) where
  count : ℕ
  world : Fin count → Fin W
  block : Fin count → Fin (2 ^ T)
  center : Fin count → Plane
  speed : Fin count → Plane
  frame : Fin count → Matrix (Fin 2) (Fin 2) ℝ
  test : Fin count → MvPolynomial (Fin 4) ℝ
  assignment : Fin count → Set Trajectory
  event : Fin count → Set Incidence

structure Frame where
  
  t₀ : ℝ
  
  q : ℝ
  
  c : Plane
  
  u : Plane
  
  D : Matrix (Fin 2) (Fin 2) ℝ

namespace Frame
variable (F : Frame)
/- From Normalize.lean. -/
noncomputable def normCoeff (l : Fin 6 → ℝ) : Fin 6 → ℝ :=
  let a₀ := l 0 + F.t₀ * l 3 - F.c 0 - F.t₀ * F.u 0
  let a₁ := l 1 + F.t₀ * l 4 - F.c 1 - F.t₀ * F.u 1
  let b₀ := l 3 - F.u 0
  let b₁ := l 4 - F.u 1
  ![F.D⁻¹ 0 0 * a₀ + F.D⁻¹ 0 1 * a₁,
    F.D⁻¹ 1 0 * a₀ + F.D⁻¹ 1 1 * a₁,
    l 2 + F.t₀ * l 5,
    F.q * (F.D⁻¹ 0 0 * b₀ + F.D⁻¹ 0 1 * b₁),
    F.q * (F.D⁻¹ 1 0 * b₀ + F.D⁻¹ 1 1 * b₁),
    F.q * l 5]

noncomputable def normTraj (l : Trajectory) : Trajectory := (l.1, F.normCoeff l.2)

/- From Atlas.lean. -/
noncomputable def denormCoeff (l' : Fin 6 → ℝ) : Fin 6 → ℝ :=
  let z₀ : Fin 2 → ℝ := ![l' 0, l' 1]
  let z₁ : Fin 2 → ℝ := ![l' 3, l' 4]
  let a := F.D.mulVec z₀
  let b := F.D.mulVec z₁
  let v₀ := F.u 0 + F.q⁻¹ * b 0
  let v₁ := F.u 1 + F.q⁻¹ * b 1
  let s₃ := F.q⁻¹ * l' 5
  ![a 0 + F.c 0 + F.t₀ * F.u 0 - F.t₀ * v₀,
    a 1 + F.c 1 + F.t₀ * F.u 1 - F.t₀ * v₁,
    l' 2 - F.t₀ * s₃,
    v₀, v₁, s₃]

theorem denormCoeff_normCoeff (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (l : Fin 6 → ℝ) :
    F.denormCoeff (F.normCoeff l) = l := by
  have hm : F.D * F.D⁻¹ = 1 := Matrix.mul_nonsing_inv F.D hD
  have h00 : F.D 0 0 * F.D⁻¹ 0 0 + F.D 0 1 * F.D⁻¹ 1 0 = 1 := by
    have := congrFun (congrFun hm 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : F.D 0 0 * F.D⁻¹ 0 1 + F.D 0 1 * F.D⁻¹ 1 1 = 0 := by
    have := congrFun (congrFun hm 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : F.D 1 0 * F.D⁻¹ 0 0 + F.D 1 1 * F.D⁻¹ 1 0 = 0 := by
    have := congrFun (congrFun hm 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : F.D 1 0 * F.D⁻¹ 0 1 + F.D 1 1 * F.D⁻¹ 1 1 = 1 := by
    have := congrFun (congrFun hm 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  funext e
  fin_cases e <;> simp [denormCoeff, normCoeff, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp
  · linear_combination (l 0 - F.c 0) * h00 + (l 1 - F.c 1) * h01
  · linear_combination (l 0 - F.c 0) * h10 + (l 1 - F.c 1) * h11
  · ring
  · linear_combination (l 3 - F.u 0) * h00 + (l 4 - F.u 1) * h01
  · linear_combination (l 3 - F.u 0) * h10 + (l 4 - F.u 1) * h11

def normEvent (A₀ : Set Trajectory) (E : Set Incidence) : Set Incidence :=
  {p | (p.1.1, F.denormCoeff p.1.2) ∈ A₀ ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    ((p.1.1, F.denormCoeff p.1.2), F.t₀ + F.q * p.2) ∈ E}

/- From Normalized.lean. -/
noncomputable def denormTraj (l : Trajectory) : Trajectory := (l.1, F.denormCoeff l.2)

theorem denormTraj_normTraj (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (l : Trajectory) :
    F.denormTraj (F.normTraj l) = l := by
  simp [denormTraj, normTraj, F.denormCoeff_normCoeff hq hD]

theorem continuous_denormCoeff : Continuous F.denormCoeff := by
  unfold denormCoeff
  refine continuous_pi fun e => ?_
  fin_cases e <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> fun_prop

theorem measurable_denormTraj : Measurable F.denormTraj :=
  measurable_fst.prodMk (F.continuous_denormCoeff.measurable.comp measurable_snd)

theorem measurableSet_normEvent {A₀ : Set Trajectory} {E : Set Incidence}
    (hA : MeasurableSet A₀) (hE : MeasurableSet E) : MeasurableSet (F.normEvent A₀ E) := by
  have h1 : Measurable fun p : Incidence => F.denormTraj p.1 :=
    F.measurable_denormTraj.comp measurable_fst
  have h2 : Measurable fun p : Incidence => (F.denormTraj p.1, F.t₀ + F.q * p.2) :=
    h1.prodMk (measurable_const.add (measurable_const.mul measurable_snd))
  exact (h1 hA).inter ((measurable_snd measurableSet_Icc).inter (h2 hE))

end Frame

def velocity (l : Trajectory) : Plane := WithLp.toLp 2 ![l.2 3, l.2 4]

namespace ChartSystem
noncomputable def frameOf {W T : ℕ} (s : ChartSystem W T) (c : Fin s.count) : Frame where
  t₀ := ((s.block c : ℕ) : ℝ) / (2 : ℝ) ^ T
  q := 1 / (2 : ℝ) ^ T
  c := s.center c
  u := s.speed c
  D := s.frame c

theorem frameOf_q_pos {W T : ℕ} (s : ChartSystem W T) (c : Fin s.count) :
    0 < (s.frameOf c).q := by
  simp only [frameOf]; positivity

theorem timeBlock_frameOf {W T : ℕ} (s : ChartSystem W T) (c : Fin s.count) :
    timeBlock T (s.block c) = Set.Icc (s.frameOf c).t₀ ((s.frameOf c).t₀ + (s.frameOf c).q) := by
  simp only [timeBlock, frameOf]
  congr 1
  ring

theorem measurable_normTraj (F : Frame) : Measurable F.normTraj := by
  have hc : Continuous F.normCoeff := by
    unfold Frame.normCoeff
    refine continuous_pi fun e => ?_
    fin_cases e <;> simp <;> fun_prop
  exact measurable_fst.prodMk (hc.measurable.comp measurable_snd)

variable {W T₀ : ℕ} (s : ChartSystem W T₀)
noncomputable def normZ (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory) : ℝ :=
  ∑ c, ω (s.world c) * ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀)

noncomputable def normWeight (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory)
    (c : Fin s.count) : ℝ :=
  ω (s.world c) * ((ν (s.world c) (s.assignment c)).toReal / (2 : ℝ) ^ T₀) / s.normZ ω ν

noncomputable def normPrior (ν : Fin W → Measure Trajectory) (c : Fin s.count) :
    Measure Trajectory :=
  (ν (s.world c) (s.assignment c))⁻¹ •
    Measure.map (s.frameOf c).normTraj ((ν (s.world c)).restrict (s.assignment c))

def normEventOf (c : Fin s.count) : Set Incidence :=
  (s.frameOf c).normEvent (s.assignment c) (s.event c)

end ChartSystem

theorem map_volume_affine (t₀ q : ℝ) (hq : 0 < q) :
    Measure.map (fun t : ℝ => (t - t₀) / q) volume = ENNReal.ofReal q • volume := by
  have h1 : (fun t : ℝ => (t - t₀) / q) = (fun s => q⁻¹ * s) ∘ (fun t => t + -t₀) := by
    funext t; simp [div_eq_inv_mul, sub_eq_add_neg]
  rw [h1, ← Measure.map_map (measurable_const_mul _) (measurable_add_const _),
    map_add_right_eq_self, Real.map_volume_mul_left (inv_ne_zero hq.ne'), inv_inv,
    abs_of_pos hq]

theorem prod_lift_apply {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (Φ : α → α) (hΦ : Measurable Φ) (A : Set α) (hA : MeasurableSet A) (t₀ q : ℝ) (hq : 0 < q)
    (F' : Set (α × ℝ)) (hF' : MeasurableSet F') :
    (ν.prod volume) {p | p.1 ∈ A ∧ (Φ p.1, (p.2 - t₀) / q) ∈ F'} =
      ENNReal.ofReal q * ((Measure.map Φ (ν.restrict A)).prod volume) F' := by
  have hG : Measurable (Prod.map Φ (fun t : ℝ => (t - t₀) / q)) :=
    hΦ.prodMap ((measurable_sub_const _).div_const _)
  have hset : {p : α × ℝ | p.1 ∈ A ∧ (Φ p.1, (p.2 - t₀) / q) ∈ F'} =
      (Prod.map Φ (fun t : ℝ => (t - t₀) / q)) ⁻¹' F' ∩ (A ×ˢ Set.univ) := by
    ext p; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Prod.map,
      Set.mem_prod, Set.mem_univ, and_true]; tauto
  rw [hset, ← Measure.restrict_apply' (hA.prod MeasurableSet.univ),
    ← Measure.restrict_prod_eq_prod_univ, ← Measure.map_apply hG hF',
    ← Measure.map_prod_map _ _ hΦ ((measurable_sub_const _).div_const _),
    map_volume_affine t₀ q hq, Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul]

end Submission.Obl.k4_remainder_angular_cap_transport.Geometry
