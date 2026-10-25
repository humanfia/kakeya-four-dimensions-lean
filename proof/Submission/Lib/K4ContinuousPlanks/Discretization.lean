/-
Adapted from: here:o018
-/
import Mathlib

/-! Finite coefficient and mark partitions for continuous weighted laws of planar traces.
Representatives are actual input traces, so the original bounded chart is preserved. -/

open MeasureTheory Set
open scoped ENNReal

namespace Submission.Lib.K4ContinuousPlanks

private theorem same_floor_scaled_distance {r x y : ℝ} (hr : 0 < r)
    (h : ⌊x / r⌋ = ⌊y / r⌋) : |x - y| ≤ r := by
  have ht := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hr] at ht
  exact ((div_lt_one hr).mp ht).le

/-- A finite measurable code can be indexed by `Fin n`, with an actual representative
in every fiber. No nonemptiness assumption on the source is needed. -/
theorem finite_code_representatives {α β : Type*} [MeasurableSpace α]
    (f : SimpleFunc α β) :
    ∃ n : ℕ, ∃ q : α → Fin n, ∃ rep : Fin n → α,
      Measurable q ∧ (∀ i, q (rep i) = i) ∧ (∀ x, f (rep (q x)) = f x) := by
  classical
  let I := {y // y ∈ f.range}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let q : α → Fin (Fintype.card I) := fun x => e ⟨f x, f.mem_range_self x⟩
  have hex (i : Fin (Fintype.card I)) : ∃ x, f x = (e.symm i).1 :=
    SimpleFunc.mem_range.mp (e.symm i).2
  let rep : Fin (Fintype.card I) → α := fun i => Classical.choose (hex i)
  have hrep (i : Fin (Fintype.card I)) : f (rep i) = (e.symm i).1 :=
    Classical.choose_spec (hex i)
  have hqiff (x : α) (i : Fin (Fintype.card I)) : q x = i ↔ f x = (e.symm i).1 := by
    change e ⟨f x, _⟩ = i ↔ _
    rw [← Equiv.eq_symm_apply]
    exact Subtype.ext_iff
  refine ⟨Fintype.card I, q, rep, ?_, ?_, ?_⟩
  · have hqs (i : Fin (Fintype.card I)) : MeasurableSet (q ⁻¹' {i}) := by
      have heq : q ⁻¹' {i} = f ⁻¹' {(e.symm i).1} := by
        ext x
        exact hqiff x i
      rw [heq]
      exact f.measurableSet_fiber _
    exact (⟨q, hqs, Set.toFinite _⟩ : SimpleFunc α (Fin (Fintype.card I))).measurable
  · intro i
    exact (hqiff (rep i) i).mpr (hrep i)
  · intro x
    rw [hrep]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨f x, f.mem_range_self x⟩)

theorem finite_range_floor_code {α : Type*} {d : ℕ}
    (f : α → Fin d → ℝ) (R : ℝ) (hR : ∀ x i, |f x i| ≤ R)
    {r : ℝ} (hr : 0 < r) :
    (Set.range (fun x i => ⌊f x i / r⌋ : α → Fin d → ℤ)).Finite := by
  let codes : Finset (Fin d → ℤ) := Fintype.piFinset
    (fun _ => Finset.Icc ⌊-R / r⌋ ⌊R / r⌋)
  apply codes.finite_toSet.subset
  rintro z ⟨x, rfl⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hR x i)).1 hr.le),
    Int.floor_mono (div_le_div_of_nonneg_right (abs_le.mp (hR x i)).2 hr.le)⟩

noncomputable def boundedFloorCode {α : Type*} [MeasurableSpace α] {d : ℕ}
    (f : α → Fin d → ℝ) (hf : Measurable f) (R : ℝ) (hR : ∀ x i, |f x i| ≤ R)
    (r : ℝ) (hr : 0 < r) : SimpleFunc α (Fin d → ℤ) where
  toFun x i := ⌊f x i / r⌋
  finite_range' := finite_range_floor_code f R hR hr
  measurableSet_fiber' z := by
    have hmeas : Measurable (fun x i => ⌊f x i / r⌋ : α → Fin d → ℤ) :=
      Measurable.of_eval fun i =>
        Int.measurable_floor.comp (((measurable_pi_apply i).comp hf).div_const r)
    exact hmeas (measurableSet_singleton z)

/-- Matching coefficient cells control the whole trace throughout the time block. -/
theorem trace_error_of_same_floor {b u b' u' : EuclideanSpace ℝ (Fin 2)}
    {r : ℝ} (hr : 0 < r)
    (hb : ∀ i, ⌊b i / r⌋ = ⌊b' i / r⌋)
    (hu : ∀ i, ⌊u i / r⌋ = ⌊u' i / r⌋)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(b + t • u) - (b' + t • u')‖ ≤ 4 * r := by
  have hcoord (i : Fin 2) : |((b + t • u) - (b' + t • u')) i| ≤ 2 * r := by
    have hb' := same_floor_scaled_distance hr (hb i)
    have hu' := same_floor_scaled_distance hr (hu i)
    change |b i + t * u i - (b' i + t * u' i)| ≤ 2 * r
    calc
      _ = |(b i - b' i) + t * (u i - u' i)| := by congr 1; ring
      _ ≤ |b i - b' i| + |t| * |u i - u' i| := by
        simpa only [abs_mul] using abs_add_le (b i - b' i) (t * (u i - u' i))
      _ ≤ r + 1 * r := add_le_add hb' (mul_le_mul (by simpa [abs_of_nonneg ht.1] using ht.2)
        hu' (abs_nonneg _) zero_le_one)
      _ = 2 * r := by ring
  have hsq (i : Fin 2) : (((b + t • u) - (b' + t • u')) i) ^ 2 ≤ (2 * r) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * r)).mpr (hcoord i)
  have hn := EuclideanSpace.real_norm_sq_eq ((b + t • u) - (b' + t • u'))
  simp [Fin.sum_univ_succ] at hn
  have hsq0 := hsq 0
  have hsq1 := hsq 1
  change (b 0 + t * u 0 - (b' 0 + t * u' 0)) ^ 2 ≤ (2 * r) ^ 2 at hsq0
  change (b 1 + t * u 1 - (b' 1 + t * u' 1)) ^ 2 ≤ (2 * r) ^ 2 at hsq1
  nlinarith [norm_nonneg ((b + t • u) - (b' + t • u'))]

/-- Finite approximation preserves the entire mark set and changes each full-time
trace by at most `4r`. Representatives are taken from the original coefficient law. -/
theorem finite_trace_discretization {α : Type*} [MeasurableSpace α] {D : ℕ}
    (b u : α → EuclideanSpace ℝ (Fin 2))
    (hb : Measurable b) (hu : Measurable u) (R : ℝ)
    (hRb : ∀ x i, |b x i| ≤ R) (hRu : ∀ x i, |u x i| ≤ R)
    (J : α → Finset (Fin D)) (hJ : ∀ S, MeasurableSet (J ⁻¹' {S}))
    (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, ∃ q : α → Fin n, ∃ rep : Fin n → α,
      Measurable q ∧ (∀ i, q (rep i) = i) ∧
      ∀ x, J (rep (q x)) = J x ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        ‖(b (rep (q x)) + t • u (rep (q x))) - (b x + t • u x)‖ ≤ 4 * r := by
  have hb' : Measurable (fun x i => b x i) := by fun_prop
  have hu' : Measurable (fun x i => u x i) := by fun_prop
  let cb := boundedFloorCode (fun x i => b x i) hb' R hRb r hr
  let cu := boundedFloorCode (fun x i => u x i) hu' R hRu r hr
  let cj : SimpleFunc α (Finset (Fin D)) := ⟨J, hJ, Set.toFinite _⟩
  let code := cb.pair (cu.pair cj)
  obtain ⟨n, q, rep, hq, hrep, hcode⟩ := finite_code_representatives code
  refine ⟨n, q, rep, hq, hrep, ?_⟩
  intro x
  have hbcode (i : Fin 2) : ⌊b (rep (q x)) i / r⌋ = ⌊b x i / r⌋ :=
    congrFun (congrArg Prod.fst (hcode x)) i
  have hucode (i : Fin 2) : ⌊u (rep (q x)) i / r⌋ = ⌊u x i / r⌋ :=
    congrFun (congrArg (fun p => p.2.1) (hcode x)) i
  refine ⟨congrArg (fun p => p.2.2) (hcode x), ?_⟩
  intro t ht
  exact trace_error_of_same_floor hr hbcode hucode ht

/-- Every finite union of code fibers has exactly the sum of its original weights. -/
theorem finite_fiber_mass {α : Type*} [MeasurableSpace α] {n : ℕ}
    (μ : Measure α) (q : α → Fin n) (hq : Measurable q) (S : Finset (Fin n)) :
    ∑ i ∈ S, μ (q ⁻¹' {i}) = μ (q ⁻¹' (S : Set (Fin n))) := by
  calc
    _ = ∑ i ∈ S, μ.map q {i} := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Measure.map_apply hq (measurableSet_singleton i)).symm
    _ = μ.map q S := sum_measure_singleton
    _ = _ := Measure.map_apply hq S.measurableSet

theorem finite_fiber_real_mass {α : Type*} [MeasurableSpace α] {n : ℕ}
    (μ : Measure α) [IsFiniteMeasure μ] (q : α → Fin n) (hq : Measurable q)
    (S : Finset (Fin n)) :
    ∑ i ∈ S, (μ (q ⁻¹' {i})).toReal = (μ (q ⁻¹' (S : Set (Fin n)))).toReal := by
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _), finite_fiber_mass μ q hq S]

end Submission.Lib.K4ContinuousPlanks
