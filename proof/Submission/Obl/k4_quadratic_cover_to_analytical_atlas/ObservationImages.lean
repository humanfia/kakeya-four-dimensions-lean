import Submission.Obl.k4_quadratic_cover_to_analytical_atlas.Interface

namespace Submission.Obl.k4_quadratic_cover_to_analytical_atlas

open Set

/-- A locally closed set in a second countable locally compact space is sigma compact. -/
theorem sigmaCompact_closed_inter_open {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) : IsSigmaCompact (C ∩ U) := by
  have hUσ : IsSigmaCompact U := by
    let _ := hU.locallyCompactSpace
    rw [isSigmaCompact_iff_sigmaCompactSpace]
    infer_instance
  obtain ⟨K, hK, hcov⟩ := hUσ
  refine ⟨fun n => C ∩ K n, fun n => (hK n).inter_left hC, ?_⟩
  rw [← inter_iUnion, hcov]

/-- A prescribed finite sign pattern is locally closed. -/
theorem sigmaCompact_sign_pattern {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] {m : ℕ}
    (p : Fin m → X → ℝ) (hp : ∀ i, Continuous (p i)) (v : Fin m → Bool) :
    IsSigmaCompact {x | (fun i => decide (0 ≤ p i x)) = v} := by
  classical
  let C : Set X := {x | ∀ i, v i = true → 0 ≤ p i x}
  let U : Set X := {x | ∀ i, v i = false → p i x < 0}
  have hC : IsClosed C := by
    have hc : IsClosed (⋂ i : Fin m, ⋂ (_ : v i = true), {x | (0 : ℝ) ≤ p i x}) := isClosed_iInter fun i : Fin m =>
      isClosed_iInter fun _ : v i = true => isClosed_le continuous_const (hp i)
    convert hc using 1
    ext x
    simp only [C, mem_ofPred_eq, mem_iInter]
  have hU : IsOpen U := by
    have hu : IsOpen (⋂ i : Fin m, ⋂ (_ : v i = false), {x | p i x < (0 : ℝ)}) := isOpen_iInter_of_finite fun i : Fin m =>
      isOpen_iInter_of_finite fun _ : v i = false => isOpen_lt (hp i) continuous_const
    convert hu using 1
    ext x
    simp only [U, mem_ofPred_eq, mem_iInter]
  have heq : {x | (fun i => decide (0 ≤ p i x)) = v} = C ∩ U := by
    ext x
    constructor
    · intro hx
      have hx' : (fun i => decide (0 ≤ p i x)) = v := hx
      constructor
      · intro i hi
        have h := congrFun hx' i
        simpa only [hi, decide_eq_true_eq] using h
      · intro i hi
        have h := congrFun hx' i
        have hn : ¬ 0 ≤ p i x := by simpa only [hi, decide_eq_false_iff_not] using h
        exact lt_of_not_ge hn
    · rintro ⟨hxC, hxU⟩
      change (fun i => decide (0 ≤ p i x)) = v
      funext i
      cases hi : v i
      · have hn : ¬ 0 ≤ p i x := not_le.mpr (hxU i hi)
        simp only [hn, decide_false]
      · have hn : 0 ≤ p i x := hxC i hi
        simp only [hn, decide_true]
  rw [heq]
  exact sigmaCompact_closed_inter_open hC hU

/-- Finite Boolean combinations of continuous nonnegative tests are sigma compact.
This gives Borel observation images without requiring quantifier elimination. -/
theorem sigmaCompact_boolean_tests {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] {m : ℕ}
    (p : Fin m → X → ℝ) (hp : ∀ i, Continuous (p i))
    (b : (Fin m → Bool) → Bool) :
    IsSigmaCompact {x | b (fun i => decide (0 ≤ p i x)) = true} := by
  classical
  have heq : {x | b (fun i => decide (0 ≤ p i x)) = true} =
      ⋃ v : {v : Fin m → Bool // b v = true}, {x | (fun i => decide (0 ≤ p i x)) = v.val} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hx
      exact ⟨⟨fun i => decide (0 ≤ p i x), hx⟩, rfl⟩
    · rintro ⟨v, hv⟩
      exact hv.symm ▸ v.property
  rw [heq]
  exact isSigmaCompact_iUnion _ fun v => sigmaCompact_sign_pattern p hp v.val

/-- The frozen polynomial Boolean format implies sigma compactness. -/
theorem sigmaCompact_of_fmt {n D : ℕ} {H : ℝ} {A : Set (Fin n → ℝ)}
    (h : fmt n H D A) : IsSigmaCompact A := by
  obtain ⟨m, -, p, -, b, hb⟩ := h
  have heq : A = {x | b (fun i => decide (0 ≤ MvPolynomial.eval x (p i))) = true} := by
    ext x
    exact hb x
  rw [heq]
  exact sigmaCompact_boolean_tests (fun i x => MvPolynomial.eval x (p i))
    (fun i => MvPolynomial.continuous_eval (p i)) b

/-- Continuous images of a sigma compact set are Borel in a Hausdorff target. -/
theorem measurableSet_image_of_sigmaCompact {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] {A : Set X}
    (hA : IsSigmaCompact A) (f : X → Y) (hf : Continuous f) : MeasurableSet (f '' A) := by
  obtain ⟨K, hK, hcov⟩ := hA.image hf
  rw [← hcov]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

/-- Each fixed-copy, fixed-hidden-bin continuous observation image of a Boolean
polynomial chart is Borel. Countable unions over copies and hidden bins remain measurable. -/
theorem measurableSet_image_of_fmt {n D : ℕ} {H : ℝ} {A : Set (Fin n → ℝ)}
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    (hA : fmt n H D A) (f : (Fin n → ℝ) → Y) (hf : Continuous f) :
    MeasurableSet (f '' A) :=
  measurableSet_image_of_sigmaCompact (sigmaCompact_of_fmt hA) f hf

/-- Intersecting a sigma compact set with a closed and an open constraint preserves
sigma compactness in the finite dimensional setting used here. -/
theorem sigmaCompact_inter_closed_open {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    {A C U : Set X} (hA : IsSigmaCompact A) (hC : IsClosed C) (hU : IsOpen U) :
    IsSigmaCompact (A ∩ C ∩ U) := by
  obtain ⟨K, hK, hcov⟩ := hA
  have heq : A ∩ C ∩ U = ⋃ n, (K n ∩ C) ∩ U := by
    rw [← hcov, iUnion_inter, iUnion_inter]
  rw [heq]
  exact isSigmaCompact_iUnion _ fun n =>
    sigmaCompact_closed_inter_open ((hK n).isClosed.inter hC) hU

/-- The exact continuous base together with a floored continuous hidden coordinate
has Borel images on sigma compact sources. No measurable input list is required. -/
theorem measurableSet_image_pair_floor {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set X} (hA : IsSigmaCompact A) (f : X → Y) (hf : Continuous f)
    (g : X → ℝ) (hg : Continuous g) :
    MeasurableSet ((fun x => (f x, ⌊g x⌋)) '' A) := by
  let S : ℤ → Set X := fun z => A ∩ {x | (z : ℝ) ≤ g x} ∩ {x | g x < (z : ℝ) + 1}
  have hS (z : ℤ) : IsSigmaCompact (S z) :=
    sigmaCompact_inter_closed_open hA (isClosed_le continuous_const hg)
      (isOpen_lt hg continuous_const)
  have hmeas (z : ℤ) : MeasurableSet ((fun x => (f x, z)) '' S z) :=
    measurableSet_image_of_sigmaCompact (hS z) _ (hf.prodMk continuous_const)
  have heq : ((fun x => (f x, ⌊g x⌋)) '' A) = ⋃ z : ℤ, (fun x => (f x, z)) '' S z := by
    ext o
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine mem_iUnion.mpr ⟨⌊g x⌋, x, ?_, rfl⟩
      exact ⟨⟨hx, Int.floor_le (g x)⟩, Int.lt_floor_add_one (g x)⟩
    · intro ho
      obtain ⟨z, x, hx, rfl⟩ := mem_iUnion.mp ho
      refine ⟨x, hx.1.1, ?_⟩
      have hfloor : ⌊g x⌋ = z := Int.floor_eq_iff.mpr ⟨hx.1.2, hx.2⟩
      change (f x, ⌊g x⌋) = (f x, z)
      rw [hfloor]
  rw [heq]
  exact MeasurableSet.iUnion hmeas

end Submission.Obl.k4_quadratic_cover_to_analytical_atlas
