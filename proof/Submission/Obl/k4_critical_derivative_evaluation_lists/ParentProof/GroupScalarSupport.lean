/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, GroupScalarSupport.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.ScalarSupportBasics
import Submission.Obl.k4_finite_row_graph_assembly.Projection
import Submission.Lib.K4ContinuousPlanks.Discretization
import Submission.Obl.k4_matching_cofinal_palette_selection.FiniteCode
/-! Adapted from this LOT tree, obligation o107, session x0353,
`Submission/Obl/k4_finite_narrowness_path_improvement/GroupScalarSupport.lean`
(commit 2d33b59a). -/


/-! A contacted true affine entry contributes boundedly many scalar bins in
one fine time bin of an initial-position/velocity group. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open Finset MeasureTheory Set
open scoped Classical

theorem group_point_coordinate_diameter
    (p q r : Fin 3 → ℝ) (D a K : ℝ) (hD : 0 ≤ D) (ha : 0 ≤ a)
    (hDa : D ≤ a) (hK : 1 ≤ K) (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K)
    (ht : |q 0 - r 0| ≤ a)
    (hqZ : |q 1 - referenceZ p (q 0)| ≤ 2 * D)
    (hrZ : |r 1 - referenceZ p (r 0)| ≤ 2 * D)
    (hqY : |q 2 - referenceY p (q 0)| ≤ 3 * D)
    (hrY : |r 2 - referenceY p (r 0)| ≤ 3 * D) :
    ∀ i, |q i - r i| ≤ 7 * K * a := by
  have hK0 : 0 ≤ K := by linarith
  have hKa : a ≤ K * a := by nlinarith only [mul_le_mul_of_nonneg_right hK ha]
  have hrefZ : |referenceZ p (q 0) - referenceZ p (r 0)| ≤ K * a := by
    calc
      _ = |p 2 * (q 0 - r 0)| := by unfold referenceZ; congr 1; ring
      _ ≤ _ := by rw [abs_mul]; exact mul_le_mul hp₂ ht (abs_nonneg _) hK0
  have hrefY : |referenceY p (q 0) - referenceY p (r 0)| ≤ K * a := by
    calc
      _ = |-p 0 * (q 0 - r 0)| := by unfold referenceY; congr 1; ring
      _ ≤ _ := by rw [abs_mul, abs_neg]; exact mul_le_mul hp₀ ht (abs_nonneg _) hK0
  have hZ : |q 1 - r 1| ≤ 5 * K * a := by
    calc
      _ ≤ |q 1 - referenceZ p (q 0)| + |referenceZ p (q 0) - referenceZ p (r 0)| +
          |referenceZ p (r 0) - r 1| :=
        (abs_sub_le (q 1) (referenceZ p (q 0)) (r 1)).trans
          ((add_le_add le_rfl (abs_sub_le (referenceZ p (q 0))
            (referenceZ p (r 0)) (r 1))).trans_eq (by ring))
      _ ≤ 2 * D + K * a + 2 * D := add_le_add (add_le_add hqZ hrefZ)
        (by simpa only [abs_sub_comm] using hrZ)
      _ ≤ _ := by linarith
  have hY : |q 2 - r 2| ≤ 7 * K * a := by
    calc
      _ ≤ |q 2 - referenceY p (q 0)| + |referenceY p (q 0) - referenceY p (r 0)| +
          |referenceY p (r 0) - r 2| :=
        (abs_sub_le (q 2) (referenceY p (q 0)) (r 2)).trans
          ((add_le_add le_rfl (abs_sub_le (referenceY p (q 0))
            (referenceY p (r 0)) (r 2))).trans_eq (by ring))
      _ ≤ 3 * D + K * a + 3 * D := add_le_add (add_le_add hqY hrefY)
        (by simpa only [abs_sub_comm] using hrY)
      _ ≤ _ := by linarith
  intro i
  fin_cases i
  · change |q 0 - r 0| ≤ 7 * K * a
    nlinarith only [ht, hKa, mul_nonneg hK0 ha]
  · change |q 1 - r 1| ≤ 7 * K * a
    nlinarith only [hZ, mul_nonneg hK0 ha]
  · exact hY

theorem group_scalar_bins_per_affine_entry
    {Ω : Type*} (S : Finset Ω) (point : Ω → Fin 3 → ℝ) (value : Ω → ℝ)
    (A : Fin 4 → ℝ) (p : Fin 3 → ℝ) (D a K : ℝ) (j : ℤ)
    (hD : 0 ≤ D) (ha : 0 < a) (hDa : D ≤ a) (hK : 1 ≤ K)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K)
    (hA : ∀ i : Fin 3, |A i.succ| ≤ K)
    (htime : ∀ e ∈ S, ⌊point e 0 / a⌋ = j)
    (hZ : ∀ e ∈ S, |point e 1 - referenceZ p (point e 0)| ≤ 2 * D)
    (hY : ∀ e ∈ S, |point e 2 - referenceY p (point e 0)| ≤ 3 * D)
    (hfit : ∀ e ∈ S, |value e - affineBaseEval A (point e)| ≤ K * a) :
    ((S.image (fun e => ⌊value e / a⌋)).card : ℝ) ≤ 1024 * K ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hK2 : K ≤ K ^ 2 := by nlinarith
  have hdiam : ∀ e ∈ S, ∀ e' ∈ S, |value e - value e'| ≤ 23 * K ^ 2 * a := by
    intro e he e' he'
    have ht : |point e 0 - point e' 0| ≤ a :=
      Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq ha
        ((htime e he).trans (htime e' he').symm)
    have hcoords := group_point_coordinate_diameter p (point e) (point e') D a K
      hD ha.le hDa hK hp₀ hp₂ ht (hZ e he) (hZ e' he') (hY e he) (hY e' he')
    have hlocal := affineBaseEval_mesh_gap A (point e) (point e') K (7 * K * a) hK0 hA hcoords
    calc
      _ ≤ |value e - affineBaseEval A (point e)| +
          |affineBaseEval A (point e) - affineBaseEval A (point e')| +
          |affineBaseEval A (point e') - value e'| :=
        (abs_sub_le (value e) (affineBaseEval A (point e)) (value e')).trans
          ((add_le_add le_rfl (abs_sub_le (affineBaseEval A (point e))
            (affineBaseEval A (point e')) (value e'))).trans_eq (by ring))
      _ ≤ K * a + 3 * K * (7 * K * a) + K * a := add_le_add
        (add_le_add (hfit e he) hlocal) (by simpa only [abs_sub_comm] using hfit e' he')
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hK2 ha.le]
  have hcount := scalar_floor_image_card_of_diameter S value ha
    (show 0 ≤ 23 * K ^ 2 * a by positivity) hdiam
  have heq : 32 * (23 * K ^ 2 * a) / a + 64 = 736 * K ^ 2 + 64 := by field_simp; ring
  rw [heq] at hcount
  have hKsq : 1 ≤ K ^ 2 := one_le_pow₀ hK
  linarith

/-- If each fine time bin meets at most B frozen true entries, their scalar
spacetime support has O(K squared B/a) bins, using the whole-entry fits. -/
theorem finite_group_scalar_support_count
    {Ω I : Type*} [DecidableEq I] (S : Finset Ω)
    (point : Ω → Fin 3 → ℝ) (value : Ω → ℝ) (label : Ω → I)
    (A : I → Fin 4 → ℝ) (allowed : ℤ → Finset I) (p : Fin 3 → ℝ)
    (D a K B : ℝ) (hD : 0 ≤ D) (ha : 0 < a) (ha1 : a ≤ 1)
    (hDa : D ≤ a) (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K)
    (hA : ∀ i, ∀ j : Fin 3, |A i j.succ| ≤ K)
    (hunit : ∀ e ∈ S, point e 0 ∈ Set.Icc (0 : ℝ) 1)
    (hZ : ∀ e ∈ S, |point e 1 - referenceZ p (point e 0)| ≤ 2 * D)
    (hY : ∀ e ∈ S, |point e 2 - referenceY p (point e 0)| ≤ 3 * D)
    (hfit : ∀ e ∈ S, |value e - affineBaseEval (A (label e)) (point e)| ≤ K * a)
    (hallowed : ∀ j, ((allowed j).card : ℝ) ≤ B)
    (hcover : ∀ e ∈ S, label e ∈ allowed ⌊point e 0 / a⌋) :
    ((S.image (fun e => (⌊point e 0 / a⌋, ⌊value e / a⌋))).card : ℝ) ≤
      98304 * K ^ 2 * B / a := by
  let timeCode := fun e => ⌊point e 0 / a⌋
  let valueCode := fun e => ⌊value e / a⌋
  let cells := fun j => S.filter (fun e => timeCode e = j)
  let bins := fun j => (cells j).image valueCode
  have hlabels (j : ℤ) : (((cells j).image label).card : ℝ) ≤ B := by
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hallowed j)
    intro i hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    have he' := Finset.mem_filter.mp he
    simpa only [← he'.2] using hcover e he'.1
  have hbins (j : ℤ) : ((bins j).card : ℝ) ≤ B * (1024 * K ^ 2) := by
    have hc := Submission.Obl.k4_finite_row_graph_assembly.card_image_le_of_fiber_images
      (cells j) label valueCode (C := 1024 * K ^ 2) (by
        intro i hi
        apply group_scalar_bins_per_affine_entry
          ((cells j).filter (fun e => label e = i)) point value (A i) p D a K j
          hD ha hDa hK hp₀ hp₂ (hA i)
        · intro e he
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
        · intro e he
          exact hZ e (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
        · intro e he
          exact hY e (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1
        · intro e he
          have he' := Finset.mem_filter.mp he
          have hh := hfit e (Finset.mem_filter.mp he'.1).1
          rwa [he'.2] at hh)
    exact hc.trans (mul_le_mul_of_nonneg_right (hlabels j) (by positivity))
  have htime : ((S.image timeCode).card : ℝ) ≤ 96 / a := by
    have hc := scalar_floor_image_card_of_diameter S (fun e => point e 0) ha
      (show (0 : ℝ) ≤ 1 by norm_num) (by
        intro e he e' he'
        have ht := hunit e he
        have ht' := hunit e' he'
        exact abs_le.mpr ⟨by linarith [ht.1, ht.2, ht'.1, ht'.2],
          by linarith [ht.1, ht.2, ht'.1, ht'.2]⟩)
    have hinv : (1 : ℝ) ≤ 1 / a := (le_div_iff₀ ha).mpr (by linarith)
    apply hc.trans
    simp only [div_eq_mul_inv, mul_one, one_mul] at hinv ⊢
    linarith only [hinv]
  let F := S.image (fun e => (timeCode e, valueCode e))
  have hsub : F ⊆ (S.image timeCode).biUnion (fun j => {j} ×ˢ bins j) := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hq
    refine Finset.mem_biUnion.mpr ⟨timeCode e, Finset.mem_image.mpr ⟨e, he, rfl⟩, ?_⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_singleton_self _,
      Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩, rfl⟩⟩
  calc
    _ ≤ (((S.image timeCode).biUnion (fun j => {j} ×ˢ bins j)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ j ∈ S.image timeCode, (({j} ×ˢ bins j).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ = ∑ j ∈ S.image timeCode, ((bins j).card : ℝ) := by simp
    _ ≤ ∑ _j ∈ S.image timeCode, B * (1024 * K ^ 2) := Finset.sum_le_sum (fun j _ => hbins j)
    _ = ((S.image timeCode).card : ℝ) * (B * (1024 * K ^ 2)) := by simp
    _ ≤ (96 / a) * (B * (1024 * K ^ 2)) :=
      mul_le_mul_of_nonneg_right htime (by positivity)
    _ = _ := by ring

/-- The finite scalar support estimate gives a cover of the actual original
source law. The finite table is used only to enumerate its genuine bins. -/
theorem original_group_scalar_support_cover
    {Y I : Type*} [MeasurableSpace Y] [DecidableEq I]
    (μ : Measure Y) (U : Set Y) (hU : MeasurableSet U) (hfull : μ Uᶜ = 0)
    (point : Y → Fin 3 → ℝ) (value : Y → ℝ) (label : Y → I)
    (hpointm : Measurable point) (hvaluem : Measurable value)
    (A : I → Fin 4 → ℝ) (allowed : ℤ → Finset I) (p : Fin 3 → ℝ)
    (D a K B R : ℝ) (hD : 0 ≤ D) (ha : 0 < a) (ha1 : a ≤ 1)
    (hDa : D ≤ a) (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hp₀ : |p 0| ≤ K) (hp₂ : |p 2| ≤ K)
    (hA : ∀ i, ∀ j : Fin 3, |A i j.succ| ≤ K)
    (hunit : ∀ y ∈ U, point y 0 ∈ Set.Icc (0 : ℝ) 1)
    (hvalue : ∀ y ∈ U, |value y| ≤ R)
    (hZ : ∀ y ∈ U, |point y 1 - referenceZ p (point y 0)| ≤ 2 * D)
    (hY : ∀ y ∈ U, |point y 2 - referenceY p (point y 0)| ≤ 3 * D)
    (hfit : ∀ y ∈ U, |value y - affineBaseEval (A (label y)) (point y)| ≤ K * a)
    (hallowed : ∀ j, ((allowed j).card : ℝ) ≤ B)
    (hcover : ∀ y ∈ U, label y ∈ allowed ⌊point y 0 / a⌋) :
    ∃ F : Finset (ℤ × ℤ), (F.card : ℝ) ≤ 98304 * K ^ 2 * B / a ∧
      ∀ᵐ y ∂μ, (⌊point y 0 / a⌋, ⌊value y / a⌋) ∈ F := by
  have hUAE : ∀ᵐ y ∂μ, y ∈ U := by
    apply ae_iff.mpr
    exact hfull
  by_cases hSne : U.Nonempty
  swap
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · exact hUAE.mono (fun y hy => False.elim (hSne ⟨y, hy⟩))
  let joint : Y → ℤ × ℤ := fun y => (⌊point y 0 / a⌋, ⌊value y / a⌋)
  have hjoint : Measurable joint :=
    (Int.measurable_floor.comp (((measurable_pi_apply 0).comp hpointm).div_const a)).prodMk
      (Int.measurable_floor.comp (hvaluem.div_const a))
  have hbounded : ∀ y : U, ∀ i : Fin 2, |(![point y 0, value y] : Fin 2 → ℝ) i| ≤ max 1 R := by
    intro y i
    fin_cases i
    · change |point y 0| ≤ max 1 R
      have ht := hunit y y.property
      exact (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩).trans (le_max_left _ _)
    · exact (hvalue y y.property).trans (le_max_right _ _)
  have hfinvec := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    (fun y : U => ![point y 0, value y]) (max 1 R) hbounded ha
  have hfinite : (joint '' U).Finite := (hfinvec.image (fun q => (q 0, q 1))).subset (by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(fun i => ⌊(![point y 0, value y] : Fin 2 → ℝ) i / a⌋), ⟨⟨y, hy⟩, rfl⟩, rfl⟩)
  obtain ⟨n, hn, code, decode, hcode, hdecode, hrepr⟩ :=
    Submission.Obl.k4_matching_cofinal_palette_selection.exists_finite_code_on U hU hSne joint hjoint hfinite
  let rep : Fin n → Y := fun i => Classical.choose (hrepr i)
  have hrep (i : Fin n) : rep i ∈ U ∧ joint (rep i) = decode i := Classical.choose_spec (hrepr i)
  let F := Finset.univ.image (fun i => joint (rep i))
  refine ⟨F, ?_, ?_⟩
  · exact finite_group_scalar_support_count Finset.univ (fun i => point (rep i))
      (fun i => value (rep i)) (fun i => label (rep i)) A allowed p D a K B hD ha ha1
      hDa hK hB hp₀ hp₂ hA (fun i _ => hunit _ (hrep i).1)
      (fun i _ => hZ _ (hrep i).1) (fun i _ => hY _ (hrep i).1)
      (fun i _ => hfit _ (hrep i).1) hallowed (fun i _ => hcover _ (hrep i).1)
  · filter_upwards [hUAE] with y hy
    exact Finset.mem_image.mpr ⟨code y, Finset.mem_univ _,
      (hrep (code y)).2.trans (hdecode y hy)⟩

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
