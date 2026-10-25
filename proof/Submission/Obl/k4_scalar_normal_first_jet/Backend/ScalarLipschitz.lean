/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarLipschitz.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarLipschitz.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Removing a bottom-scale additive error from scalar row comparisons. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open Set
open scoped NNReal

/-- A real row with an additive comparison error lies uniformly near a
genuine Lipschitz row, on exactly the original active set. -/
theorem lipschitz_approx_of_additive_error {α : Type*} [PseudoMetricSpace α]
    {s : Set α} {f : α → ℝ} {K : ℝ≥0} {δ : ℝ}
    (hf : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ K * dist x y + δ) :
    ∃ g : α → ℝ, LipschitzWith K g ∧ ∀ x ∈ s, |g x - f x| ≤ δ := by
  rcases eq_empty_or_nonempty s with rfl | hs
  · exact ⟨fun _ => 0, (LipschitzWith.const _).weaken zero_le, by simp⟩
  have : Nonempty s := by simpa only [nonempty_coe_sort] using hs
  let g : α → ℝ := fun y => iInf fun x : s => f x + K * dist y x
  have hadd (x : α) (hx : x ∈ s) (y : α) (hy : y ∈ s) :
      f x ≤ f y + K * dist x y + δ := by
    have h := (abs_le.mp (hf x hx y hy)).2
    linarith
  have hb (y : α) : BddBelow (range fun x : s => f x + K * dist y x) := by
    obtain ⟨z, hz⟩ := hs
    refine ⟨f z - K * dist y z - δ, ?_⟩
    rintro w ⟨t, rfl⟩
    have hh := hadd z hz t t.2
    have ht := mul_le_mul_of_nonneg_left (dist_triangle_left z t y) K.coe_nonneg
    dsimp
    nlinarith
  have hg : LipschitzWith K g := by
    apply LipschitzWith.of_le_add_mul K
    intro x y
    rw [← sub_le_iff_le_add]
    apply le_ciInf
    intro z
    rw [sub_le_iff_le_add]
    calc
      g x ≤ f z + K * dist x z := ciInf_le (hb x) z
      _ ≤ f z + K * dist y z + K * dist x y := by
        have ht := mul_le_mul_of_nonneg_left (dist_triangle x y z) K.coe_nonneg
        nlinarith
  refine ⟨g, hg, ?_⟩
  intro x hx
  have hupper : g x ≤ f x := by
    simpa only [g, dist_self, mul_zero, add_zero] using ciInf_le (hb x) ⟨x, hx⟩
  have hlower : f x - δ ≤ g x := by
    apply le_ciInf
    intro y
    have hh := hadd x hx y y.2
    linarith
  have hδ : 0 ≤ δ := by simpa using hf x hx x hx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A residual slope which depends approximately on one scalar coordinate
is uniformly near a genuine Lipschitz function of that coordinate. The
index set and the original labels are retained in the conclusion. -/
theorem lipschitz_coordinate_factor {ι : Type*} (A : Set ι) (v q : ι → ℝ)
    {K : ℝ≥0} {δ : ℝ}
    (hq : ∀ i ∈ A, ∀ j ∈ A, |q i - q j| ≤ K * |v i - v j| + δ) :
    ∃ G : ℝ → ℝ, LipschitzWith K G ∧ ∀ i ∈ A, |q i - G (v i)| ≤ 2 * δ := by
  classical
  let f : ℝ → ℝ := fun x => if hx : ∃ i ∈ A, v i = x then q hx.choose else 0
  have hrep (x : ℝ) (hx : x ∈ v '' A) : ∃ i ∈ A, v i = x ∧ f x = q i := by
    have he : ∃ i ∈ A, v i = x := hx
    refine ⟨he.choose, he.choose_spec.1, he.choose_spec.2, ?_⟩
    simp only [f, dite_eq_left he]
  have hf : ∀ x ∈ v '' A, ∀ y ∈ v '' A, |f x - f y| ≤ K * dist x y + δ := by
    intro x hx y hy
    obtain ⟨i, hi, hvi, hfi⟩ := hrep x hx
    obtain ⟨j, hj, hvj, hfj⟩ := hrep y hy
    have h := hq i hi j hj
    rw [hvi, hvj] at h
    simpa only [hfi, hfj, Real.dist_eq] using h
  obtain ⟨G, hG, hnear⟩ := lipschitz_approx_of_additive_error hf
  refine ⟨G, hG, ?_⟩
  intro i hi
  have hmem : v i ∈ v '' A := ⟨i, hi, rfl⟩
  obtain ⟨j, hj, hvj, hfj⟩ := hrep (v i) hmem
  have hqf : |q i - f (v i)| ≤ δ := by
    rw [hfj]
    have h := hq i hi j hj
    rw [hvj] at h
    simpa only [sub_self, abs_zero, mul_zero, zero_add] using h
  have hGf : |f (v i) - G (v i)| ≤ δ := by
    simpa only [abs_sub_comm] using hnear (v i) hmem
  exact (abs_sub_le (q i) (f (v i)) (G (v i))).trans (by linarith)

/-- Scaling the observed coordinate by its Lipschitz constant gives a
unit Lipschitz model, with the same original indexed approximation error. -/
theorem lipschitz_coordinate_factor_unit {ι : Type*} (A : Set ι) (v q : ι → ℝ)
    {K δ : ℝ} (hK : 0 < K)
    (hq : ∀ i ∈ A, ∀ j ∈ A, |q i - q j| ≤ K * |v i - v j| + δ) :
    ∃ G : ℝ → ℝ, (∀ s t, |G s - G t| ≤ |s - t|) ∧
      ∀ i ∈ A, |q i - G (K * v i)| ≤ 2 * δ := by
  have hcompare : ∀ i ∈ A, ∀ j ∈ A,
      |q i - q j| ≤ (⟨K, hK.le⟩ : ℝ≥0) * |v i - v j| + δ := hq
  obtain ⟨G₀, hG₀, hnear₀⟩ := lipschitz_coordinate_factor A v q hcompare
  let G : ℝ → ℝ := fun s => G₀ (s / K)
  refine ⟨G, ?_, ?_⟩
  · intro s t
    calc
      _ ≤ K * dist (s / K) (t / K) := hG₀.dist_le_mul _ _
      _ = |s - t| := by
        rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hK]
        field_simp
  · intro i hi
    simpa only [G, mul_div_cancel_left₀ (v i) hK.ne'] using hnear₀ i hi

/-- The global Lipschitz approximation can keep an original active anchor
exactly, which is needed before scalar time normalization. -/
theorem lipschitz_approx_preserving_anchor {α : Type*} [PseudoMetricSpace α]
    {s : Set α} {f : α → ℝ} {K : ℝ≥0} {δ : ℝ} {a : α} (ha : a ∈ s)
    (hf : ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ K * dist x y + δ) :
    ∃ g : α → ℝ, LipschitzWith K g ∧ g a = f a ∧
      ∀ x ∈ s, |g x - f x| ≤ 2 * δ := by
  obtain ⟨g, hg, hnear⟩ := lipschitz_approx_of_additive_error hf
  have hLip : LipschitzWith K (fun x => g x - g a + f a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    calc
      _ = dist (g x) (g y) := by rw [Real.dist_eq, Real.dist_eq]; congr 1; ring
      _ ≤ _ := hg.dist_le_mul x y
  refine ⟨fun x => g x - g a + f a, hLip, by ring, ?_⟩
  intro x hx
  calc
    _ = |(g x - f x) - (g a - f a)| := by congr 1; ring
    _ ≤ |g x - f x| + |g a - f a| := abs_sub _ _
    _ ≤ 2 * δ := by linarith [hnear x hx, hnear a ha]

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
