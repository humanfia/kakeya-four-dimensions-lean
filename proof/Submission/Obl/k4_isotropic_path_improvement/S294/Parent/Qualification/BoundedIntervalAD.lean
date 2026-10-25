-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.BoundedIntervalAD, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/BoundedIntervalAD.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 3bcc131b,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/BoundedIntervalAD.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/BoundedIntervalAD.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
import Submission.Obl.k4_scalar_initial_true_horizon.FiniteCardBound


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open Set Metric
open WangZahlLot.Obl.wz_slab_local_linearity

noncomputable section

/-- Uniform counts for finite collections of actual codes construct
a finite cover of the ENTIRE original family. -/
theorem finite_code_ball_cover {Ω I : Type*} (A : Set Ω) (point : Ω → ℝ)
    (code : Ω → I) (center : I → ℝ) (r C : ℝ)
    (hcount : ∀ F : Finset I, (↑F : Set I) ⊆ code '' A → (F.card : ℝ) ≤ C)
    (hfit : ∀ ω ∈ A, point ω ∈ closedBall (center (code ω)) r) :
    ∃ (m : ℕ) (c : Fin m → ℝ),
      point '' A ⊆ ⋃ j, closedBall (c j) r ∧ (m : ℝ) ≤ C := by
  classical
  have hfinite := Submission.Obl.k4_scalar_initial_true_horizon.finite_of_uniform_finset_card_bound
    (code '' A) C hcount
  let F := hfinite.toFinset
  let e := Fintype.equivFin F
  refine ⟨Fintype.card F, fun j => center (e.symm j).val, ?_, ?_⟩
  · rintro x ⟨ω,hω,rfl⟩
    have hmem : code ω ∈ F := hfinite.mem_toFinset.mpr ⟨ω,hω,rfl⟩
    refine mem_iUnion.mpr ⟨e ⟨code ω,hmem⟩, ?_⟩
    change point ω ∈ closedBall ((fun z : F => center z.val)
      (e.symm (e ⟨code ω,hmem⟩))) r
    rw [e.symm_apply_apply]
    exact hfit ω hω
  · simpa only [Fintype.card_coe] using hcount F (by simp [F])

/-- Combine actual finite ball covers without introducing a factor
depending on the number of points being covered. -/
theorem finite_family_ball_cover {I : Type*} [Fintype I] (S : I → Set ℝ) (r C : ℝ)
    (h : ∀ i, ∃ (m : ℕ) (c : Fin m → ℝ),
      S i ⊆ ⋃ j, closedBall (c j) r ∧ (m : ℝ) ≤ C) :
    ∃ (m : ℕ) (c : Fin m → ℝ),
      (⋃ i, S i) ⊆ ⋃ j, closedBall (c j) r ∧ (m : ℝ) ≤ Fintype.card I * C := by
  classical
  choose m c hc hm using h
  let J := (i : I) × Fin (m i)
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j => c (e.symm j).1 (e.symm j).2, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hc i hi)
    apply mem_iUnion.mpr
    refine ⟨e ⟨i,j⟩, ?_⟩
    change x ∈ closedBall ((fun w : J => c w.1 w.2) (e.symm (e ⟨i,j⟩))) r
    rw [e.symm_apply_apply]
    exact hj
  · calc
      (Fintype.card J : ℝ) = ∑ i, (m i : ℝ) := by
        simp only [J, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
      _ ≤ ∑ _i : I, C := Finset.sum_le_sum fun i _ => hm i
      _ = Fintype.card I * C := by simp

/-- The scalar-normal interface asks for all outer radii, including
R>1. A fixed finite unit-interval cover extends the genuine local
counts to those radii, with only a fixed multiplicative loss. -/
theorem intervalAD_of_local_unit_cover (S : Set ℝ) (ζ d C : ℝ)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (M : ℕ) (hM : 1 ≤ M) (left : Fin M → ℝ)
    (hunit : S ⊆ ⋃ i, Icc (left i) (left i + 1))
    (hlocal : ∀ r R a : ℝ, ζ ≤ r → r ≤ R → R ≤ 1 →
      ∃ (m : ℕ) (c : Fin m → ℝ),
        S ∩ Icc a (a + R) ⊆ ⋃ j, closedBall (c j) r ∧
          (m : ℝ) ≤ C * (R / r) ^ d) :
    IntervalAD ζ d ((M : ℝ) * C) S := by
  intro r R a hζr hrR
  have hr : 0 < r := hζ.trans_le hζr
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  by_cases hR : R ≤ 1
  · obtain ⟨m,c,hcover,hcard⟩ := hlocal r R a hζr hrR hR
    refine ⟨m,c,hcover,hcard.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by nlinarith : C ≤ (M : ℝ) * C)
      (Real.rpow_nonneg (div_nonneg (hr.le.trans hrR) hr.le) _)
  · let r₀ := min r 1
    have hr₀ : 0 < r₀ := lt_min hr (by norm_num)
    have hζ₀ : ζ ≤ r₀ := le_min hζr hζ1
    have h₀r : r₀ ≤ r := min_le_left _ _
    have h₀1 : r₀ ≤ 1 := min_le_right _ _
    have hfamily (i : Fin M) : ∃ (m : ℕ) (c : Fin m → ℝ),
        S ∩ Icc (left i) (left i + 1) ⊆ ⋃ j, closedBall (c j) r ∧
          (m : ℝ) ≤ C * (1 / r₀) ^ d := by
      obtain ⟨m,c,hcover,hcard⟩ := hlocal r₀ 1 (left i) hζ₀ h₀1 le_rfl
      refine ⟨m,c,?_,hcard⟩
      intro x hx
      obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hx)
      exact mem_iUnion.mpr ⟨j, closedBall_subset_closedBall h₀r hj⟩
    obtain ⟨m,c,hcover,hcard⟩ := finite_family_ball_cover
      (fun i : Fin M => S ∩ Icc (left i) (left i + 1)) r (C * (1 / r₀) ^ d) hfamily
    have hratio : 1 / r₀ ≤ R / r := by
      by_cases hr1 : r ≤ 1
      · rw [show r₀ = r from min_eq_left hr1]
        exact div_le_div_of_nonneg_right (by linarith : (1 : ℝ) ≤ R) hr.le
      · rw [show r₀ = 1 from min_eq_right (le_of_not_ge hr1)]
        simp only [div_one]
        exact (le_div_iff₀ hr).mpr (by simpa using hrR)
    refine ⟨m,c,?_,?_⟩
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hunit hx.1)
      exact hcover (mem_iUnion.mpr ⟨i,hx.1,hi⟩)
    · calc
        (m : ℝ) ≤ (M : ℝ) * (C * (1 / r₀) ^ d) := by simpa using hcard
        _ = ((M : ℝ) * C) * (1 / r₀) ^ d := by ring
        _ ≤ ((M : ℝ) * C) * (R / r) ^ d :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hratio hd) (by positivity)

/-- A bounded scalar set supplies its own fixed unit-interval cover. -/
theorem intervalAD_of_bounded_local (S : Set ℝ) (ζ d C B : ℝ)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hd : 0 ≤ d) (hC : 0 ≤ C) (_hB : 0 ≤ B)
    (hbound : ∀ x ∈ S, |x| ≤ B)
    (hlocal : ∀ r R a : ℝ, ζ ≤ r → r ≤ R → R ≤ 1 →
      ∃ (m : ℕ) (c : Fin m → ℝ),
        S ∩ Icc a (a + R) ⊆ ⋃ j, closedBall (c j) r ∧
          (m : ℝ) ≤ C * (R / r) ^ d) :
    IntervalAD ζ d ((⌈2 * B⌉₊ + 1 : ℕ) * C) S := by
  let M := ⌈2 * B⌉₊ + 1
  let left : Fin M → ℝ := fun i => -B + (i : ℕ)
  apply intervalAD_of_local_unit_cover S ζ d C hζ hζ1 hd hC M (by omega) left
    ?_ hlocal
  intro x hx
  have hb := abs_le.mp (hbound x hx)
  have hu : 0 ≤ x + B := by linarith
  have hfloor := Nat.floor_le hu
  have hceil := Nat.le_ceil (2 * B)
  have hi : ⌊x + B⌋₊ < M := by
    have hh : (⌊x + B⌋₊ : ℝ) ≤ (⌈2 * B⌉₊ : ℕ) := by linarith
    have : ⌊x + B⌋₊ ≤ ⌈2 * B⌉₊ := by exact_mod_cast hh
    dsimp [M]
    omega
  refine mem_iUnion.mpr ⟨⟨⌊x + B⌋₊, hi⟩, ?_⟩
  change x ∈ Icc (-B + (⌊x+B⌋₊ : ℝ)) (-B + (⌊x+B⌋₊ : ℝ) + 1)
  constructor
  · linarith
  · linarith [Nat.lt_floor_add_one (x + B)]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
