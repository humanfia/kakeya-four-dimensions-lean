-- Adapted from LOT tree oai_074 obligation o062 (k4_scalar_mesh_projection), session x0212,
-- branch x0212 at commit 82cea2e4, file Submission/Obl/k4_scalar_mesh_projection/OriginalWholeBlockFields.lean;
-- only the namespace was renamed into o230's.
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.OriginalLongRows
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.OriginalBlockRemez
import Submission.Obl.k4_scalar_grid_cartesian_field.Cart.LongRowDirectionalField

namespace Submission.Obl.k4_scalar_grid_cartesian_field.Cart

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4PolynomialPotential
open Submission.Lib.K4ScalarSwitching.PolynomialDegree
open scoped ENNReal

/-- An original source set carrying component field fits yields an
original retained set with the directional equation throughout the
whole block. The prior mass and relative row length stay explicit. -/
theorem exists_original_whole_block_field_rows {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure (α × ℝ))
    (C m t0 h η V E₀ E₁ : ℝ) (hC : 0 < C) (hm : 0 < m) (hh : 0 < h)
    (hη : 0 < η) (hη1 : η ≤ 1) (hV0 : 0 ≤ V) (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁)
    (hbudget : 2*C*h*η ≤ m) (hdom : μ ≤ ENNReal.ofReal C • (ν.prod volume))
    (D : ℕ) (P : Fin 2 → MvPolynomial (Fin 2) ℝ) (hP : ∀ e, (P e).totalDegree ≤ D)
    (curve : α → Fin 2 → Polynomial ℝ) (hcurve : ∀ a e, (curve a e).natDegree ≤ 1)
    (T : α → Polynomial ℝ) (hT : ∀ a, (T a).natDegree ≤ 2)
    (v : α → ℝ) (G : Fin 2 → α × ℝ → ℝ)
    (S : Set (α × ℝ)) (hSm : MeasurableSet S)
    (hStime : ∀ p ∈ S, p.2 ∈ Icc t0 (t0+h))
    (hmass : ENNReal.ofReal m*ν univ ≤ μ S)
    (hV : ∀ p ∈ S, |v p.1| ≤ V)
    (hgraph : ∀ p ∈ S, |(T p.1).eval p.2-G 0 p-v p.1*G 1 p| ≤ E₀)
    (hfield : ∀ p ∈ S, ∀ e,
      |G e p-eval (fun j => (curve p.1 j).eval p.2) (P e)| ≤ E₁) :
    ∃ U : Set (α × ℝ), MeasurableSet U ∧ U ⊆ S ∧
      ENNReal.ofReal (m/2)*ν univ ≤ μ U ∧
      ∀ p ∈ U, ∀ t ∈ Icc t0 (t0+h),
        |(T p.1).eval t-eval (fun j => (curve p.1 j).eval t) (P 0)-
          v p.1*eval (fun j => (curve p.1 j).eval t) (P 1)| ≤
          (8*((D : ℝ)+3)/η)^(D+2)*(E₀+(1+V)*E₁) := by
  obtain ⟨U,hUm,hUS,hUmass,hUrow⟩ := exists_original_long_rows ν μ C m hC hm hdom S hSm hmass
  let Q (a : α) : MvPolynomial (Fin 2) ℝ := P 0+MvPolynomial.C (v a)*P 1
  let R (a : α) : Polynomial ℝ := T a-MvPolynomial.aeval (curve a) (Q a)
  have hQ (a : α) : (Q a).totalDegree ≤ D :=
    degree_add_le (hP 0) ((degree_C_mul_le _ _).trans (hP 1))
  have hRdegree (a : α) : (R a).natDegree ≤ D+2 := by
    have hrow : (MvPolynomial.aeval (curve a) (Q a)).natDegree ≤ D := by
      simpa only [Nat.mul_one] using MvPolynomial.aeval_natDegree_le (Q a) (hQ a) (curve a) (hcurve a)
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le ((hT a).trans (Nat.le_add_left _ _)) (hrow.trans (Nat.le_add_right _ _)))
  have hReval (a : α) (t : ℝ) : (R a).eval t=
      (T a).eval t-eval (fun j => (curve a j).eval t) (P 0)-
        v a*eval (fun j => (curve a j).eval t) (P 1) := by
    dsimp only [R]
    rw [Polynomial.eval_sub]
    change (T a).eval t-(MvPolynomial.eval₂ Polynomial.C (curve a) (Q a)).eval t=_
    rw [eval_polynomial_substitution]
    simp only [Q,map_add,map_mul,eval_C]
    ring
  have hrowCost : h*η ≤ m/(2*C) :=
    (le_div_iff₀ (by positivity : 0 < 2*C)).2 (by nlinarith)
  refine ⟨U,hUm,hUS,hUmass,?_⟩
  intro p hp t ht
  have htrace : MeasurableSet (Prod.mk p.1 ⁻¹' S) :=
    hSm.preimage (measurable_const.prodMk measurable_id)
  have htraceBlock : Prod.mk p.1 ⁻¹' S ⊆ Icc t0 (t0+h) :=
    fun s hs => hStime (p.1,s) hs
  have htraceMass : ENNReal.ofReal (h*η) ≤ volume (Prod.mk p.1 ⁻¹' S) :=
    (ENNReal.ofReal_le_ofReal hrowCost).trans (hUrow p hp)
  have hfit (s : ℝ) (hs : s ∈ Prod.mk p.1 ⁻¹' S) :
      |(R p.1).eval s| ≤ E₀+(1+V)*E₁ := by
    rw [hReval]
    exact directional_residual_le_of_component_fits ((T p.1).eval s) (G 0 (p.1,s))
      (G 1 (p.1,s)) (eval (fun j => (curve p.1 j).eval s) (P 0))
      (eval (fun j => (curve p.1 j).eval s) (P 1)) (v p.1) V E₀ E₁
      (hV (p.1,s) hs) (hgraph (p.1,s) hs) (hfield (p.1,s) hs 0) (hfield (p.1,s) hs 1)
  have hremez := polynomial_remez_original_block (R p.1) (D+2) (hRdegree p.1)
    t0 h η (E₀+(1+V)*E₁) hh hη hη1 (by positivity)
    (Prod.mk p.1 ⁻¹' S) htrace htraceBlock htraceMass hfit t ht
  simpa only [hReval,Nat.cast_add,Nat.cast_ofNat,
    show (2 : ℝ)+1=3 by norm_num,add_assoc] using hremez

end Submission.Obl.k4_scalar_grid_cartesian_field.Cart
