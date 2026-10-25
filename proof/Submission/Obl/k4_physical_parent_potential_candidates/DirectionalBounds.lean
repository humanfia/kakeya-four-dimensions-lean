import Submission.Obl.k4_physical_parent_potential_candidates.AffineLineFits
import Submission.Lib.K4PotentialPlaneMenus.PotentialThirdJets
import Submission.Obl.k4_scalar_grid_parameter_preparation.PolynomialComparison

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open Submission.Lib.K4PotentialPlaneMenus
open Submission.Lib.K4CubicTests

noncomputable section

/-- Every fixed pure directional jet above order one is small along an
actual affine row. The comparison constant depends only on degree and order. -/
theorem exists_affine_directional_jet_bound (q r : ℕ) (hq : 1 ≤ q) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ q →
      ∀ (x u : Fin 3 → ℝ) (h α β E : ℝ), 0 < h → 0 ≤ E →
      (∀ s ∈ Icc (0:ℝ) 1, |eval (fun i => x i+s*u i) P/h-(α+β*s)| ≤ E) →
      ∀ s ∈ Icc (0:ℝ) 1,
        |eval (fun i => x i+s*u i) ((polynomialDirectionalDerivative u)^[r] P)|/h ≤ C*E := by
  obtain ⟨C, hC, hbound⟩ :=
    Submission.Obl.k4_scalar_grid_parameter_preparation.exists_polynomial_iterated_derivative_bound q r
  refine ⟨C, hC, ?_⟩
  intro P hP x u h α β E hh hE hfit s hs
  let p0 := lineRestrR P x u
  let affine : Polynomial ℝ := Polynomial.C α + Polynomial.C β*Polynomial.X
  let p : Polynomial ℝ := Polynomial.C h⁻¹*p0-affine
  have haff : affine.natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
  have hp : p.natDegree ≤ q :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le
      ((Polynomial.natDegree_C_mul_le _ _).trans ((natDegree_lineRestrR_le P x u).trans hP))
      (haff.trans hq))
  have hpb : ∀ s ∈ Icc (0:ℝ) 1, |p.eval s| ≤ E := by
    intro s hs
    simpa only [p, p0, affine, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X, eval_lineRestrR, div_eq_mul_inv, mul_comm]
      using hfit s hs
  have hdaff : (Polynomial.derivative^[r]) affine = 0 :=
    Polynomial.iterate_derivative_eq_zero (haff.trans_lt (by omega))
  have hdp : (Polynomial.derivative^[r]) p =
      Polynomial.C h⁻¹*((Polynomial.derivative^[r]) p0) := by
    dsimp only [p]
    rw [Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_C_mul, hdaff, sub_zero]
  have hd0 : ((Polynomial.derivative^[r]) p0).eval s =
      eval (fun i => x i+s*u i) ((polynomialDirectionalDerivative u)^[r] P) := by
    calc
      _ = iteratedDeriv r (fun s => p0.eval s) s := by
        rw [iteratedDeriv_polynomial_eval]
      _ = _ := by
        simpa only [p0, eval_lineRestrR] using
          PotentialThirdJets.iteratedDeriv_eval_affine P x u r s
  have hb := hbound p E hp hE hpb s hs
  rw [hdp, Polynomial.eval_mul, Polynomial.eval_C, hd0, abs_mul, abs_inv, abs_of_pos hh] at hb
  simpa only [div_eq_mul_inv, mul_comm] using hb

namespace PhysicalSource

variable {q T j : ℕ} {ν : Measure Ln}
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

/-- The frozen potential has small second and higher pure jets at EVERY
source-line time, without choosing common directions across base cells. -/
theorem exists_pure_line_jet_bound (hq : 1 ≤ q) (r : ℕ) (hr : 2 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hP0 : P0.totalDegree ≤ 2),
      ∀ l ∈ source.lineSet, ∀ s ∈ Icc (0:ℝ) 1,
        |eval (fun i => packetBase T j c u
          (l, (j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹*s) i)
          ((polynomialDirectionalDerivative (fun i => Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i))^[r]
            source.Pot)|/((2:ℝ)^T)⁻¹ ≤ C*source.K*ζ := by
  obtain ⟨C, hC, hjet⟩ := exists_affine_directional_jet_bound q r hq hr
  refine ⟨9*C, by positivity, ?_⟩
  intro hP0 l hl s hs
  let h : ℝ := ((2:ℝ)^T)⁻¹
  let t0 : ℝ := (j:ℝ)*h
  have hh : 0 < h := by dsimp [h]; positivity
  have hbase (s : ℝ) : (fun i => packetBase T j c u (l,t0+h*s) i) =
      fun i => packetOrigin T j c u l i+s*Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i := by
    have heq := packetBase_affine T j c u (l,t0+h*s)
    have hratio : ((t0+h*s)-(j:ℝ)*h)/h = s := by dsimp only [t0]; field_simp; ring
    change packetBase T j c u (l,t0+h*s) = _ at heq
    dsimp only [h, t0] at hratio
    rw [hratio] at heq
    exact congrArg (fun z : P3 => fun i => z i) heq
  have hfit : ∀ s ∈ Icc (0:ℝ) 1,
      |eval (fun i => packetOrigin T j c u l i+
          s*Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i) source.Pot/h-
        (eval (fun i => packetOrigin T j c u l i) source.Pot/h+
          Submission.Lib.K4GlobalParentSignal.rate P0 l t0*s)| ≤ 9*source.K*ζ := by
    intro s hs
    have hf := source.normalized_affine_line_fit hP0 l hl s hs
    rw [hbase s] at hf
    exact hf
  have hb := hjet source.Pot source.degree (fun i => packetOrigin T j c u l i)
    (fun i => Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i) h
    (eval (fun i => packetOrigin T j c u l i) source.Pot/h)
    (Submission.Lib.K4GlobalParentSignal.rate P0 l t0) (9*source.K*ζ) hh
    (by have hK := source.K_two; have hζ := source.ε_pos.trans_le source.ε_le; positivity) hfit s hs
  change |eval (fun i => packetBase T j c u (l,t0+h*s) i) _|/h ≤ _
  rw [hbase]
  convert hb using 1 <;> ring

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
