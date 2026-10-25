import Submission.Obl.k4_physical_parent_potential_candidates.DirectionalBounds

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData
open Submission.Lib.K4PotentialPlaneMenus
open Submission.Lib.K4CubicTests

noncomputable section

/-- A low-degree polynomial row fit bounds all higher pure directional jets,
in the exact units of its error. -/
theorem exists_polynomial_fit_directional_jet_bound (q r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : MvPolynomial (Fin 3) ℝ, P.totalDegree ≤ q →
      ∀ (fit : Polynomial ℝ), fit.natDegree ≤ q → fit.natDegree < r →
      ∀ (x u : Fin 3 → ℝ) (a E : ℝ), 0 < a → 0 ≤ E →
      (∀ s ∈ Icc (0:ℝ) 1, |eval (fun i => x i+s*u i) P/a-fit.eval s| ≤ E) →
      ∀ s ∈ Icc (0:ℝ) 1,
        |eval (fun i => x i+s*u i) ((polynomialDirectionalDerivative u)^[r] P)|/a ≤ C*E := by
  obtain ⟨C, hC, hbound⟩ :=
    Submission.Obl.k4_scalar_grid_parameter_preparation.exists_polynomial_iterated_derivative_bound q r
  refine ⟨C, hC, ?_⟩
  intro P hP fit hfitdeg hfitr x u a E ha hE hfit s hs
  let p0 := lineRestrR P x u
  let p : Polynomial ℝ := Polynomial.C a⁻¹*p0-fit
  have hp : p.natDegree ≤ q :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le
      ((Polynomial.natDegree_C_mul_le _ _).trans ((natDegree_lineRestrR_le P x u).trans hP)) hfitdeg)
  have hpb : ∀ s ∈ Icc (0:ℝ) 1, |p.eval s| ≤ E := by
    intro s hs
    simpa only [p, p0, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      eval_lineRestrR, div_eq_mul_inv, mul_comm] using hfit s hs
  have hdfit : (Polynomial.derivative^[r]) fit = 0 := Polynomial.iterate_derivative_eq_zero hfitr
  have hdp : (Polynomial.derivative^[r]) p =
      Polynomial.C a⁻¹*((Polynomial.derivative^[r]) p0) := by
    dsimp only [p]
    rw [Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_C_mul, hdfit, sub_zero]
  have hd0 : ((Polynomial.derivative^[r]) p0).eval s =
      eval (fun i => x i+s*u i) ((polynomialDirectionalDerivative u)^[r] P) := by
    calc
      _ = iteratedDeriv r (fun s => p0.eval s) s := by rw [iteratedDeriv_polynomial_eval]
      _ = _ := by simpa only [p0, eval_lineRestrR] using
          PotentialThirdJets.iteratedDeriv_eval_affine P x u r s
  have hb := hbound p E hp hE hpb s hs
  rw [hdp, Polynomial.eval_mul, Polynomial.eval_C, hd0, abs_mul, abs_inv, abs_of_pos ha] at hb
  simpa only [div_eq_mul_inv, mul_comm] using hb

namespace PhysicalSource

/-- Sharp pure jets: third and higher directional derivatives of Pot are
bounded in a units, with a constant fixed before the entire physical source. -/
theorem exists_uniform_sharp_pure_line_jet_bound (q : ℕ) (hq : 2 ≤ q) (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T j : ℕ} {ν : Measure Ln}
      {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
      (source : PhysicalSource q ν B a ζ d T j c u P0 A F H),
      ∀ (_hP0 : P0.totalDegree ≤ 2),
      ∀ l ∈ source.lineSet, ∀ s ∈ Icc (0:ℝ) 1,
        |eval (fun i => packetBase T j c u
          (l, (j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹*s) i)
          ((polynomialDirectionalDerivative (fun i => Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i))^[r]
            source.Pot)|/a ≤ C*ζ := by
  obtain ⟨C, hC, hjet⟩ := exists_polynomial_fit_directional_jet_bound q r
  refine ⟨C, hC, ?_⟩
  intro T j ν B a ζ d c u P0 A F H source hP0 l hl s hs
  let h : ℝ := ((2:ℝ)^T)⁻¹
  let t0 : ℝ := (j:ℝ)*h
  let direction : Fin 4 → ℝ := ![1,l.2 3,l.2 4,l.2 5]
  let signal := lineRestrR P0 (xp l t0) (fun i => h*direction i)
  let fit := Polynomial.C a⁻¹*(signal-Polynomial.C (ownIntercept T j c u P0 source.Pot l))
  have hsignal : signal.natDegree ≤ 2 := (natDegree_lineRestrR_le _ _ _).trans hP0
  have hfitdeg : fit.natDegree ≤ 2 :=
    (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_sub_le _ _).trans (max_le hsignal (by simp)))
  have heval (s : ℝ) : signal.eval s = eval (xp l (t0+h*s)) P0 := by
    dsimp only [signal]
    rw [eval_lineRestrR]
    apply congrArg (fun x : Fin 4 → ℝ => eval x P0)
    funext i
    fin_cases i <;> simp [xp, direction] <;> ring
  have hh : 0 < h := by dsimp [h]; positivity
  have hbase (s : ℝ) : (fun i => packetBase T j c u (l,t0+h*s) i) =
      fun i => packetOrigin T j c u l i+s*Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i := by
    have heq := packetBase_affine T j c u (l,t0+h*s)
    have hratio : ((t0+h*s)-(j:ℝ)*h)/h = s := by dsimp only [t0]; field_simp; ring
    dsimp only [h, t0] at hratio
    rw [hratio] at heq
    exact congrArg (fun z : P3 => fun i => z i) heq
  have hfit : ∀ s ∈ Icc (0:ℝ) 1,
      |eval (fun i => packetOrigin T j c u l i+
          s*Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i) source.Pot/a-
        fit.eval s| ≤ ζ := by
    intro s hs
    have ht : t0+h*s ∈ Icc ((j:ℝ)*h) (((j:ℝ)+1)*h) := by
      dsimp only [t0]
      constructor <;> nlinarith [hs.1, hs.2]
    have hf := source.line_fit l hl (t0+h*s) ht
    rw [hbase s] at hf
    have heq : |eval (fun i => packetOrigin T j c u l i+
          s*Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i) source.Pot/a-
        fit.eval s| =
      |(eval (xp l (t0+h*s)) P0-
        eval (fun i => packetOrigin T j c u l i+
          s*Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i) source.Pot)-
        ownIntercept T j c u P0 source.Pot l|/a := by
      dsimp only [fit]
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_C, heval]
      calc
        _ = |(-((eval (xp l (t0+h*s)) P0-
          eval (fun i => packetOrigin T j c u l i+
            s*Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i) source.Pot)-
          ownIntercept T j c u P0 source.Pot l)/a)| := by congr 1; ring
        _ = _ := by rw [abs_div, abs_neg, abs_of_pos source.a_pos]
    rw [heq]
    exact (div_le_iff₀ source.a_pos).2 (by nlinarith [hf])
  have hb := hjet source.Pot source.degree fit (hfitdeg.trans hq) (hfitdeg.trans_lt (by omega))
    (fun i => packetOrigin T j c u l i)
    (fun i => Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i) a ζ source.a_pos
    (source.ε_pos.trans_le source.ε_le).le hfit s hs
  change |eval (fun i => packetBase T j c u (l,t0+h*s) i) _|/a ≤ _
  rw [hbase]
  exact hb

variable {q T j : ℕ} {ν : Measure Ln}
  {B a ζ d : ℝ} {c u : P2} {P0 : Po} {A : Set Ln} {F H : Set Ev}
  (source : PhysicalSource q ν B a ζ d T j c u P0 A F H)

/-- The source-indexed form of the uniform sharp jet estimate. -/
theorem exists_sharp_pure_line_jet_bound (hq : 2 ≤ q) (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hP0 : P0.totalDegree ≤ 2),
      ∀ l ∈ source.lineSet, ∀ s ∈ Icc (0:ℝ) 1,
        |eval (fun i => packetBase T j c u
          (l, (j:ℝ)*((2:ℝ)^T)⁻¹+((2:ℝ)^T)⁻¹*s) i)
          ((polynomialDirectionalDerivative (fun i => Submission.Lib.K4OriginalCellSampling.Sampling.lift (v l) i))^[r]
            source.Pot)|/a ≤ C*ζ := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_sharp_pure_line_jet_bound q hq r hr
  exact ⟨C,hC,hbound source⟩

end PhysicalSource

end

end Submission.Obl.k4_physical_parent_potential_candidates
