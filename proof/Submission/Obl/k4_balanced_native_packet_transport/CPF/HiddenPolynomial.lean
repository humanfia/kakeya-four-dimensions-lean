/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/HiddenPolynomial.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.RawQuadraticSampling
import Submission.Obl.k4_balanced_native_packet_transport.CPF.Definitions
import Submission.Obl.k4_native_shear_source_transport.PolyAxis

/-! Connect the finite hidden-bin crossing test with the actual chart polynomial. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open Submission.Obl.k4_native_shear_source_transport

theorem coordinatePolynomial_derivative {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (a : σ → ℝ) (j : σ) :
    (coordinatePolynomial P a j).derivative =
      coordinatePolynomial (MvPolynomial.pderiv j P) a j := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [coordinatePolynomial]
  | add P Q hP hQ =>
    simpa only [coordinatePolynomial, MvPolynomial.eval₂_add, map_add,
      Polynomial.derivative_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    by_cases hi : i = j
    · subst i
      simpa [coordinatePolynomial, MvPolynomial.pderiv_mul, Polynomial.derivative_mul,
        mul_comm, add_comm] using hP
    · simpa [coordinatePolynomial, MvPolynomial.pderiv_mul, Polynomial.derivative_mul, hi,
        Ne.symm hi, mul_comm] using congrArg (fun q : Polynomial ℝ => q * Polynomial.C (a i)) hP

/-- Freeze the three exactly observed coordinates and retain the hidden variable. -/
noncomputable def hiddenPolynomial (P : Test) (z : EuclideanSpace ℝ (Fin 3)) : Polynomial ℝ :=
  coordinatePolynomial P ![z 0, z 1, z 2, 0] (3 : Fin 4)

theorem hiddenPolynomial_degree (P : Test) (z : EuclideanSpace ℝ (Fin 3)) :
    (hiddenPolynomial P z).natDegree ≤ P.totalDegree :=
  coordinatePolynomial_natDegree_le _ _ _

theorem hiddenPolynomial_eval (P : Test) (z : EuclideanSpace ℝ (Fin 3)) (w : ℝ) :
    (hiddenPolynomial P z).eval w = MvPolynomial.eval ![z 0, z 1, z 2, w] P := by
  rw [hiddenPolynomial, coordinatePolynomial_eval]
  apply congrArg (fun v : Fin 4 → ℝ => MvPolynomial.eval v P)
  ext i
  fin_cases i <;> simp [Function.update]

theorem hiddenPolynomial_derivative (P : Test) (z : EuclideanSpace ℝ (Fin 3)) :
    (hiddenPolynomial P z).derivative = hiddenPolynomial (MvPolynomial.pderiv 3 P) z :=
  coordinatePolynomial_derivative _ _ _

theorem hiddenPolynomial_eval_native (P : Test) (l : Trajectory) (t : ℝ) :
    (hiddenPolynomial P (WithLp.toLp 2 ![t, (x l t) 1, (x l t) 2])).eval ((x l t) 3) =
      MvPolynomial.eval (x l t) P := by
  rw [hiddenPolynomial_eval]
  apply congrArg (fun z : Fin 4 → ℝ => MvPolynomial.eval z P)
  ext i
  fin_cases i <;> rfl

/-- Every selected chart incidence passes the explicit midpoint crossing test of
its original observation label. -/
theorem Chart.hidden_label_mem {Nk κ j r B : ℝ} {M D T : ℕ}
    {E : Set Incidence} {c u : Spatial} {Q : Frame} {R : Test}
    {A : Set Trajectory} {F : Set Incidence} {ex : Prop}
    (hchart : Chart Nk M D κ T j r B E c u Q R A F ex)
    (hκ : 1 ≤ κ) (hB : 0 < B) {m : ℕ} (hm : 4 * κ ^ 2 ≤ m)
    {p : Incidence} (hp : p ∈ F) :
    (obs B (δ Nk r) p).2 ∈ sampledQuadraticBins
      (rescaleHiddenPolynomial (δ Nk r) B (hiddenPolynomial R (obs B (δ Nk r) p).1)) κ m := by
  have hδ : 0 < δ Nk r := by unfold δ; positivity
  obtain ⟨_, _, _, _, hdeg, _, _, _, _, hline, hsel, _⟩ := hchart
  obtain ⟨_, hA, ht, hfloor⟩ := hsel p hp
  obtain ⟨_, _, htime⟩ := hline p.1 hA
  obtain ⟨_, hval, hder, hder2⟩ := htime p.2 ht
  have hev (P : Test) :
      (hiddenPolynomial P (obs B (δ Nk r) p).1).eval ((x p.1 p.2) 3) =
        MvPolynomial.eval (x p.1 p.2) P := hiddenPolynomial_eval_native P p.1 p.2
  apply mem_rawSampledQuadraticBins _ ((hiddenPolynomial_degree _ _).trans hdeg)
    hκ hδ hB hm
  · rw [hev]
    exact hval
  · rw [hiddenPolynomial_derivative, hev]
    exact hfloor
  · rw [hiddenPolynomial_derivative, hev]
    exact hder
  · rw [hiddenPolynomial_derivative, hiddenPolynomial_derivative, hev]
    exact hder2

end Submission.Obl.k4_balanced_native_packet_transport.CPF
