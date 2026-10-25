/-
Adapted from: here:o062
Original proof: x0511, branch x0511, commit bf52299; retained source-credit comment follows.
Owned source: Submission/Obl/k4_scalar_mesh_projection/TensorRemez.lean.
-/

/- From o062 session x0511, branch x0511, commit bf52299;
original file Submission/Obl/k4_scalar_mesh_projection/TensorRemez.lean. -/

import Submission.Lib.K4PolynomialRemez
import Submission.Lib.K4PolynomialPotential.Coordinate

namespace Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory
open Submission.Lib.K4PolynomialRemez
open Submission.Lib.K4PolynomialPotential
open MvPolynomial

abbrev SquarePoint := Fin 2 → ℝ

def unitSquare : Set SquarePoint := Icc 0 1

/-- Tensoring the accepted square Remez estimate gives a four-variable
estimate. The power loss depends only on the polynomial degree. -/
theorem product_square_remez (f : SquarePoint × SquarePoint → ℝ)
    (hf : Continuous f) (D : ℕ)
    (h₁ : ∀ b : SquarePoint, ∀ a : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ t, p.eval t = f (![a, t], b))
    (h₂ : ∀ b : SquarePoint, ∀ a : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ t, p.eval t = f (![t, a], b))
    (h₃ : ∀ a : SquarePoint, ∀ b : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ t, p.eval t = f (a, ![b, t]))
    (h₄ : ∀ a : SquarePoint, ∀ b : ℝ, ∃ p : Polynomial ℝ,
      p.natDegree ≤ D ∧ ∀ t, p.eval t = f (a, ![t, b]))
    (S : Set (SquarePoint × SquarePoint)) (hSmeas : MeasurableSet S) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ unitSquare ×ˢ unitSquare)
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |f z| ≤ E) :
    ∀ z ∈ unitSquare ×ˢ unitSquare,
      |f z| ≤ (32 * ((D : ℝ) + 1) / η) ^ (4 * D) * E := by
  let μ : Measure SquarePoint := volume.restrict unitSquare
  have hI : MeasurableSet unitSquare := measurableSet_Icc
  have : IsProbabilityMeasure μ := ⟨by
    simp [μ, unitSquare, Real.volume_Icc_pi]⟩
  have hμS : (μ.prod μ) S = volume S := by
    dsimp only [μ]
    rw [Measure.prod_restrict, Measure.restrict_apply hSmeas, inter_eq_left.mpr hS]
    rfl
  have hlarge := probability_large_fibers μ μ S hSmeas hη.le (hmass.trans_eq hμS.symm)
  let H : Set SquarePoint := {a | ENNReal.ofReal (η / 2) ≤ μ (Prod.mk a ⁻¹' S)}
  have hH : MeasurableSet H := measurableSet_le measurable_const
    (measurable_measure_prodMk_left hSmeas)
  have hHmass : ENNReal.ofReal (η / 2) ≤ volume (H ∩ unitSquare) := by
    change ENNReal.ofReal (η / 2) ≤ μ H at hlarge
    simpa only [μ, Measure.restrict_apply hH] using hlarge
  let A : ℝ := 32 * ((D : ℝ) + 1) / η
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hfactor : 16 * ((D : ℝ) + 1) / (η / 2) = A := by dsimp [A]; ring
  have hvertical : ∀ a ∈ H ∩ unitSquare, ∀ b ∈ unitSquare,
      |f (a, b)| ≤ A ^ (2 * D) * E := by
    intro a ha b hb
    have hslice : Prod.mk a ⁻¹' S ⊆ unitSquare := fun z hz => (hS hz).2
    have hsm : MeasurableSet (Prod.mk a ⁻¹' S) :=
      hSmeas.preimage (measurable_const.prodMk measurable_id)
    have hsliceMass : ENNReal.ofReal (η / 2) ≤ volume (Prod.mk a ⁻¹' S) := by
      have h := ha.1
      change ENNReal.ofReal (η / 2) ≤ μ (Prod.mk a ⁻¹' S) at h
      simpa only [μ, Measure.restrict_apply hsm, inter_eq_left.mpr hslice] using h
    have h := separately_polynomial_remez_box (fun b => f (a, b))
      (hf.comp (by fun_prop)) D (h₃ a) (h₄ a) (Prod.mk a ⁻¹' S)
      (by positivity : 0 < η / 2) (by linarith : η / 2 ≤ 1) hE hslice hsliceMass
      (fun z hz => hbound (a, z) hz) b hb
    simpa only [hfactor] using h
  intro z hz
  have h := separately_polynomial_remez_box (fun a => f (a, z.2))
    (hf.comp (by fun_prop)) D (h₁ z.2) (h₂ z.2) (H ∩ unitSquare)
    (by positivity : 0 < η / 2) (by linarith : η / 2 ≤ 1)
    (mul_nonneg (pow_nonneg hA _) hE) inter_subset_right hHmass
    (fun a ha => hvertical a ha z.2 hz.2) z.1 hz.1
  have heq : A ^ (2 * D) * (A ^ (2 * D) * E) = A ^ (4 * D) * E := by
    rw [show 4 * D = 2 * D + 2 * D by omega, pow_add]
    ring
  simpa only [hfactor, heq, A] using h

def pairCoordinates (z : SquarePoint × SquarePoint) : Fin 4 → ℝ :=
  ![z.1 0, z.1 1, z.2 0, z.2 1]

def splitFour : (Fin 4 → ℝ) ≃ᵐ SquarePoint × SquarePoint :=
  (MeasurableEquiv.arrowCongr'
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm (MeasurableEquiv.refl ℝ)).trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ))

theorem splitFour_symm_apply (z : SquarePoint × SquarePoint) :
    splitFour.symm z = pairCoordinates z := by
  funext i
  fin_cases i <;> rfl

theorem splitFour_apply (z : Fin 4 → ℝ) :
    splitFour z = (![z 0, z 1], ![z 2, z 3]) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

theorem volume_preserving_splitFour : MeasurePreserving splitFour := by
  exact (volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).comp
    (volume_preserving_arrowCongr'
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).symm (MeasurableEquiv.refl ℝ)
      (MeasurePreserving.id volume))

theorem splitFour_mem_unit (z : Fin 4 → ℝ) :
    splitFour z ∈ unitSquare ×ˢ unitSquare ↔ z ∈ Icc (0 : Fin 4 → ℝ) 1 := by
  rw [splitFour_apply]
  simp only [unitSquare, mem_prod, mem_Icc, Pi.le_def, Fin.forall_fin_succ,
    Pi.zero_apply, Pi.one_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.forall_fin_zero]
  tauto

theorem coordinate_line_witness {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) (a : Fin n → ℝ) (i : Fin n) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ D ∧
      ∀ t : ℝ, q.eval t = eval (Function.update a i t) P := by
  let q := coordinatePolynomialHom a i P
  refine ⟨q, ?_, fun t => eval_coordinatePolynomialHom P a i t⟩
  change (MvPolynomial.aeval
    (fun k => if k = i then Polynomial.X else Polynomial.C (a k)) P).natDegree ≤ D
  simpa only [Nat.mul_one] using MvPolynomial.aeval_natDegree_le (n := 1) P hP
    (fun k : Fin n => if k = i then Polynomial.X else Polynomial.C (a k))
    (fun k => by split_ifs <;> simp)

/-- The tensor estimate in the standard four-coordinate Lebesgue measure. -/
theorem polynomial_remez_four (P : MvPolynomial (Fin 4) ℝ) (D : ℕ)
    (hP : P.totalDegree ≤ D) (S : Set (Fin 4 → ℝ)) (hSm : MeasurableSet S)
    {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (0 : Fin 4 → ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |eval z P| ≤ E) :
    ∀ z ∈ Icc (0 : Fin 4 → ℝ) 1,
      |eval z P| ≤ (32 * ((D : ℝ) + 1) / η) ^ (4 * D) * E := by
  let f : SquarePoint × SquarePoint → ℝ := fun z => eval (pairCoordinates z) P
  have hf : Continuous f := (MvPolynomial.continuous_eval P).comp (by
    unfold pairCoordinates
    fun_prop)
  let T := splitFour.symm ⁻¹' S
  have hTm : MeasurableSet T := hSm.preimage splitFour.symm.measurable
  have hTS : T ⊆ unitSquare ×ˢ unitSquare := by
    intro z hz
    have h := (splitFour_mem_unit (splitFour.symm z)).mpr (hS hz)
    simpa only [MeasurableEquiv.apply_symm_apply] using h
  have hTvol : volume T = volume S :=
    (MeasurePreserving.symm splitFour volume_preserving_splitFour).measure_preimage hSm.nullMeasurableSet
  have hTbound : ∀ z ∈ T, |f z| ≤ E := by
    intro z hz
    simpa only [f, splitFour_symm_apply] using hbound (splitFour.symm z) hz
  have h₁ (b : SquarePoint) (a : ℝ) : ∃ q : Polynomial ℝ,
      q.natDegree ≤ D ∧ ∀ t, q.eval t = f (![a, t], b) := by
    obtain ⟨q, hq, he⟩ := coordinate_line_witness P hP (![a, 0, b 0, b 1]) 1
    refine ⟨q, hq, fun t => ?_⟩
    rw [he]
    apply congrArg (fun z : Fin 4 → ℝ => eval z P)
    funext i
    fin_cases i <;> simp [pairCoordinates]
  have h₂ (b : SquarePoint) (a : ℝ) : ∃ q : Polynomial ℝ,
      q.natDegree ≤ D ∧ ∀ t, q.eval t = f (![t, a], b) := by
    obtain ⟨q, hq, he⟩ := coordinate_line_witness P hP (![0, a, b 0, b 1]) 0
    refine ⟨q, hq, fun t => ?_⟩
    rw [he]
    apply congrArg (fun z : Fin 4 → ℝ => eval z P)
    funext i
    fin_cases i <;> simp [pairCoordinates]
  have h₃ (a : SquarePoint) (b : ℝ) : ∃ q : Polynomial ℝ,
      q.natDegree ≤ D ∧ ∀ t, q.eval t = f (a, ![b, t]) := by
    obtain ⟨q, hq, he⟩ := coordinate_line_witness P hP (![a 0, a 1, b, 0]) 3
    refine ⟨q, hq, fun t => ?_⟩
    rw [he]
    apply congrArg (fun z : Fin 4 → ℝ => eval z P)
    funext i
    fin_cases i <;> simp [pairCoordinates]
  have h₄ (a : SquarePoint) (b : ℝ) : ∃ q : Polynomial ℝ,
      q.natDegree ≤ D ∧ ∀ t, q.eval t = f (a, ![t, b]) := by
    obtain ⟨q, hq, he⟩ := coordinate_line_witness P hP (![a 0, a 1, 0, b]) 2
    refine ⟨q, hq, fun t => ?_⟩
    rw [he]
    apply congrArg (fun z : Fin 4 → ℝ => eval z P)
    funext i
    fin_cases i <;> simp [pairCoordinates]
  have h := product_square_remez f hf D h₁ h₂ h₃ h₄ T hTm hη hη1 hE hTS
    (hmass.trans_eq hTvol.symm) hTbound
  intro z hz
  have hz' := (splitFour_mem_unit z).mpr hz
  have hval := h (splitFour z) hz'
  simpa only [f, ← splitFour_symm_apply, MeasurableEquiv.symm_apply_apply] using hval

end Submission.Lib.K4ScalarSwitching.Switching
