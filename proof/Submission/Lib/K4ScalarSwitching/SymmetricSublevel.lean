/-
Adapted from: here:o062
Original proof: x0212, commit c48e045; uses the imported x0511 coefficient and tensor APIs.
Owned source: Submission/Obl/k4_scalar_mesh_projection/SymmetricSublevel.lean.
-/

import Submission.Lib.K4ScalarSwitching.MinorSublevel
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

/-- Transfer the unit-cube Remez bound to the actual signed-increment cube.
The volume factor is exactly `2^4 = 16`. -/
theorem polynomial_remez_symmetric_four (P : MvPolynomial (Fin 4) ℝ) (D : ℕ)
    (hP : P.totalDegree ≤ D) (S : Set (Fin 4 → ℝ)) (hSm : MeasurableSet S)
    {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (-1 : Fin 4 → ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |eval z P| ≤ E) :
    ∀ z ∈ Icc (-1 : Fin 4 → ℝ) 1,
      |eval z P| ≤ (512 * ((D : ℝ) + 1) / η) ^ (4 * D) * E := by
  let Q : MvPolynomial (Fin 4) ℝ := aeval (fun i => C (2 : ℝ) * X i - 1) P
  have hQ : Q.totalDegree ≤ D := by
    apply (degree_aeval_le P _ ?_).trans hP
    intro i
    apply degree_sub_le
    · exact (degree_C_mul_le _ _).trans (by simp)
    · simp
  have heval (z : Fin 4 → ℝ) : eval z Q = eval (fun i => 2 * z i - 1) P := by
    have h := MvPolynomial.comp_aeval_apply
      (fun i : Fin 4 => C (2 : ℝ) * X i - 1) (MvPolynomial.aeval z) P
    simpa only [Q, MvPolynomial.aeval_eq_eval, map_sub, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, map_one] using h
  have hvec (z : Fin 4 → ℝ) : (fun i => 2 * z i - 1) = (2 : ℝ) • z - 1 := by
    funext i
    rfl
  let T : Set (Fin 4 → ℝ) := (fun z => (2 : ℝ) • z - 1) ⁻¹' S
  have hTm : MeasurableSet T := hSm.preimage (by fun_prop)
  have hTS : T ⊆ Icc (0 : Fin 4 → ℝ) 1 := by
    intro z hz
    have hl := (hS hz).1
    have hu := (hS hz).2
    constructor <;> intro i
    · have h := hl i
      change (-1 : ℝ) ≤ 2 * z i - 1 at h
      change (0 : ℝ) ≤ z i
      linarith
    · have h := hu i
      change 2 * z i - 1 ≤ (1 : ℝ) at h
      change z i ≤ (1 : ℝ)
      linarith
  have hTvol : volume T = ENNReal.ofReal ((1 : ℝ) / 16) * volume S := by
    have hTdef : T = (fun z : Fin 4 → ℝ => (2 : ℝ) • z) ⁻¹'
        ((fun z : Fin 4 → ℝ => z + (-1)) ⁻¹' S) := by
      ext z
      change ((2 : ℝ) • z - 1 ∈ S) ↔ ((2 : ℝ) • z + (-1) ∈ S)
      rw [sub_eq_add_neg]
    rw [hTdef, volume.addHaar_preimage_smul (by norm_num : (2 : ℝ) ≠ 0),
      measure_preimage_add_right]
    norm_num [Module.finrank_fin_fun]
  have hTmass : ENNReal.ofReal (η / 16) ≤ volume T := by
    rw [hTvol, show η / 16 = ((1 : ℝ) / 16) * η by ring,
      ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul' le_rfl hmass
  have hTbound : ∀ z ∈ T, |eval z Q| ≤ E := by
    intro z hz
    rw [heval, hvec]
    exact hbound _ hz
  have h := polynomial_remez_four Q D hQ T hTm
    (by positivity : 0 < η / 16) (by linarith : η / 16 ≤ 1) hE hTS hTmass hTbound
  intro x hx
  let z : Fin 4 → ℝ := fun i => (x i + 1) / 2
  have hz : z ∈ Icc (0 : Fin 4 → ℝ) 1 := by
    constructor <;> intro i
    · have hl := hx.1 i
      change (-1 : ℝ) ≤ x i at hl
      change (0 : ℝ) ≤ z i
      dsimp only [z]
      linarith
    · have hu := hx.2 i
      change x i ≤ (1 : ℝ) at hu
      change z i ≤ (1 : ℝ)
      dsimp only [z]
      linarith
  have hback : (fun i => 2 * z i - 1) = x := by
    funext i
    dsimp only [z]
    ring
  have hvalue := h z hz
  rw [heval, hback] at hvalue
  have hfactor : 32 * ((D : ℝ) + 1) / (η / 16) = 512 * ((D : ℝ) + 1) / η := by ring
  simpa only [hfactor] using hvalue

/-- The minor sublevel estimate on the full cube of signed increments.
The original polynomial's large linear coefficient is retained as the
normalization; no coefficient assertion after translation is needed. -/
theorem exists_symmetric_polynomial_sublevel_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 4) ℝ), P.totalDegree ≤ D →
      ∀ (i : Fin 4) (κ η : ℝ), 0 < κ → 0 < η → η ≤ 1 →
        κ ≤ |P.coeff (Finsupp.single i 1)| →
        volume {z : Fin 4 → ℝ | z ∈ Icc (-1 : Fin 4 → ℝ) 1 ∧
          |eval z P| ≤ κ * η ^ (4 * D) /
            (2 * C * (512 * ((D : ℝ) + 1)) ^ (4 * D))} < ENNReal.ofReal η := by
  obtain ⟨C, hC, hcoeff⟩ := exists_linear_coefficient_constant D
  refine ⟨C, hC, ?_⟩
  intro P hP i κ η hκ hη hη1 hi
  let E : ℝ := κ * η ^ (4 * D) / (2 * C * (512 * ((D : ℝ) + 1)) ^ (4 * D))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let S : Set (Fin 4 → ℝ) := {z | z ∈ Icc (-1) 1 ∧ |eval z P| ≤ E}
  have hSm : MeasurableSet S := measurableSet_Icc.inter
    (isClosed_le (MvPolynomial.continuous_eval P).abs continuous_const).measurableSet
  by_contra! hvol
  have hremez := polynomial_remez_symmetric_four P D hP S hSm hη hη1 hE
    (fun _ hz => hz.1) hvol (fun _ hz => hz.2)
  have hunit : Icc (0 : Fin 4 → ℝ) 1 ⊆ Icc (-1 : Fin 4 → ℝ) 1 := by
    intro z hz
    refine ⟨?_, hz.2⟩
    intro j
    exact (by norm_num : (-1 : ℝ) ≤ 0).trans (hz.1 j)
  have h := hcoeff P hP _ (by positivity) (fun z hz => hremez z (hunit hz)) i
  have hid : C * ((512 * ((D : ℝ) + 1) / η) ^ (4 * D) * E) = κ / 2 := by
    dsimp [E]
    rw [div_pow]
    field_simp
  rw [hid] at h
  linarith

end Submission.Lib.K4ScalarSwitching.Switching
