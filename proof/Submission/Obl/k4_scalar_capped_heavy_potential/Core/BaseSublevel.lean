/- Adapted (namespace renamed) from LOT tree oai_074 (this tree), obligation o062,
session x0511, branch x0511, commit f33e26edad,
Submission/Lib/K4ScalarCoreTools/Simulation/BaseSublevel.lean (an unadmitted lib candidate).
Its own credits follow unchanged. -/

/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarSimulation/BaseSublevel.lean at ccb7071c.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit 778c2ed,
Submission/Obl/k4_scalar_mesh_projection/BaseSublevel.lean.
-/

import Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientBounds
import Submission.Lib.K4ScalarSwitching.TensorRemez
import Submission.Lib.K4ScalarSwitching.SwitchPath
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ScalarSwitching.Switching
open Submission.Lib.K4PolynomialRemez
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

theorem polynomial_remez_two (P : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hP : P.totalDegree ≤ D) (S : Set (Fin 2 → ℝ)) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (0 : Fin 2 → ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |eval z P| ≤ E) :
    ∀ z ∈ Icc (0 : Fin 2 → ℝ) 1,
      |eval z P| ≤ (16 * ((D : ℝ) + 1) / η) ^ (2 * D) * E := by
  have hrow (a : ℝ) : ∃ q : Polynomial ℝ, q.natDegree ≤ D ∧
      ∀ t, q.eval t = eval (![a, t]) P := by
    obtain ⟨q, hq, he⟩ := coordinate_line_witness P hP (![a, 0]) 1
    refine ⟨q, hq, fun t => ?_⟩
    rw [he]
    apply congrArg (fun z : Fin 2 → ℝ => eval z P)
    ext i
    fin_cases i <;> simp
  have hcol (a : ℝ) : ∃ q : Polynomial ℝ, q.natDegree ≤ D ∧
      ∀ t, q.eval t = eval (![t, a]) P := by
    obtain ⟨q, hq, he⟩ := coordinate_line_witness P hP (![0, a]) 0
    refine ⟨q, hq, fun t => ?_⟩
    rw [he]
    apply congrArg (fun z : Fin 2 → ℝ => eval z P)
    ext i
    fin_cases i <;> simp
  exact separately_polynomial_remez_box _ (MvPolynomial.continuous_eval P) D
    hrow hcol S hη hη1 hE hS hmass hbound

/-- The symmetric-cube transfer follows the same affine volume argument
as x0212's SymmetricSublevel.lean (c48e045), now in the two base variables. -/
theorem polynomial_remez_symmetric_two (P : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hP : P.totalDegree ≤ D) (S : Set (Fin 2 → ℝ)) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (-1 : Fin 2 → ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |eval z P| ≤ E) :
    ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval z P| ≤ (64 * ((D : ℝ) + 1) / η) ^ (2 * D) * E := by
  let Q : MvPolynomial (Fin 2) ℝ := aeval (fun i => C (2 : ℝ) * X i - 1) P
  have hQ : Q.totalDegree ≤ D := by
    apply (degree_aeval_le P _ ?_).trans hP
    intro i
    apply degree_sub_le
    · exact (degree_C_mul_le _ _).trans (by simp)
    · simp
  have heval (z : Fin 2 → ℝ) : eval z Q = eval ((2 : ℝ) • z - 1) P := by
    dsimp only [Q]
    rw [eval_substitution]
    simp only [map_sub, map_mul, eval_C, eval_X, map_one]
    rfl
  let T : Set (Fin 2 → ℝ) := (fun z => (2 : ℝ) • z - 1) ⁻¹' S
  have hTS : T ⊆ Icc (0 : Fin 2 → ℝ) 1 := by
    intro z hz
    constructor <;> intro i
    · have h := (hS hz).1 i
      change (-1 : ℝ) ≤ 2 * z i - 1 at h
      change (0 : ℝ) ≤ z i
      linarith
    · have h := (hS hz).2 i
      change 2 * z i - 1 ≤ (1 : ℝ) at h
      change z i ≤ (1 : ℝ)
      linarith
  have hTvol : volume T = ENNReal.ofReal ((1 : ℝ) / 4) * volume S := by
    have hTdef : T = (fun z : Fin 2 → ℝ => (2 : ℝ) • z) ⁻¹'
        ((fun z : Fin 2 → ℝ => z + (-1)) ⁻¹' S) := by
      ext z
      change ((2 : ℝ) • z - 1 ∈ S) ↔ ((2 : ℝ) • z + (-1) ∈ S)
      rw [sub_eq_add_neg]
    rw [hTdef, volume.addHaar_preimage_smul (by norm_num : (2 : ℝ) ≠ 0),
      measure_preimage_add_right]
    norm_num [Module.finrank_fin_fun]
  have hTmass : ENNReal.ofReal (η / 4) ≤ volume T := by
    rw [hTvol, show η / 4 = ((1 : ℝ) / 4) * η by ring,
      ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul' le_rfl hmass
  have h := polynomial_remez_two Q D hQ T (by positivity : 0 < η / 4)
    (by linarith : η / 4 ≤ 1) hE hTS hTmass
    (fun z hz => by simpa only [heval] using hbound _ hz)
  intro x hx
  let z : Fin 2 → ℝ := fun i => (x i + 1) / 2
  have hz : z ∈ Icc (0 : Fin 2 → ℝ) 1 := by
    constructor <;> intro i
    · have h := hx.1 i
      change (-1 : ℝ) ≤ x i at h
      change (0 : ℝ) ≤ (x i + 1) / 2
      linarith
    · have h := hx.2 i
      change x i ≤ (1 : ℝ) at h
      change (x i + 1) / 2 ≤ (1 : ℝ)
      linarith
  have hback : (2 : ℝ) • z - 1 = x := by ext i; dsimp [z]; ring
  have hvalue := h z hz
  rw [heval, hback] at hvalue
  have hfactor : 16 * ((D : ℝ) + 1) / (η / 4) = 64 * ((D : ℝ) + 1) / η := by ring
  simpa only [hfactor] using hvalue

/-- A large coefficient of the curl polynomial forces high curl at all
but a power-small base volume. This supplies the starting-point discard
before the four-leg minor argument. -/
theorem exists_base_polynomial_sublevel_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ (e : Fin 2 →₀ ℕ) (κ η : ℝ), 0 < κ → 0 < η → η ≤ 1 → κ ≤ |P.coeff e| →
        volume {z : Fin 2 → ℝ | z ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
          |eval z P| ≤ κ * η ^ (2 * D) /
            (2 * C * (64 * ((D : ℝ) + 1)) ^ (2 * D))} < ENNReal.ofReal η := by
  obtain ⟨C, hC, hcoeff⟩ := exists_multivariate_coefficient_constant D
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro P hP e κ η hκ hη hη1 he
  let E : ℝ := κ * η ^ (2 * D) / (2 * C ^ 2 * (64 * ((D : ℝ) + 1)) ^ (2 * D))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let S : Set (Fin 2 → ℝ) := {z | z ∈ Icc (-1) 1 ∧ |eval z P| ≤ E}
  by_contra! hvol
  have hremez := polynomial_remez_symmetric_two P D hP S hη hη1 hE
    (fun _ hz => hz.1) hvol (fun _ hz => hz.2)
  have hunit : Icc (0 : Fin 2 → ℝ) 1 ⊆ Icc (-1 : Fin 2 → ℝ) 1 := by
    intro z hz
    refine ⟨?_, hz.2⟩
    intro i
    exact (by norm_num : (-1 : ℝ) ≤ 0).trans (hz.1 i)
  have h := hcoeff 2 P hP _ (by positivity) (fun z hz => hremez z (hunit hz)) e
  have hid : C ^ 2 * ((64 * ((D : ℝ) + 1) / η) ^ (2 * D) * E) = κ / 2 := by
    dsimp [E]
    rw [div_pow]
    field_simp
  rw [hid] at h
  linarith

/-- A base density ceiling transfers the polynomial small-value volume
bound to the original incidence law, with its unnormalized ceiling intact. -/
theorem exists_base_polynomial_discard_constant (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : MvPolynomial (Fin 2) ℝ), P.totalDegree ≤ D →
      ∀ (e : Fin 2 →₀ ℕ) (κ η : ℝ), 0 < κ → 0 < η → η ≤ 1 → κ ≤ |P.coeff e| →
        ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α)
          (base : α → Fin 2 → ℝ) (M : ENNReal), Measurable base →
          μ.map base ≤ M • volume →
          μ {a | base a ∈ Icc (-1 : Fin 2 → ℝ) 1 ∧
            |eval (base a) P| ≤ κ * η ^ (2 * D) /
              (2 * C * (64 * ((D : ℝ) + 1)) ^ (2 * D))} ≤ M * ENNReal.ofReal η := by
  obtain ⟨C, hC, hsub⟩ := exists_base_polynomial_sublevel_constant D
  refine ⟨C, hC, ?_⟩
  intro P hP e κ η hκ hη hη1 he α _ μ base M hbase hdom
  let threshold := κ * η ^ (2 * D) / (2 * C * (64 * ((D : ℝ) + 1)) ^ (2 * D))
  let Bad : Set (Fin 2 → ℝ) := {z | z ∈ Icc (-1) 1 ∧ |eval z P| ≤ threshold}
  have hBad : MeasurableSet Bad := measurableSet_Icc.inter
    (isClosed_le (MvPolynomial.continuous_eval P).abs continuous_const).measurableSet
  have h := Measure.le_iff.mp hdom Bad hBad
  rw [Measure.map_apply hbase hBad, Measure.smul_apply, smul_eq_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hsub P hP e κ η hκ hη hη1 he).le bot_le)

end Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching
