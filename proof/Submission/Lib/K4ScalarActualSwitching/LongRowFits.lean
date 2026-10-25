/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit c44c664d046b76ec88237a3add62b482dd01d022,
Submission/Obl/k4_scalar_mesh_projection/LongRowFits.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4PolynomialRemez
import Submission.Lib.K4PolynomialPotential.TrajectoryFits

namespace Submission.Lib.K4ScalarActualSwitching

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4PolynomialRemez Submission.Lib.K4PolynomialPotential

/-- Univariate Remez on the normalized signed time interval. The good row
may be an arbitrary set; the estimate uses its outer Lebesgue measure. -/
theorem polynomial_remez_signed_interval (p : Polynomial ℝ) (D : ℕ)
    (hp : p.natDegree ≤ D) (S : Set ℝ) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (-1 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ t ∈ S, |p.eval t| ≤ E) :
    ∀ x ∈ Icc (-1 : ℝ) 1, |p.eval x| ≤ (16 * ((D : ℝ) + 1) / η) ^ D * E := by
  let A : Polynomial ℝ := Polynomial.C 2 * Polynomial.X - 1
  let q := p.comp A
  have hA : A.natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (Polynomial.natDegree_mul_le.trans (by simp)) (by simp))
  have hq : q.natDegree ≤ D :=
    Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hp hA).trans_eq (Nat.mul_one D))
  let T := (fun t : ℝ => 2 * t - 1) ⁻¹' S
  have hTS : T ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨hl, hu⟩ := hS ht
    change -1 ≤ 2 * t - 1 at hl
    change 2 * t - 1 ≤ 1 at hu
    constructor <;> linarith
  have hTvol : volume T = ENNReal.ofReal ((1 : ℝ) / 2) * volume S := by
    have hid : T = (fun t : ℝ => (2 : ℝ) • t) ⁻¹'
        ((fun t : ℝ => t + (-1)) ⁻¹' S) := by
      ext t
      change (2 * t - 1 ∈ S) ↔ (2 * t + (-1) ∈ S)
      rw [sub_eq_add_neg]
    rw [hid, volume.addHaar_preimage_smul (by norm_num : (2 : ℝ) ≠ 0),
      measure_preimage_add_right]
    norm_num
  have hTmass : ENNReal.ofReal (η / 2) ≤ volume T := by
    rw [hTvol, show η / 2 = ((1 : ℝ) / 2) * η by ring,
      ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul' le_rfl hmass
  have hTbound : ∀ t ∈ T, |q.eval t| ≤ E := by
    intro t ht
    simpa only [q, A, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one] using hbound _ ht
  have h := polynomial_remez_unit q D hq T
    (by positivity : 0 < η / 2) (by linarith : η / 2 ≤ 1) hE hTS hTmass hTbound
  intro x hx
  have hpoint : (x + 1) / 2 ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hvalue := h ((x + 1) / 2) hpoint
  have hback : 2 * ((x + 1) / 2) - 1 = x := by ring
  have hfactor : 8 * ((D : ℝ) + 1) / (η / 2) = 16 * ((D : ℝ) + 1) / η := by ring
  simpa only [q, A, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, hback, hfactor] using hvalue

/-- A quadratic trajectory fit on any long row extends to the entire time
interval. No interval component or measurable midpoint is selected. -/
theorem scalar_quadratic_fit_of_long_row (P : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hP : P.totalDegree ≤ D) (T : Polynomial ℝ) (hT : T.natDegree ≤ 2)
    (u v : ℝ) (S : Set ℝ) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Icc (-1 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hfit : ∀ t ∈ S, |eval ![t, u + t * v] P - T.eval t| ≤ E) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      |eval ![t, u + t * v] P - T.eval t| ≤
        (16 * ((D : ℝ) + 3) / η) ^ (D + 2) * E := by
  let q := scalarLineHom u v P - T
  have hq : q.natDegree ≤ D + 2 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact (natDegree_scalarLineHom_le P u v).trans (hP.trans (Nat.le_add_right _ _))
    · exact hT.trans (Nat.le_add_left _ _)
  have hbound : ∀ t ∈ S, |q.eval t| ≤ E := by
    intro t ht
    simpa only [q, Polynomial.eval_sub, eval_scalarLineHom] using hfit t ht
  have h := polynomial_remez_signed_interval q (D + 2) hq S hη hη1 hE hS hmass hbound
  intro t ht
  simpa only [q, Polynomial.eval_sub, eval_scalarLineHom, Nat.cast_add,
    Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num, add_assoc] using h t ht

end Submission.Lib.K4ScalarActualSwitching
