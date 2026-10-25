import Submission.Obl.k4_raw_localized_native_systems.Window.AlignedInverse
import Submission.Lib.K4ModelReduction.PlankCaps

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The full-time current strip controls the actual normal velocity of each
of its trajectories. -/
theorem native_strip_velocity {n : Plane} (hn : ‖n‖ = 1)
    {int sp thickness : ℝ} {l : Line}
    (hstrip : ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ n (y l t) - int - t * sp| ≤ thickness) :
    |inner ℝ n (v l - sp • n)| ≤ 2 * thickness := by
  have hself : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
  have h := Submission.Lib.K4ModelReduction.velocity_inner_le_of_full_time
    (y l 0) (v l) (int • n) (sp • n) n thickness ?_
  · simpa only [real_inner_comm] using h
  · intro t ht
    have hyt : y l 0 + t • v l = y l t := by
      have hh := Pairing.y_sub_y l 0 t
      simp only [sub_zero] at hh
      exact (add_comm _ _).trans (eq_add_of_sub_eq hh).symm
    rw [hyt, real_inner_comm, inner_sub_right, inner_sub_right,
      inner_smul_right, inner_smul_right, inner_smul_right, hself]
    simpa only [mul_one] using hstrip t ht

/-- The full-time scalar chart has the original native signal and current tangential coordinate. -/
theorem native_full_time_identities (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (n : Plane) {A : Set Line} {l : Line} (hl : l ∈ A) (t : ℝ) :
    scalarX (fullTimeCoefficients P (normalTangent n) A l) t = MvPolynomial.eval (x l t) P ∧
    scalarY (fullTimeCoefficients P (normalTangent n) A l) t = inner ℝ (normalTangent n) (y l t) := by
  refine ⟨fullTimeCoefficients_signal P hP _ hl t, ?_⟩
  rw [fullTimeCoefficients_position P _ hl t, tangentValue, real_inner_comm]

/-- Full-time normal strips supply the raw scalar-position and strip clauses
with the original current center and center velocity. -/
theorem native_family_geometry {C : ℕ} (P : Fin C → MvPolynomial (Fin 4) ℝ)
    (n : Fin C → Plane) (int sp thickness : Fin C → ℝ)
    (A : Fin C → Set Line) (F : Fin C → Set Point)
    (hn : ∀ a, ‖n a‖ = 1) (hth : ∀ a, 0 ≤ thickness a)
    (hF : ∀ a q, q ∈ F a → q.1 ∈ A a ∧ q.2 ∈ Icc (0 : ℝ) 1)
    (hstrip : ∀ a l, l ∈ A a → ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ (n a) (y l t) - int a - t * sp a| ≤ thickness a) :
    ∀ a, ‖n a‖ = 1 ∧ 0 ≤ thickness a ∧ ∀ q ∈ F a,
      scalarY (fullTimeCoefficients (P a) (normalTangent (n a)) (A a) q.1) q.2 =
        0 + inner ℝ (normalTangent (n a)) (y q.1 q.2) ∧
      |inner ℝ (n a) (y q.1 q.2 - int a • n a - q.2 • (sp a • n a))| ≤ thickness a := by
  intro a
  refine ⟨hn a, hth a, ?_⟩
  intro q hq
  obtain ⟨hqA, hqt⟩ := hF a q hq
  constructor
  · rw [fullTimeCoefficients_position (P a) _ hqA q.2, tangentValue, real_inner_comm,
      zero_add]
  · have hself : inner ℝ (n a) (n a) = 1 := by
      rw [real_inner_self_eq_norm_sq, hn a]
      norm_num
    simpa only [inner_sub_right, inner_smul_right, hself, mul_one] using
      hstrip a q.1 hqA q.2 hqt

end
end Submission.Obl.k4_raw_localized_native_systems.Window
