import Submission.Obl.k4_scalar_tangent_isotropic_improvement.AffineCubic
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GridNormalization
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.NormalizedTrajectories

/-! Normalize actual packet trajectories and pull the recovered quadratic back to physical coordinates. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

open MvPolynomial

theorem exists_unitbox_trajectory_cubicTest_bound (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (a : Fin 5 → ℝ) (t₀ y₀ h H E : ℝ),
      p.totalDegree ≤ D → 0 < h → 0 < H → 0 ≤ E →
      (∀ t ∈ Set.Icc t₀ (t₀ + h),
        |a 2 + t * a 3 + t ^ 2 * a 4 -
          eval ![(t - t₀) / h, (a 0 + t * a 1 - y₀) / h] p| ≤ E) →
      ∀ t ∈ Set.Icc t₀ (t₀ + h),
        |cubicTest (affineBaseHom (fun _ => -2 * H) (4 * H) p)
          (normalizeBase H ![(t - t₀) / h, (a 0 + t * a 1 - y₀) / h]) (a 1)| ≤
            C * H ^ 3 * E := by
  obtain ⟨C, hC, hline⟩ := exists_normalized_trajectory_cubicTest_bound D
  refine ⟨64 * C, by positivity, ?_⟩
  intro p a t₀ y₀ h H E hp hh hH hE hfit t ht
  rw [cubicTest_affineBaseHom, normalizeBase_inverse hH.ne', abs_mul,
    abs_of_pos (pow_pos (by positivity : 0 < 4 * H) 3)]
  exact (mul_le_mul_of_nonneg_left (hline p a t₀ y₀ h E hp hh hE hfit t ht)
    (by positivity)).trans_eq (by ring)

/-- Pull a normalized quadratic back to the actual `(t,y)` coordinates. Its
coefficient budget depends on the packet scale and original bounds, independently
of the velocity separation used to discover it. -/
theorem exists_normalized_quadratic_pullback : ∃ C : ℝ, 0 < C ∧
    ∀ (q : MvPolynomial (Fin 2) ℝ) (z₀ : Fin 2 → ℝ) (H h B : ℝ),
      q.totalDegree ≤ 2 → 1 ≤ H → 0 < h → h ≤ 1 → 0 ≤ B →
      (∀ b, |q.coeff b| ≤ B) → (∀ i, |z₀ i| ≤ H) →
      ∃ Q : MvPolynomial (Fin 2) ℝ, Q.totalDegree ≤ 2 ∧
        (∀ b, |Q.coeff b| ≤ C * B * (H / h) ^ 4) ∧
        (∀ x, eval x Q = eval (normalizeBase H (fun i => (x i - z₀ i) / h)) q) := by
  obtain ⟨C, hC, hsub⟩ := exists_affine_substitution_coefficient_bound 2
  refine ⟨16 * C, by positivity, ?_⟩
  intro q z₀ H h B hq hH hh hh1 hB hqc hz₀
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  let s : ℝ := 1 / (4 * H * h)
  let a : Fin 2 → ℝ := fun i => 1 / 2 - z₀ i * s
  let L : ℝ := 2 * (H / h)
  have hbase : 1 ≤ H / h := (le_div_iff₀ hh).mpr (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hspos : 0 < s := by dsimp [s]; positivity
  have hsone : s ≤ 1 / h :=
    one_div_le_one_div_of_le hh (by nlinarith [mul_nonneg (sub_nonneg.mpr hH) hh.le])
  have hsabs : |s| ≤ 1 / h := by rwa [abs_of_pos hspos]
  have hs : |s| ≤ L := by
    rw [abs_of_pos hspos]
    calc
      s ≤ 1 / h := hsone
      _ ≤ H / h := div_le_div_of_nonneg_right hH hh.le
      _ ≤ L := by dsimp [L]; linarith
  have ha (i : Fin 2) : |a i| ≤ L := by
    calc
      |a i| ≤ |(1 : ℝ) / 2| + |z₀ i| * |s| := by
        simpa only [abs_mul] using abs_sub (1 / 2) (z₀ i * s)
      _ ≤ 1 / 2 + H * (1 / h) := by
        rw [show |(1 : ℝ) / 2| = 1 / 2 by norm_num]
        exact add_le_add le_rfl (mul_le_mul (hz₀ i) hsabs
          (abs_nonneg _) hHpos.le)
      _ = 1 / 2 + H / h := by ring
      _ ≤ L := by dsimp [L]; linarith only [hbase]
  obtain ⟨hd, hcoeff, heval⟩ := hsub q a s B L hq hB hL hqc ha hs
  refine ⟨affineBaseHom a s q, hd, ?_, ?_⟩
  · intro b
    exact (hcoeff b).trans_eq (by dsimp [L]; rw [mul_pow]; ring)
  · intro x
    rw [eval_affineBaseHom]
    apply congrArg (fun u : Fin 2 → ℝ => eval u q)
    ext i
    dsimp [a, s, normalizeBase]
    field_simp
    ring

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
