import Submission.Obl.k4_homogeneous_native_pair_preparation.Front
import Submission.Obl.k4_quadratic_atlas_normalization.ChartMonotonicity
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal
import Submission.Lib.K4ChartLifting.Format
import Submission.Obl.k4_horizon_asymptotic_assembly.Fmt

namespace Submission.Obl.k4_homogeneous_native_pair_preparation

open MeasureTheory Set

/-- Removing the right endpoint preserves the old chart with one additional
affine sign test and the same geometric slack. -/
theorem chart_halfOpen {N κ j r B : ℝ} {M D T : ℕ}
    {E F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))} {ex : Prop}
    (hN : 2 ≤ N) (hκ : 0 < κ) (hB : 0 ≤ B)
    (hc : chart N M D κ T j r B E c u Q R A F ex) :
    chart N (M + 1) (max D 1) κ T j r B E c u Q R A
      (F ∩ {p | p.2 < (j + 1) / (2 : ℝ) ^ T}) ex := by
  have hN1 : 1 ≤ N := one_le_two.trans hN
  have hb : N ^ M + 1 ≤ N ^ (M + 1) := by
    rw [pow_succ]
    calc
      N ^ M + 1 ≤ N ^ M + N ^ M := add_le_add_right (one_le_pow₀ hN1) _
      _ = N ^ M * 2 := by ring
      _ ≤ N ^ M * N := mul_le_mul_of_nonneg_left hN (by positivity)
  have ht : fmt 7 1 1 {z : Fin 7 → ℝ | z 6 < (j + 1) / (2 : ℝ) ^ T} := by
    simpa only [fmt, Submission.Obl.k4_horizon_asymptotic_assembly.Outer.Fmt,
      MvPolynomial.eval_X] using
      Submission.Obl.k4_horizon_asymptotic_assembly.Outer.Fmt.lt_const
        (MvPolynomial.X (6 : Fin 7)) (by simp) ((j + 1) / (2 : ℝ) ^ T)
  have hf (i : ℕ) : fmt 7 (N ^ (M + 1)) (max D 1)
      {z : Fin 7 → ℝ | ((i, fun b : Fin 6 => z b.castSucc), z 6) ∈
        F ∩ {p | p.2 < (j + 1) / (2 : ℝ) ^ T}} :=
    Submission.Lib.K4ChartLifting.Fmt.mono
      (Submission.Lib.K4ChartLifting.Fmt.inter (hc.2.2.2.2.2.2.2.2.1 i).2 ht)
      hb le_rfl
  have hc' : chart N (M + 1) (max D 1) κ T j r B E c u Q R A F ex :=
    Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
      hN1 (by omega) (le_max_left _ _) hκ le_rfl hB hc id
  obtain ⟨hdet, hcu, hQ, hsize, hdeg, hcoeff, hAm, hFm, hfmt, hwhole, hsel, hex⟩ := hc'
  exact ⟨hdet, hcu, hQ, hsize, hdeg, hcoeff, hAm,
    hFm.inter (measurableSet_lt measurable_snd measurable_const),
    fun i => ⟨(hfmt i).1, hf i⟩, hwhole, fun p hp => hsel p hp.1, hex⟩

/-- The half-open chart set has exactly the original unconditioned mass. -/
theorem chart_halfOpen_mass {N κ j r B : ℝ} {M D T : ℕ}
    {E F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))} {ex : Prop}
    (hc : chart N M D κ T j r B E c u Q R A F ex)
    (ν : Measure (ℕ × (Fin 6 → ℝ))) :
    (ν.prod volume) (F ∩ {p | p.2 < (j + 1) / (2 : ℝ) ^ T}) = (ν.prod volume) F := by
  apply Submission.Obl.k4_quadratic_finite_greedy_cover.measure_trim_right
  intro p hp
  exact (hc.2.2.2.2.2.2.2.2.2.2.1 p hp).2.2.1.2

end Submission.Obl.k4_homogeneous_native_pair_preparation
