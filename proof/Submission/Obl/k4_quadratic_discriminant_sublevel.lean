import Mathlib
import ChallengeDeps
import Submission.Obl.k4_quadratic_discriminant_safe_paths.Anchor
set_option linter.unusedVariables false

/-!
# Quadratic discriminant sublevel estimate

The accepted anchor estimate from the safe-path obligation bounds the sublevel
volume by `128 * θ` times the fixed ball volume. Set `θ = N ^ (-4 * a)` and
`CD = Cs + 9`; taking `N ^ a` large absorbs both fixed constants.
-/

theorem Submission.k4_quadratic_discriminant_sublevel : ∀ Cs : ℕ, 0 < Cs → ∃ CD : ℝ, 0 < CD ∧ ∀ a : ℝ, 0 < a → ∃ N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N → ∀ (p : MvPolynomial (Fin 3) ℝ) (α : EuclideanSpace ℝ (Fin 3)), p.totalDegree ≤ 2 → (∀ d, |p.coeff d| ≤ N ^ a) → ‖α‖ ≤ 1 / 8 → (N ^ a) ^ (-(Cs : ℝ)) ≤ |MvPolynomial.eval (fun i => α i) p| → MeasureTheory.volume {z : EuclideanSpace ℝ (Fin 3) | ‖z‖ ≤ 1 / 8 ∧ |MvPolynomial.eval (fun i => z i) p| < N ^ (-(CD * a))} ≤ ENNReal.ofReal (N ^ (-(3 * a))) := by
  intro Cs hCs
  refine ⟨(Cs : ℝ) + 9, by positivity, ?_⟩
  intro a ha
  let B : Set (EuclideanSpace ℝ (Fin 3)) := Metric.closedBall 0 (1 / 8)
  have hBfinite : MeasureTheory.volume B ≠ ⊤ :=
    MeasureTheory.measure_closedBall_lt_top.ne
  have hlim := tendsto_rpow_atTop ha
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (Filter.eventually_gt_atTop
      (max 576 (128 * (MeasureTheory.volume B).toReal))))
  refine ⟨max 2 N₀, ?_⟩
  intro N hN p α hp _hcoeff hα hvalue
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by linarith
  have hlarge := hN₀ N ((le_max_right _ _).trans hN)
  have h576 : 576 < N ^ a := (le_max_left _ _).trans_lt hlarge
  have hconstant : 128 * (MeasureTheory.volume B).toReal ≤ N ^ a :=
    ((le_max_right _ _).trans_lt hlarge).le
  have hθ : 0 < N ^ (-(4 * a)) := Real.rpow_pos_of_pos hNpos _
  have hθ1 : N ^ (-(4 * a)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hgap : 576 * N ^ (-(((Cs : ℝ) + 9) * a)) <
      (N ^ a) ^ (-(Cs : ℝ)) * (N ^ (-(4 * a))) ^ 2 := by
    calc
      _ < N ^ a * N ^ (-(((Cs : ℝ) + 9) * a)) :=
        mul_lt_mul_of_pos_right h576 (Real.rpow_pos_of_pos hNpos _)
      _ = _ := by
        rw [← Real.rpow_mul hNpos.le, ← Real.rpow_mul_natCast hNpos.le,
          ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
        congr 1
        ring
  have hbound :=
    Submission.Obl.k4_quadratic_discriminant_safe_paths.volume_anchor_sublevel_le
      p hp α hα hθ hθ1 (Real.rpow_nonneg hNpos.le _) hvalue hgap
  calc
    MeasureTheory.volume {z : EuclideanSpace ℝ (Fin 3) |
        ‖z‖ ≤ 1 / 8 ∧ |MvPolynomial.eval (fun i => z i) p| <
          N ^ (-(((Cs : ℝ) + 9) * a))} ≤
        MeasureTheory.volume {z : EuclideanSpace ℝ (Fin 3) |
          z ∈ B ∧ |MvPolynomial.eval (fun i => z i) p| ≤
            N ^ (-(((Cs : ℝ) + 9) * a))} := by
      apply MeasureTheory.measure_mono
      intro z hz
      exact ⟨mem_closedBall_zero_iff.mpr hz.1, hz.2.le⟩
    _ ≤ ENNReal.ofReal (128 * N ^ (-(4 * a))) * MeasureTheory.volume B := hbound
    _ = ENNReal.ofReal
        ((128 * N ^ (-(4 * a))) * (MeasureTheory.volume B).toReal) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 128 * N ^ (-(4 * a))),
        ENNReal.ofReal_toReal hBfinite]
    _ ≤ ENNReal.ofReal (N ^ (-(3 * a))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        (128 * N ^ (-(4 * a))) * (MeasureTheory.volume B).toReal =
            (128 * (MeasureTheory.volume B).toReal) * N ^ (-(4 * a)) := by ring
        _ ≤ N ^ a * N ^ (-(4 * a)) :=
          mul_le_mul_of_nonneg_right hconstant hθ.le
        _ = N ^ (-(3 * a)) := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
