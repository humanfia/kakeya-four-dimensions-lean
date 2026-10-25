import Submission.Obl.k4_algebraic_sheet_bound.AnalyticStability
import Submission.Obl.k4_algebraic_sheet_bound.Anchor
import Submission.Obl.k4_algebraic_sheet_bound.LastVar
import Submission.Obl.k4_algebraic_sheet_bound.LineGeometry
import Submission.Obl.k4_algebraic_sheet_bound.FamilyContinuity

namespace Submission.Obl.k4_algebraic_sheet_bound
open Set Metric Filter MvPolynomial
open scoped Topology

theorem uniform_basis_sheet_bound (n D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (c : Fin (polyDim n D) → ℂ) (f : EuclideanSpace ℂ (Fin n) → ℂ),
      ‖c‖ = 1 → DifferentiableOn ℂ f (ball 0 4) →
      (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin n)) 4,
        eval (Fin.snoc (fun i => z i) (f z)) (polyOf c) = 0) →
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ (1 : ℝ) / 2 →
        ‖f (WithLp.toLp 2 (fun i : Fin n => (x i : ℂ)))‖ ≤ 1) →
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ 1 → ‖f z‖ ≤ C := by
  classical
  by_contra h
  push Not at h
  have hex (j : ℕ) := h ((j : ℝ) + 1) (by positivity)
  choose c f hc hf hroot hbase z hz hlarge using hex
  let K := sphere (0 : Fin (polyDim n D) → ℂ) 1 ×ˢ
    closedBall (0 : EuclideanSpace ℂ (Fin n)) 1
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  have huK (j : ℕ) : (c j, z j) ∈ K := by
    exact ⟨by simpa only [mem_sphere, dist_zero_right] using hc j,
      by simpa only [mem_closedBall, dist_zero_right] using hz j⟩
  obtain ⟨p, hp, φ, hφ, hu⟩ := hK.tendsto_subseq huK
  have hpc : p.1 ≠ 0 := by
    have hnorm : ‖p.1‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hp.1
    intro hzero
    simp [hzero] at hnorm
  have hP : polyOf p.1 ≠ 0 := polyOf_ne_zero hpc
  have hlc : (lastVar (polyOf p.1)).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (lastVar_ne_zero hP)
  obtain ⟨xr, hxr, hanchor⟩ := exists_real_anchor hlc
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun i : Fin n => (xr i : ℂ))
  have hx : ‖x‖ ≤ 1 / 2 := by simpa only [x, norm_complexify] using hxr
  let H : ((Fin (polyDim n D) → ℂ) × EuclideanSpace ℂ (Fin n)) → ℂ → ℂ → ℂ :=
    fun q t w => eval (Fin.snoc (fun i => x i + t * (q.2 i - x i)) w) (polyOf q.1)
  have hH : Continuous (fun q : ((Fin (polyDim n D) → ℂ) × EuclideanSpace ℂ (Fin n)) × (ℂ × ℂ) =>
      H q.1 q.2.1 q.2.2) := continuous_line_eval_polyOf x
  let Q := lineRestrict (polyOf p.1) (fun i => x i) (fun i => p.2 i)
  have hlim (t w : ℂ) : H p t w = (Q.map (Polynomial.evalRingHom t)).eval w :=
    (lineRestrict_eval (polyOf p.1) (fun i => x i) (fun i => p.2 i) t w).symm
  have hlead : Q.leadingCoeff.eval 0 ≠ 0 := by
    dsimp only [Q]
    rw [lineRestrict_leadingCoeff_eval_zero _ _ _ hanchor]
    exact hanchor
  let g : ℕ → ℂ → ℂ := fun j t => f (φ j) (x + t • (z (φ j) - x))
  have hg (j : ℕ) : DifferentiableOn ℂ (g j) (ball 0 2) :=
    differentiableOn_affine_line (hf (φ j)) hx (hz (φ j))
  have hgr (j : ℕ) (t : ℂ) (ht : t ∈ ball 0 2) :
      H ((fun j => (c j, z j)) (φ j)) t (g j t) = 0 := by
    exact hroot (φ j) (x + t • (z (φ j) - x)) (affine_line_mem_ball_four hx (hz (φ j)) ht)
  have hgb (j : ℕ) : ‖g j 0‖ ≤ 1 := by
    simpa [g, x] using hbase (φ j) xr hxr
  obtain ⟨R, hRpos, hR⟩ := eventually_bound_of_polynomial_limit hu H hH Q hlim hlead g hg hgr hgb
  obtain ⟨N, hN⟩ := exists_nat_gt R
  obtain ⟨j, hj, hjN⟩ := (hR.and (eventually_ge_atTop N)).exists
  have hNj : (N : ℝ) ≤ φ j := by exact_mod_cast hjN.trans (hφ.id_le j)
  have hline : x + (1 : ℂ) • (z (φ j) - x) = z (φ j) := by module
  have hj' : ‖f (φ j) (z (φ j))‖ ≤ R := by simpa only [g, hline] using hj
  have := hlarge (φ j)
  linarith

end Submission.Obl.k4_algebraic_sheet_bound
