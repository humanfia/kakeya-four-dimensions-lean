import Submission.Obl.k4_stable_native_signal_oscillation.PolynomialBounds
import Submission.Lib.K4PolynomialRemezThree.Comparison
import Submission.Lib.K4ChartLifting.PolyAlgebra

/-! Remez calibration from nearby actual witnesses. The oscillation loss is
absorbed into the unknown coefficient norm, so no initial coefficient bound
is assumed. This is the analytic kernel for spreading occupied mesh cells.

Adapted from: here:o200 (session x0696, commit e204d918; as on branch x0829 at
commit 6f32949a), file
`Submission/Obl/k4_finite_projected_horizontal_candidates/DiscreteCoefficientCalibration.lean`,
moved into this obligation's namespace. -/

namespace Submission.Obl.k4_quadratic_mesh_coefficient_calibration

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ChartLifting

noncomputable section

theorem euclidean_dist_le_twice_coordinate_bound (x y : Fin 3 → ℝ) {delta : ℝ}
    (hd : 0 ≤ delta) (hxy : ∀ i, |x i - y i| ≤ delta) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) - WithLp.toLp 2 y‖ ≤ 2 * delta := by
  have hs : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) - WithLp.toLp 2 y‖ ^ 2 ≤
      3 * delta ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, delta ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (norm_nonneg _)
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using hxy i
      _ = 3 * delta ^ 2 := by simp
  nlinarith [norm_nonneg ((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) - WithLp.toLp 2 y)]

/-- The witness points can be discrete. Their nearby cell filling supplies
Lebesgue mass, and a sufficiently fine mesh absorbs coefficient oscillation.
`C` and `L` depend only on the fixed degree. -/
theorem exists_coefficient_bound_from_nearby_witnesses (D : ℕ) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ (S : Set (Fin 3 → ℝ)) (eta E delta : ℝ),
        0 < eta → eta ≤ 1 → 0 ≤ E → 0 ≤ delta →
        S ⊆ Icc (0 : Fin 3 → ℝ) 1 →
        (∀ x ∈ S, ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1) →
        ENNReal.ofReal eta ≤ volume S →
        (∀ x ∈ S, ∃ y : Fin 3 → ℝ,
          ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 ∧
            (∀ i, |x i - y i| ≤ delta) ∧ |eval y P| ≤ E) →
        2 * L * ((D + 1) ^ 3 : ℕ) * C *
          (32 * ((D : ℝ) + 1) / eta) ^ (3 * D) * delta ≤ 1 / 2 →
        ∀ e, |P.coeff e| ≤ 2 * ((D + 1) ^ 3 : ℕ) * C *
          (32 * ((D : ℝ) + 1) / eta) ^ (3 * D) * E := by
  obtain ⟨C, hC, hcoeff⟩ :=
    Submission.Lib.K4PolynomialRemezThree.exists_coefficient_bound_from_base_mass D
  obtain ⟨L, hL, hlip⟩ :=
    Submission.Obl.k4_stable_native_signal_oscillation.exists_polynomial_lipschitz_degree D
  refine ⟨C, L, hC, hL, ?_⟩
  intro P hP S eta E delta heta heta1 hE hdelta hS hnorm hmass hwitness hsmall e
  let A : ℝ := coeffL1 P
  let B : ℝ := C * (32 * ((D : ℝ) + 1) / eta) ^ (3 * D)
  let M : ℝ := ((D + 1) ^ 3 : ℕ)
  have hA : 0 ≤ A := coeffL1_nonneg P
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have htrace : ∀ x ∈ S, |eval x P| ≤ E + 2 * L * A * delta := by
    intro x hx
    obtain ⟨y, hy, hxy, hval⟩ := hwitness x hx
    have hh := hlip P hP A hA (abs_coeff_le_coeffL1 P)
      (WithLp.toLp 2 x) (WithLp.toLp 2 y) (hnorm x hx) hy
    change |eval x P - eval y P| ≤ L * A *
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3)) - WithLp.toLp 2 y‖ at hh
    have hdist := euclidean_dist_le_twice_coordinate_bound x y hdelta hxy
    have hosc : |eval x P - eval y P| ≤ 2 * L * A * delta := by
      exact hh.trans ((mul_le_mul_of_nonneg_left hdist (by positivity)).trans_eq (by ring))
    calc
      _ ≤ |eval x P - eval y P| + |eval y P| := by
        simpa only [sub_zero] using abs_sub_le (eval x P) (eval y P) 0
      _ ≤ 2 * L * A * delta + E := add_le_add hosc hval
      _ = E + 2 * L * A * delta := by ring
  have hc : ∀ d, |P.coeff d| ≤ B * (E + 2 * L * A * delta) :=
    hcoeff P hP S eta (E + 2 * L * A * delta) heta heta1 (by positivity) hS hmass htrace
  have hself : A ≤ M * (B * (E + 2 * L * A * delta)) :=
    coeffL1_le_of_coeff_le P hP _ hc
  have hsmall' : (2 * L * M * B * delta) ≤ 1 / 2 := by
    dsimp only [B, M]
    simpa only [mul_assoc] using hsmall
  have hmul := mul_le_mul_of_nonneg_right hsmall' hA
  have hnormbound : A ≤ 2 * M * B * E := by nlinarith [hself]
  exact (abs_coeff_le_coeffL1 P e).trans (by simpa only [A, M, B, mul_assoc] using hnormbound)

/-- Finite ORIGINAL-law cell caps give actual volume to the union of their
disjoint spatial cells. There is no claim of continuous domination of μ. -/
theorem filled_cell_volume_of_original_mass {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    (events : ι → Set Ω) (cells : ι → Set (Fin 3 → ℝ))
    (hdisj : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hmeas : ∀ i, MeasurableSet (cells i)) {m beta : ℝ}
    (hbeta : 0 < beta) (hmass : ENNReal.ofReal m ≤ μ univ)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ events i)
    (hcap : ∀ i, μ (events i) ≤ ENNReal.ofReal beta * volume (cells i)) :
    ENNReal.ofReal (m / beta) ≤ volume (⋃ i, cells i) := by
  classical
  have hcover' : μ univ ≤ μ (⋃ i, events i) := by
    apply measure_mono_ae
    filter_upwards [hcover] with p hp
    exact fun _ => mem_iUnion.mpr hp
  have hcell : ENNReal.ofReal m ≤ ENNReal.ofReal beta * volume (⋃ i, cells i) := by
    calc
      _ ≤ μ univ := hmass
      _ ≤ μ (⋃ i, events i) := hcover'
      _ ≤ ∑ i, μ (events i) := by simpa only [tsum_fintype] using measure_iUnion_le events
      _ ≤ ∑ i, ENNReal.ofReal beta * volume (cells i) := Finset.sum_le_sum fun i _ => hcap i
      _ = ENNReal.ofReal beta * volume (⋃ i, cells i) := by
        rw [measure_iUnion hdisj hmeas, tsum_fintype, Finset.mul_sum]
  rw [ENNReal.ofReal_div_of_pos hbeta,
    ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hbeta)) ENNReal.ofReal_ne_top]
  simpa only [mul_comm] using hcell

/-- The Remez bridge using just finite mesh-cell caps, occupied-cell
witnesses, and the ORIGINAL mass floor. The spatial cells can be arbitrarily
fine after the fixed density losses have been chosen. -/
theorem exists_coefficient_bound_from_original_cells (D : ℕ) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (Ω ι : Type*) [MeasurableSpace Ω] [Fintype ι]
        (μ : Measure Ω) (events : ι → Set Ω) (cells : ι → Set (Fin 3 → ℝ)),
      Pairwise (fun i j => Disjoint (cells i) (cells j)) →
      (∀ i, MeasurableSet (cells i)) →
      ∀ (P : MvPolynomial (Fin 3) ℝ), P.totalDegree ≤ D →
      ∀ m beta E delta : ℝ, 0 < m → 0 < beta → m ≤ beta → 0 ≤ E → 0 ≤ delta →
      ENNReal.ofReal m ≤ μ univ →
      (∀ᵐ p ∂μ, ∃ i, p ∈ events i) →
      (∀ i, μ (events i) ≤ ENNReal.ofReal beta * volume (cells i)) →
      (∀ i, cells i ⊆ Icc (0 : Fin 3 → ℝ) 1) →
      (∀ i x, x ∈ cells i → ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖ ≤ 1) →
      (∀ i, ∃ y : Fin 3 → ℝ,
        ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 ∧
          (∀ x ∈ cells i, ∀ j, |x j - y j| ≤ delta) ∧ |eval y P| ≤ E) →
      2 * L * ((D + 1) ^ 3 : ℕ) * C *
        (32 * ((D : ℝ) + 1) / (m / beta)) ^ (3 * D) * delta ≤ 1 / 2 →
      ∀ e, |P.coeff e| ≤ 2 * ((D + 1) ^ 3 : ℕ) * C *
        (32 * ((D : ℝ) + 1) / (m / beta)) ^ (3 * D) * E := by
  obtain ⟨C, L, hC, hL, hbound⟩ := exists_coefficient_bound_from_nearby_witnesses D
  refine ⟨C, L, hC, hL, ?_⟩
  intro Ω ι _ _ μ events cells hdisj hmeas P hP m beta E delta hm hbeta hmb hE hdelta
    hmass hcover hcap hcube hnorm hwitness hsmall e
  apply hbound P hP (⋃ i, cells i) (m / beta) E delta (div_pos hm hbeta)
    ((div_le_one hbeta).mpr hmb) hE hdelta
  · rintro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hcube i hi
  · rintro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hnorm i x hi
  · exact filled_cell_volume_of_original_mass μ events cells hdisj hmeas hbeta hmass hcover hcap
  · rintro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨y, hy, hxy, heval⟩ := hwitness i
    exact ⟨y, hy, hxy x hi, heval⟩
  · exact hsmall

end
end Submission.Obl.k4_quadratic_mesh_coefficient_calibration
