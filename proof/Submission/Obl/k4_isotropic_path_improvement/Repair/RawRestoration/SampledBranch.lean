-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawRestoration/SampledBranch.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
-- Adapted from this LOT tree o143/x0542, commit f027eb90,
-- Submission/Obl/k4_isotropic_discovery_of_local_restoration/SampledBranch.lean.
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.NormalizedCandidate
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.AffineDistance

/-! The finite analytic interface used before local degree restoration. -/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration

noncomputable section

open MeasureTheory MvPolynomial

/-- A real function with a holomorphic algebraic extension on a fixed enlargement.
The relation degree is independent of the size of its coefficients. -/
def HasRealExtension (D : ℕ) (f : Base → ℝ) : Prop :=
  ∃ (F : EuclideanSpace ℂ (Fin 3) → ℂ) (P : MvPolynomial (Fin 4) ℂ),
    P ≠ 0 ∧ P.totalDegree ≤ D ∧
    ContDiffOn ℂ ⊤ F (Metric.ball 0 4) ∧
    (∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      eval (Fin.snoc (fun i : Fin 3 => z i) (F z)) P = 0) ∧
    ∀ x ∈ Metric.ball (0 : Base) 4,
      F (WithLp.toLp 2 (fun i : Fin 3 => (x i : ℂ))) = (f x : ℂ)

/-- The requested exponent controls all jets through order six, including
derivatives relative to the best affine error. -/
def DenseJetBound (D J : ℕ) : Prop :=
  ∀ (A : ℝ), 2 ≤ A → ∀ (f : Base → ℝ), HasRealExtension D f →
    (∀ (E : Set Base) (v : ℝ), MeasurableSet E →
      E ⊆ Metric.closedBall (0 : Base) 1 →
      ENNReal.ofReal A⁻¹ ≤ volume E → 0 ≤ v →
      (∀ x ∈ E, |f x| ≤ v) →
      ∀ j : ℕ, j ≤ 6 → ∀ x ∈ Metric.closedBall (0 : Base) 2,
        ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * v) ∧
    (∀ (c : ℝ) (L : Base →L[ℝ] ℝ) (ε : ℝ), 0 < ε →
      (∀ x ∈ Metric.closedBall (0 : Base) 1, |f x - c - L x| ≤ ε) →
      ∀ j : ℕ, 2 ≤ j → j ≤ 6 →
      ∀ x ∈ Metric.closedBall (0 : Base) 2,
        ‖iteratedFDeriv ℝ j f x‖ ≤ A ^ J * ε)

def DenseJetAssertion : Prop := ∀ D : ℕ, ∃ J : ℕ, 1 ≤ J ∧ DenseJetBound D J

/-- Input to the finite jet argument. The four missing global estimates
are replaced by values on a common real set of controlled volume. -/
structure SampledBranchData (Cloc J D : ℕ) where
  A : ℝ
  Z : ℝ
  a : ℝ
  b : ℝ
  h : ℝ
  s : ℝ
  S : Poly
  f : Base → ℝ
  p : Fin 7 → Base
  E : Set Base
  two_le_A : 2 ≤ A
  loss_le_Z : A ^ (J + 1) ≤ Z
  b_pos : 0 < b
  b_le_a : b ≤ a
  a_le_one : a ≤ 1
  h_pos : 0 < h
  small_scale : h * (A ^ (J + 1)) ^ Cloc ≤ b / a
  s_nonneg : 0 ≤ s
  inv_b_le_Z : b⁻¹ ≤ Z
  S_degree : S.totalDegree ≤ 2
  S_coeff : ∀ e, |S.coeff e| ≤ Z
  S_curvature : ∀ u : Base, ∀ w : ℝ,
    |eval ![u 0, u 1, u 2, w] (pderiv 3 (pderiv 3 S))| ≤ A / a
  smooth : ContDiffOn ℝ 6 f (Metric.ball 0 3)
  value_zero : |f 0| ≤ Z
  first_zero : ‖fderiv ℝ f 0‖ ≤ Z
  second_zero : ‖iteratedFDeriv ℝ 2 f 0‖ ≤ Z
  affine_distance : ∀ (c : ℝ) (L : Base →L[ℝ] ℝ),
    ∃ u ∈ Metric.closedBall (0 : Base) 1, s ≤ |f u - c - L u|
  affine_approximation : ∀ ε : ℝ, s < ε →
    ∃ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∀ u ∈ Metric.closedBall (0 : Base) 1, |f u - c - L u| ≤ ε
  directions : ∀ i, p i 0 = 1 ∧ ‖p i‖ ≤ A
  transverse : ∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
    A⁻¹ ≤ |Matrix.det (Matrix.of fun r t : Fin 3 => (![p i, p j, p k] r) t)|
  measurable_E : MeasurableSet E
  E_subset : E ⊆ Metric.closedBall (0 : Base) 1
  E_mass : ENNReal.ofReal A⁻¹ ≤ volume E
  f_extension : HasRealExtension D f
  second_extension : ∀ i : Fin 7,
    HasRealExtension D (fun v => iteratedFDeriv ℝ 2 f v (fun _ => p i))
  residual_extension : HasRealExtension D
    (fun v => eval ![v 0, v 1, v 2, f v] S / a)
  third_extension : ∀ i : Fin 7, HasRealExtension D
    (fun v => iteratedFDeriv ℝ 3
      (fun z => eval ![z 0, z 1, z 2, f z] S / a) v (fun _ => p i))
  second_samples : ∀ i : Fin 7, ∀ u ∈ E,
    |iteratedFDeriv ℝ 2 f u (fun _ => p i)| ≤ A * (b + s * h)
  residual_samples : ∀ u ∈ E, |eval ![u 0, u 1, u 2, f u] S / a| ≤ A
  third_samples : ∀ i : Fin 7, ∀ u ∈ E,
    |iteratedFDeriv ℝ 3
      (fun z => eval ![z 0, z 1, z 2, f z] S / a) u (fun _ => p i)| ≤ A * b / a

def SampledBranchData.region {Cloc J D : ℕ} (d : SampledBranchData Cloc J D) :
    Set (Base × ℝ) :=
  {z | z.1 ∈ Metric.closedBall 0 1 ∧ |z.2 - d.f z.1| ≤ d.A * d.b ∧
    d.A⁻¹ ≤ |eval ![z.1 0, z.1 1, z.1 2, z.2] (pderiv 3 d.S)| ∧
    |eval ![z.1 0, z.1 1, z.1 2, z.2] (pderiv 3 d.S)| ≤ d.A}

lemma SampledBranchData.A_le_loss {Cloc J D : ℕ} (d : SampledBranchData Cloc J D) :
    d.A ≤ d.A ^ (J + 1) := by
  exact (pow_one d.A).symm.trans_le
    (pow_le_pow_right₀ (by linarith [d.two_le_A]) (by omega : 1 ≤ J + 1))

/-- No restoration is used here: dense algebraic estimates supply its inputs. -/
def SampledBranchData.toLocal {Cloc J D : ℕ} (d : SampledBranchData Cloc J D)
    (hjet : DenseJetBound D J) : LocalBranchData Cloc where
  A := d.A ^ (J + 1)
  Z := d.Z
  a := d.a
  b := d.b
  h := d.h
  s := d.s
  S := d.S
  f := d.f
  p := d.p
  two_le_A := d.two_le_A.trans d.A_le_loss
  A_le_Z := d.loss_le_Z
  b_pos := d.b_pos
  b_le_a := d.b_le_a
  a_le_one := d.a_le_one
  h_pos := d.h_pos
  small_scale := d.small_scale
  s_nonneg := d.s_nonneg
  inv_b_le_Z := d.inv_b_le_Z
  S_degree := d.S_degree
  S_coeff := d.S_coeff
  S_curvature u w := (d.S_curvature u w).trans
    (div_le_div_of_nonneg_right d.A_le_loss (d.b_pos.trans_le d.b_le_a).le)
  smooth := d.smooth
  value_zero := d.value_zero
  first_zero := d.first_zero
  second_zero := d.second_zero
  affine_distance := d.affine_distance
  higher_bounds j hj2 hj6 u hu := by
    have hrel := (hjet d.A d.two_le_A d.f d.f_extension).2
    have hs := bound_by_affine_distance_scale d.f d.s (d.A ^ J)
      (‖iteratedFDeriv ℝ j d.f u‖) d.s_nonneg
      (pow_nonneg (by linarith [d.two_le_A]) _)
      d.affine_approximation (fun c L ε hε hc => hrel c L ε hε hc j hj2 hj6 u hu)
    apply hs.trans
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by linarith [d.two_le_A]) (by omega : J ≤ J + 1)) d.s_nonneg
  directions i := ⟨(d.directions i).1, (d.directions i).2.trans d.A_le_loss⟩
  transverse i j k hij hik hjk :=
    (inv_anti₀ (by linarith [d.two_le_A]) d.A_le_loss).trans
      (d.transverse i j k hij hik hjk)
  second_tests i j hj u hu := by
    have hb : 0 ≤ d.b + d.s * d.h :=
      add_nonneg d.b_pos.le (mul_nonneg d.s_nonneg d.h_pos.le)
    have hh := (hjet d.A d.two_le_A _ (d.second_extension i)).1
      d.E (d.A * (d.b + d.s * d.h)) d.measurable_E d.E_subset d.E_mass
      (mul_nonneg (by linarith [d.two_le_A]) hb) (d.second_samples i)
      j (by omega) u hu
    simpa only [pow_succ, mul_assoc] using hh
  residual_bounds j hj u hu := by
    have hh := (hjet d.A d.two_le_A _ d.residual_extension).1
      d.E d.A d.measurable_E d.E_subset d.E_mass (by linarith [d.two_le_A])
      d.residual_samples j hj u hu
    simpa only [pow_succ] using hh
  third_tests i j hj u hu := by
    have hh := (hjet d.A d.two_le_A _ (d.third_extension i)).1
      d.E (d.A * d.b / d.a) d.measurable_E d.E_subset d.E_mass
      (div_nonneg (mul_nonneg (by linarith [d.two_le_A]) d.b_pos.le)
        (d.b_pos.trans_le d.b_le_a).le) (d.third_samples i)
      j (by omega) u hu
    simpa only [pow_succ, mul_div_assoc, mul_assoc] using hh

theorem SampledBranchData.region_subset {Cloc J D : ℕ}
    (d : SampledBranchData Cloc J D) (hjet : DenseJetBound D J) :
    d.region ⊆ (d.toLocal hjet).region := by
  rintro z ⟨hball, hdist, hlo, hhi⟩
  refine ⟨hball, hdist.trans ?_, ?_, hhi.trans d.A_le_loss⟩
  · exact mul_le_mul_of_nonneg_right d.A_le_loss d.b_pos.le
  · exact (inv_anti₀ (by linarith [d.two_le_A]) d.A_le_loss).trans hlo

end

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration
