/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/RefinementWitness.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_linear_critical_extremizers.Interfaces
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ScalarEquiv
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementLaws

/-! Named witnesses for the literal refinement predicate, together with its
canonical invertible whole-trajectory coordinate maps. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

noncomputable section

structure RefinementData (p q : Code) where
  sample : ℕ → ℕ
  loss : ℕ → ℝ
  exponent : ℕ
  T : ℕ → ℕ
  world : (k : ℕ) → Fin (W q k) → Fin (W p (sample k))
  block : (k : ℕ) → Fin (W q k) → Fin (2 ^ T k)
  assignment : (k : ℕ) → Fin (W q k) → Set (ℕ × ScalarCoeff)
  selected : (k : ℕ) → Fin (W q k) → Set ((ℕ × ScalarCoeff) × ℝ)
  center : (k : ℕ) → Fin (W q k) → ℝ
  speed : (k : ℕ) → Fin (W q k) → ℝ
  width : (k : ℕ) → Fin (W q k) → ℝ
  polynomial : (k : ℕ) → Fin (W q k) → MvPolynomial (Fin 2) ℝ
  lists : (k : ℕ) → Fin (W p (sample k)) →
    ((Fin 2 → ℝ) × ℤ) → Finset (Fin (W q k))
  trajectory : (k : ℕ) → Fin (W q k) → (ℕ × ScalarCoeff) → (ℕ × ScalarCoeff)

namespace RefinementData

def duration {p q : Code} (w : RefinementData p q) (k : ℕ) : ℝ := ((2 : ℝ) ^ w.T k)⁻¹

def start {p q : Code} (w : RefinementData p q) (k : ℕ) (i : Fin (W q k)) : ℝ :=
  ((w.block k i : ℕ) : ℝ) * w.duration k

end RefinementData

/-- This structure only names the data and proofs already required by the
frozen refinement predicate. -/
structure RefinementWitness (p q : Code) (r b h : ℝ) extends RefinementData p q where
  sample_strictMono : StrictMono sample
  loss_pos : ∀ k, 0 < loss k
  loss_tendsto : Tendsto loss atTop (nhds 0)
  exponent_one : 1 ≤ exponent
  charts : ∀ k, N q k = N p (sample k) ∧
    ChartData p exponent r b (h + loss k) (loss k) false (sample k) (T k) (W q k)
      (world k) (block k) (assignment k) (selected k)
      (center k) (speed k) (width k) (polynomial k) (lists k)
  maps : ∀ k i, Measurable (trajectory k i) ∧
    (∀ l, (trajectory k i l).1 = l.1) ∧
    (∀ l t, y (trajectory k i l) ((t - toRefinementData.start k i) / toRefinementData.duration k) =
      (y l t - center k i - t * speed k i) / width k i) ∧
    (∀ l t, x (trajectory k i l) ((t - toRefinementData.start k i) / toRefinementData.duration k) =
      (x l t - MvPolynomial.eval ![t, y l t] (polynomial k i)) / N p (sample k) ^ (-r)) ∧
    ν q k i = (ν p (sample k) (world k i) (assignment k i))⁻¹ •
      Measure.map (trajectory k i) ((ν p (sample k) (world k i)).restrict (assignment k i)) ∧
    mu q k i = (ENNReal.ofReal (toRefinementData.duration k) *
        ν p (sample k) (world k i) (assignment k i))⁻¹ •
      Measure.map (fun z => (trajectory k i z.1,
        (z.2 - toRefinementData.start k i) / toRefinementData.duration k))
        ((mu p (sample k) (world k i)).restrict (selected k i))
  weights : ∀ k, (fun Z : ℝ => 0 < Z ∧ ∀ i,
    ω q k i = (ω p (sample k) (world k i) * toRefinementData.duration k *
      (ν p (sample k) (world k i) (assignment k i)).toReal) / Z)
    (∑ i : Fin (W q k), ω p (sample k) (world k i) * toRefinementData.duration k *
      (ν p (sample k) (world k i) (assignment k i)).toReal)

theorem refinement_iff_nonempty_witness {p q : Code} {r b h : ℝ} :
    Refinement p q r b h ↔ Nonempty (RefinementWitness p q r b h) := by
  constructor
  · rintro ⟨φ, ε, B, T, γ, j, A, C, u, v, J, P, Λ, θ,
      hφ, hε, hεt, hB, hchart, hmaps, hweights⟩
    exact ⟨⟨⟨φ, ε, B, T, γ, j, A, C, u, v, J, P, Λ, θ⟩,
      hφ, hε, hεt, hB, hchart, hmaps, hweights⟩⟩
  · rintro ⟨w⟩
    exact ⟨w.sample, w.loss, w.exponent, w.T, w.world, w.block, w.assignment,
      w.selected, w.center, w.speed, w.width, w.polynomial, w.lists, w.trajectory,
      w.sample_strictMono, w.loss_pos, w.loss_tendsto, w.exponent_one,
      w.charts, w.maps, w.weights⟩

namespace RefinementWitness

variable {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h)

theorem duration_pos (k : ℕ) : 0 < w.toRefinementData.duration k := by
  exact inv_pos.mpr (pow_pos (by norm_num) _)

theorem width_pos (k : ℕ) (i : Fin (W q k)) : 0 < w.width k i :=
  ((w.charts k).2.2.2.2.2.2.1 i).2.1

theorem polynomial_degree (k : ℕ) (i : Fin (W q k)) :
    (w.polynomial k i).totalDegree ≤ 2 :=
  ((w.charts k).2.2.2.2.2.2.1 i).2.2.2.2.2.1

/-- The original arbitrary coefficient map is the unique canonical invertible
scalar normalization, on every trajectory. -/
theorem trajectory_eq (hp : Exact p) (k : ℕ) (i : Fin (W q k)) :
    w.trajectory k i = scalarTrajectoryEquiv (w.polynomial k i)
      (w.polynomial_degree k i) (w.toRefinementData.start k i)
      (w.toRefinementData.duration k) (w.center k i) (w.speed k i) (w.width k i)
      (N p (w.sample k) ^ (-r)) (w.duration_pos k).ne' (w.width_pos k i).ne'
      (Real.rpow_pos_of_pos (by linarith [hp.1.1 (w.sample k)]) _).ne' := by
  apply eq_scalarTrajectoryEquiv_of_identities
  · exact (w.maps k i).2.1
  · exact (w.maps k i).2.2.1
  · exact (w.maps k i).2.2.2.1

def coefficientEquiv (hp : Exact p) (k : ℕ) (i : Fin (W q k)) :
    (ℕ × ScalarCoeff) ≃ᵐ (ℕ × ScalarCoeff) :=
  scalarTrajectoryEquiv (w.polynomial k i) (w.polynomial_degree k i)
    (w.toRefinementData.start k i) (w.toRefinementData.duration k)
    (w.center k i) (w.speed k i) (w.width k i) (N p (w.sample k) ^ (-r))
    (w.duration_pos k).ne' (w.width_pos k i).ne'
    (Real.rpow_pos_of_pos (by linarith [hp.1.1 (w.sample k)]) _).ne'

def incidenceEquiv (hp : Exact p) (k : ℕ) (i : Fin (W q k)) :
    ((ℕ × ScalarCoeff) × ℝ) ≃ᵐ ((ℕ × ScalarCoeff) × ℝ) :=
  (w.coefficientEquiv hp k i).prodCongr
    (scalarTimeEquiv (w.toRefinementData.start k i)
      (w.toRefinementData.duration k) (w.duration_pos k).ne')

theorem prior_eq (hp : Exact p) (k : ℕ) (i : Fin (W q k)) :
    ν q k i =
      Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior
        (ν p (w.sample k) (w.world k i)) (w.assignment k i) (w.coefficientEquiv hp k i) := by
  simpa only [Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior, coefficientEquiv,
    w.trajectory_eq hp k i] using (w.maps k i).2.2.2.2.1

theorem incidence_eq (hp : Exact p) (k : ℕ) (i : Fin (W q k)) :
    mu q k i = (ENNReal.ofReal (w.toRefinementData.duration k) *
        ν p (w.sample k) (w.world k i) (w.assignment k i))⁻¹ •
      Measure.map (w.incidenceEquiv hp k i)
        ((mu p (w.sample k) (w.world k i)).restrict (w.selected k i)) := by
  change mu q k i = _ • Measure.map
    (fun z : (ℕ × ScalarCoeff) × ℝ => ((w.coefficientEquiv hp k i) z.1,
      (z.2 - w.toRefinementData.start k i) / w.toRefinementData.duration k)) _
  simpa only [coefficientEquiv, w.trajectory_eq hp k i] using (w.maps k i).2.2.2.2.2

/-- Positivity comes from the selected incidence witness, while the
normalization mass remains that of the entire assignment. -/
theorem assignment_mass_pos (k : ℕ) (i : Fin (W q k)) :
    0 < ν p (w.sample k) (w.world k i) (w.assignment k i) := by
  have hC : 0 < mu p (w.sample k) (w.world k i) (w.selected k i) :=
    ((w.charts k).2.2.2.2.2.2.1 i).1
  have hsub : w.selected k i ⊆ w.assignment k i ×ˢ I (w.T k) (w.block k i) :=
    fun _ hz => (((w.charts k).2.2.2.2.2.1 i) hz).2
  have hmass : 0 <
      ((ν p (w.sample k) (w.world k i)).prod volume)
        (w.assignment k i ×ˢ I (w.T k) (w.block k i)) :=
    lt_of_lt_of_le hC
      ((Measure.restrict_apply_le _ _).trans (measure_mono hsub))
  rw [Measure.prod_prod] at hmass
  exact (ENNReal.mul_pos_iff.mp hmass).1

theorem assignment_mass_ne_top (hp : Exact p) (k : ℕ) (i : Fin (W q k)) :
    ν p (w.sample k) (w.world k i) (w.assignment k i) ≠ ∞ := by
  have : IsProbabilityMeasure (ν p (w.sample k) (w.world k i)) :=
    ((hp.2.1 (w.sample k)).2.2.2.1 (w.world k i)).1
  exact measure_ne_top _ _

/-- The child full assignment, pulled back through the actual refinement,
has exactly the product of the parent and conditional child prior masses. -/
theorem original_assignment_mass (hp : Exact p) (k : ℕ) (i : Fin (W q k))
    {B : Set (ℕ × ScalarCoeff)} (hB : MeasurableSet B) :
    ν p (w.sample k) (w.world k i)
        (w.assignment k i ∩ (w.coefficientEquiv hp k i) ⁻¹' B) =
      ν p (w.sample k) (w.world k i) (w.assignment k i) * ν q k i B := by
  rw [w.prior_eq hp k i]
  exact (RefinementLaws.assignment_mass_mul _ _ _ hB
    (w.assignment_mass_pos k i).ne' (w.assignment_mass_ne_top hp k i)).symm

/-- A second prior normalization is a normalization of the original full
assignment, not of the intervening selected incidence law. -/
theorem original_conditionedPrior (hp : Exact p) (k : ℕ) (i : Fin (W q k))
    {B : Set (ℕ × ScalarCoeff)} (hB : MeasurableSet B)
    (f : (ℕ × ScalarCoeff) ≃ᵐ (ℕ × ScalarCoeff)) :
    Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior (ν q k i) B f =
      Submission.Obl.k4_dyadic_crop_affine_laws.Framework.conditionedPrior
        (ν p (w.sample k) (w.world k i))
        (w.assignment k i ∩ (w.coefficientEquiv hp k i) ⁻¹' B)
        ((w.coefficientEquiv hp k i).trans f) := by
  rw [w.prior_eq hp k i]
  exact RefinementLaws.conditionedPrior_comp _ _ _ _ hB
    (w.assignment_mass_pos k i).ne' (w.assignment_mass_ne_top hp k i)

/-- Arbitrary later incidence masks compose in the original coordinates with
the product of actual durations and the unchanged original full-prior mass. -/
theorem original_normalized_incidence (hp : Exact p) (k : ℕ) (i : Fin (W q k))
    {B : Set (ℕ × ScalarCoeff)} (hB : MeasurableSet B)
    {C' : Set ((ℕ × ScalarCoeff) × ℝ)} (hC' : MeasurableSet C')
    (Ψ : ((ℕ × ScalarCoeff) × ℝ) ≃ᵐ ((ℕ × ScalarCoeff) × ℝ)) (q₂ : ℝ≥0∞) :
    (q₂ * ν q k i B)⁻¹ • (Measure.map Ψ ((mu q k i).restrict C')) =
      (ENNReal.ofReal (w.toRefinementData.duration k) * q₂ *
        ν p (w.sample k) (w.world k i)
          (w.assignment k i ∩ (w.coefficientEquiv hp k i) ⁻¹' B))⁻¹ •
        Measure.map ((w.incidenceEquiv hp k i).trans Ψ)
          ((mu p (w.sample k) (w.world k i)).restrict
            (w.selected k i ∩ (w.incidenceEquiv hp k i) ⁻¹' C')) := by
  rw [w.prior_eq hp k i, w.incidence_eq hp k i]
  exact RefinementLaws.normalized_incidence_comp _ _ _ _ hC' _ _ _ hB _ _
    (w.assignment_mass_pos k i).ne' (w.assignment_mass_ne_top hp k i)
    (ENNReal.ofReal_pos.mpr (w.duration_pos k)).ne' ENNReal.ofReal_ne_top

end RefinementWitness

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
