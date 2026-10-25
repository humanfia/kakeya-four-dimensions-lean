import Submission.Obl.k4_scalar_candidate_original_return.SourceMixture
import Submission.Obl.k4_scalar_candidate_original_return.ObservationFormat
import Submission.Obl.k4_scalar_candidate_original_return.ObservationBound
import Submission.Obl.k4_scalar_candidate_original_return.Flattening
import Submission.Lib.K4MeshListRecovery.MeshListRecovery

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ModelReduction

noncomputable section

/-- Exact original selected densities with a finite sign description. The
polynomial coefficients need no quantitative bound for mesh averaging. -/
structure SourceCertificate (ν : Measure Line) (C : Set Inc) (H R A : ℝ) (D : ℕ) where
  density : (Fin 6 → ℝ) → ℝ
  measurable : Measurable density
  nonneg : ∀ w, 0 ≤ density w
  bound : ∀ w, |density w| ≤ H
  support : supportedInCube density R
  atoms : ℕ
  atom_count : (atoms : ℝ) ≤ A
  polynomial : Fin atoms → MvPolynomial (Fin 6) ℝ
  degree : ∀ j, (polynomial j).totalDegree ≤ D
  controls : ∀ w w', (∀ j, SignType.sign (MvPolynomial.eval w (polynomial j)) =
    SignType.sign (MvPolynomial.eval w' (polynomial j))) → density w = density w'
  law : (((ν.prod volume).restrict C).map (fun q => observationShear (q.1.2, q.2))) =
    volume.withDensity (fun w => ENNReal.ofReal (density w))

/-- A source certificate retains its exact density and law when its four
quantitative bounds are enlarged. -/
def SourceCertificate.enlarge {ν : Measure Line} {C : Set Inc} {H R A H' R' A' : ℝ} {D D' : ℕ}
    (c : SourceCertificate ν C H R A D) (hH : H ≤ H') (hR : R ≤ R')
    (hA : A ≤ A') (hD : D ≤ D') : SourceCertificate ν C H' R' A' D' where
  density := c.density
  measurable := c.measurable
  nonneg := c.nonneg
  bound w := (c.bound w).trans hH
  support w i hi := c.support w i (hR.trans_lt hi)
  atoms := c.atoms
  atom_count := c.atom_count.trans hA
  polynomial := c.polynomial
  degree j := (c.degree j).trans hD
  controls := c.controls
  law := c.law

lemma SourceCertificate.integrable {ν : Measure Line} {C : Set Inc} {H R A : ℝ} {D : ℕ}
    (c : SourceCertificate ν C H R A D) : Integrable c.density volume :=
  Submission.Lib.K4MeshListRecovery.integrable_cube_density H R
    ⟨c.density, c.measurable, c.bound⟩ c.support

/-- Every finite formatted original prior and selected event gives a source
certificate with explicit density, support, atom count and degree bounds. -/
theorem source_certificate {m DB DC : ℕ} {HB HC H R : ℝ}
    (hHB : 1 ≤ HB) (hHC : 1 ≤ HC) (hR : 1 ≤ R)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ H) (copy : Fin m → ℕ)
    (B : Fin m → Set (Fin 5 → ℝ)) (hB : ∀ j, Format 5 HB DB (B j))
    (hBbound : ∀ j a, a ∈ B j → ∀ i, |a i| ≤ R)
    (ν : Measure Line)
    (hν : ν = ∑ j, ENNReal.ofReal (c j) •
      Measure.map (fun a : Fin 5 → ℝ => (copy j, a)) (volume.restrict (B j)))
    (C : Set Inc) (hC : MeasurableSet C)
    (hCtime : ∀ q ∈ C, q.2 ∈ Icc (0 : ℝ) 1)
    (hCformat : ∀ z, Format 6 HC DC
      {w | ((z, fun e : Fin 5 => w e.castSucc), w 5) ∈ C}) :
    Nonempty (SourceCertificate ν C ((m : ℝ) * H) (3 * R)
      ((m : ℝ) * (HB + HC)) (max (DB * 3) (DC * 3))) := by
  classical
  let S : Fin m → Set (Fin 6 → ℝ) := fun j =>
    {w | (observationShear.symm w).1 ∈ B j ∧
      ((copy j, (observationShear.symm w).1), (observationShear.symm w).2) ∈ C}
  have hSformat (j : Fin m) : Format 6 (HB + HC) (max (DB * 3) (DC * 3)) (S j) :=
    k4_scalar_true_atlas_terminal_lists.Format.inter
      (observation_prior_format hHB (hB j))
      (observation_incidence_format hHC hCformat (copy j)) hHB hHC
  have hSmeas (j : Fin m) : MeasurableSet (S j) :=
    k4_scalar_true_atlas_terminal_lists.Format.measurable (hSformat j)
  obtain ⟨n, hn, p, hp, hcontrol⟩ := piecewise_density_sign_family S hSformat c
  refine ⟨{
    density := mixtureDensity c S
    measurable := mixtureDensity_measurable c S hSmeas
    nonneg := mixtureDensity_nonneg c (fun j => (hc j).1) S
    bound := mixtureDensity_bound c hc S
    support := ?_
    atoms := n
    atom_count := hn
    polynomial := p
    degree := hp
    controls := hcontrol
    law := ?_ }⟩
  · intro w i hi
    have hnot (j : Fin m) : w ∉ S j := by
      intro hw
      have hbound := observationShear_bound hR (observationShear.symm w).1
        (hBbound j _ hw.1) (hCtime _ hw.2)
      change ∀ i, |observationShear (observationShear.symm w) i| ≤ 3 * R at hbound
      rw [MeasurableEquiv.apply_symm_apply] at hbound
      exact not_lt_of_ge (hbound i) hi
    apply Finset.sum_eq_zero
    intro j _
    simp [hnot j]
  · exact mixture_law_in_coordinates observationShear measurePreserving_observationShear
      c (fun j => (hc j).1) copy B
      (fun j => k4_scalar_true_atlas_terminal_lists.Format.measurable (hB j)) ν hν C hC

/-- Averaging only the two exact observed coordinates retains the original
hidden coordinate and has error linear in the mesh width. -/
theorem SourceCertificate.flatten {ν : Measure Line} {C : Set Inc} {H R A : ℝ} {D : ℕ}
    (c : SourceCertificate ν C H R A D) (hR : 0 ≤ R) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ g : boundedMeasurableFunctions (Fin 6 → ℝ) H,
      (∀ w, 0 ≤ g.val w) ∧
      (∫⁻ w, ENNReal.ofReal (g.val w)) = (∫⁻ w, ENNReal.ofReal (c.density w)) ∧
      (∀ w w', (∀ i ∉ ([0, 1] : List (Fin 6)), w i = w' i) →
        (∀ i ∈ ([0, 1] : List (Fin 6)), ⌊w i / ρ⌋ = ⌊w' i / ρ⌋) → g.val w = g.val w') ∧
      supportedInCube g.val (R + 2 * ρ) ∧
      densityL1Distance volume g.val c.density ≤
        ENNReal.ofReal (16 * H * A * (D : ℝ) * ρ * (2 * R) ^ 5) := by
  have hH : 0 ≤ H := (abs_nonneg (c.density 0)).trans (c.bound 0)
  obtain ⟨g, hg0, hgmass, hgcell, hgsupport, hgerror⟩ :=
    flatten_sign_controlled H R D hH hR ⟨c.density, c.measurable, c.bound⟩
      c.nonneg c.support c.polynomial c.degree c.controls [0, 1] hρ
  refine ⟨g, hg0, hgmass, hgcell, ?_, ?_⟩
  · simpa using hgsupport
  · have heq : (([0, 1] : List (Fin 6)).length : ℝ) *
        (4 * H * ((2 * c.atoms * D : ℕ) : ℝ) * ρ) * (2 * R) ^ 5 =
        16 * H * (c.atoms : ℝ) * (D : ℝ) * ρ * (2 * R) ^ 5 := by
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.cast_mul,
        Nat.cast_ofNat]
      ring
    rw [heq] at hgerror
    apply hgerror.trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    exact c.atom_count

end

end Submission.Obl.k4_scalar_candidate_original_return
