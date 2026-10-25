-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/OriginalPolynomialRow.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/OriginalPolynomialRow.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, obligation o106 (k4_isotropic_path_improvement), session x0358
-- (commit 7085a9da), as merged on branch x0352 at commit 1e57792e, file Submission/Obl/k4_isotropic_path_improvement/OriginalPolynomialRow.lean;
-- only the namespace and module paths were renamed into o285's Cart namespace.
-- Existing source attributions of that file are preserved below.

import Submission.Obl.k4_physical_row_packet_potential.Cartesian.OriginalFiberSelection
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.GridInterpolation

/-!
# One actual polynomial row from original fitting witnesses

Paper `tex-06-isotropic.tex`, Section 6, "Cartesian interpolation of the physical field", from
the original source: a row field `G : X → Fin q → ℝ` with, along each of the three axes, actual
degree-`D` polynomial fits `P axis x` witnessed on ordinary time sets of duration `≥ 1/K`
(with at most `K` field / fiber-time list options), actual coordinates `u` within `ξ` of a
`ξ`-separated real grid `S`.  On an ORIGINAL subfamily `T'` of explicit mass one actual
polynomial row `Q : Fin q → MvPolynomial (Fin 3) ℝ` of degree `≤ 3 D` fits `G` up to
`p + 3 (1 + (D + 1) (2 K / r)^D)^3 E`, where
`E = p + ε + (D + 1) p (3 K)^D + 3 (D + 1) D (K + p) (3 K)^D ξ`.

Combines x0352's `original_common_fiber_selection` (common field and fiber codes with a
fixed-power original mass cost) and `selected_common_fiber_fits` (the common tables fit every
positive original cell) with `original_grid_polynomial_field_row` (`GridInterpolation.lean`),
applied to the restriction of `μ` to the selected set; masses return to the original `μ`
exactly.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set MvPolynomial Submission.Lib.K4CommonLocalChoice

noncomputable section

/-- **One actual polynomial row from original fitting witnesses.** -/
theorem original_polynomial_row (D q : ℕ) :
    ∃ Bsel : ℝ, 0 < Bsel ∧ ∃ C : ℝ, 0 < C ∧
    ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
      (S : Finset ℝ) [Nonempty S] (code : X → S × S × S), Measurable code →
      ∀ (G : X → Fin q → ℝ), Measurable G →
      ∀ (P : Fin 3 → X → Fin q → Polynomial ℝ),
      (∀ axis, Measurable (fun x => polynomialFitCoefficients D (P axis x))) →
      ∀ (Ω : Set X), MeasurableSet Ω →
      ∀ (p K ξ ε a U δ r : ℝ), 0 < p → 1 ≤ K → 0 < ξ → 0 ≤ ε → 0 < a → 0 < U → 0 ≤ δ →
      0 < r →
      (∀ axis x, x ∈ Ω → ∀ j, (P axis x j).natDegree ≤ D) →
      ∀ E : Fin 3 → X → Set ℝ,
      (∀ axis x, x ∈ Ω → MeasurableSet (E axis x)) →
      (∀ axis x, x ∈ Ω → E axis x ⊆ Icc (0 : ℝ) 1) →
      (∀ axis x, x ∈ Ω → ENNReal.ofReal (1 / K) ≤ volume (E axis x)) →
      ∀ H : Fin 3 → X → ℝ → Fin q → ℝ,
      (∀ axis x, x ∈ Ω → ∀ t ∈ E axis x, ∀ j, |(P axis x j).eval t - H axis x t j| ≤ p) →
      (∀ g, ∃ F : Finset (Fin q → ℤ), (F.card : ℝ) ≤ K ∧
        ∀ x ∈ Ω, code x = g → cell p (G x) ∈ F) →
      (∀ axis key t, ∃ F : Finset (Fin q → ℤ), (F.card : ℝ) ≤ K ∧
        ∀ x ∈ Ω, gridFiberKey axis (code x) = key → t ∈ E axis x →
          cell p (H axis x t) ∈ F) →
      ∀ (u : X → Fin 3 → ℝ),
      (∀ s ∈ S, |s| ≤ K) →
      (∀ x ∈ Ω, ∀ i, |u x i| ≤ K) →
      (∀ x ∈ Ω, ∀ i, |u x i - gridPoint (code x) i| ≤ ξ) →
      (∀ x ∈ Ω, ∀ j, |G x j| ≤ K) →
      (∀ axis x, x ∈ Ω → ∀ j k, |(P axis x j).coeff k| ≤ K) →
      (∀ axis x, x ∈ Ω → ∀ j, |G x j - (P axis x j).eval (∑ i, u x i)| ≤ ε) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ξ ≤ dist x y) →
      (∀ i : S × S × S, μ.real {x | code x = i} ≤ U) →
      δ * U * (S.card : ℝ) ^ 3 + (S.card : ℝ) ^ 3 * a ≤
        μ.real Ω / (Bsel * K ^ (1 + 3 * (3 + 3 * D * (q * (D + 1))))) →
      3 * ((D + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ)) < δ ^ ((D + 2) ^ 3) →
      ∃ (Q : Fin q → MvPolynomial (Fin 3) ℝ) (T' : Set X),
        MeasurableSet T' ∧ T' ⊆ Ω ∧
        (∀ j, (Q j).totalDegree ≤ 3 * D) ∧
        (∀ j d, |(Q j).coeff d| ≤
          C * (((D : ℝ) + 1) ^ 3 * (K + p) * ((1 + K) / r) ^ (3 * D))) ∧
        (δ ^ ((D + 2) ^ 3) - 3 * ((D + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ))) / 2 *
          a * (S.card : ℝ) ^ 3 ≤ μ.real T' ∧
        ∀ x ∈ T', ∀ j, |G x j - eval (gridPoint (code x)) (Q j)| ≤
          p + 3 * (1 + ((D : ℝ) + 1) * ((2 * K) / r) ^ D) ^ 3 *
            (p + ε + ((D : ℝ) + 1) * p * (3 * K) ^ D +
              3 * ((D : ℝ) + 1) * D * (K + p) * (3 * K) ^ D * ξ) := by
  obtain ⟨Bsel, hBsel, hsel⟩ := original_common_fiber_selection D q
  obtain ⟨C, hC, hrow⟩ := original_grid_polynomial_field_row D q
  refine ⟨Bsel, hBsel, C, hC, ?_⟩
  intro X _ μ _ S _ code hcode G hG P hPm Ω hΩ p K ξ ε a U δ r hp hK hξ hε ha hU hδ hr
    hdeg E hEm hEsub hEvol H hHfit hfield hlocal u hS hu hdist hGb hcoeff hfitG hsep hcap
    hbudget hgap
  obtain ⟨value, fiber, T, hT, hTΩ, hmem, hmass⟩ :=
    hsel μ code hcode G hG P hPm Ω hΩ p K hp hK hdeg E hEm hEsub hEvol H hHfit hfield hlocal
  have hvalue : ∀ x ∈ T, cell p (G x) = value (code x) := fun x hx => ((hmem x).mp hx).2.1
  have hfiber : ∀ axis x, x ∈ T → polynomialFitCoefficientCode D p (P axis x) =
      fiber axis (gridFiberKey axis (code x)) := fun axis x hx => ((hmem x).mp hx).2.2 axis
  set Err := p + ε + ((D : ℝ) + 1) * p * (3 * K) ^ D +
    3 * ((D : ℝ) + 1) * D * (K + p) * (3 * K) ^ D * ξ with hErr
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hErr0 : 0 ≤ Err := by positivity
  -- the common tables fit every positive original cell of the selected set
  have hfits := selected_common_fiber_fits μ T code (fun s : S => (s : ℝ)) u G P D p K ξ ε hp hK
    hξ.le (fun s => hS _ s.2) (fun x hx => hu x (hTΩ hx))
    (fun x hx => hdist x (hTΩ hx)) (fun x hx => hGb x (hTΩ hx))
    (fun axis x hx => hdeg axis x (hTΩ hx)) (fun axis x hx => hcoeff axis x (hTΩ hx))
    (fun axis x hx => hfitG axis x (hTΩ hx)) value fiber hvalue hfiber
  -- heavy cells of the restricted measure are positive original cells
  have hpos : ∀ g, a ≤ (μ.restrict T).real {x | code x = g} →
      0 < μ.real (T ∩ code ⁻¹' {g}) := by
    intro g hg
    have hmeas : MeasurableSet {x | code x = g} := hcode (measurableSet_singleton g)
    rw [measureReal_restrict_apply hmeas] at hg
    have : {x | code x = g} ∩ T = T ∩ code ⁻¹' {g} := by
      ext x; simp [and_comm]
    rw [this] at hg
    linarith
  -- the row theorem on the restricted measure
  obtain ⟨Q, G', hdegQ, hcoefQ, hmeasG', hmassG', herr⟩ :=
    hrow (μ.restrict T) S code hcode a U δ ξ r K (K + p) Err ha hU hδ hξ hr (by positivity) hErr0
      hS hsep
      (fun i => by
        have hmeas : MeasurableSet {x | code x = i} := hcode (measurableSet_singleton i)
        rw [measureReal_restrict_apply hmeas]
        exact (measureReal_mono Set.inter_subset_left).trans (hcap i))
      (by
        rw [measureReal_restrict_apply_univ]
        have hden : 0 < Bsel * K ^ (1 + 3 * (3 + 3 * D * (q * (D + 1)))) := by positivity
        refine hbudget.trans ?_
        rw [div_le_iff₀ hden]
        linarith [hmass])
      hgap (commonGridValue p value)
      (fun g e hg => (hfits g (hpos g hg)).1 e)
      (fun e => fun y z => commonFiberPolynomial (fun s : S => (s : ℝ)) D p fiber 0 (y, z) e)
      (fun e => fun x z => commonFiberPolynomial (fun s : S => (s : ℝ)) D p fiber 1 (x, z) e)
      (fun e => fun x y => commonFiberPolynomial (fun s : S => (s : ℝ)) D p fiber 2 (x, y) e)
      (fun e y z => degree_commonFiberPolynomial _ D p fiber 0 _ e)
      (fun e x z => degree_commonFiberPolynomial _ D p fiber 1 _ e)
      (fun e x y => degree_commonFiberPolynomial _ D p fiber 2 _ e)
      (fun g e hg => (hfits g (hpos g hg)).2 0 e)
      (fun g e hg => (hfits g (hpos g hg)).2 1 e)
      (fun g e hg => (hfits g (hpos g hg)).2 2 e)
  refine ⟨Q, T ∩ {x | code x ∈ G'}, hT.inter hmeasG',
    fun x hx => hTΩ hx.1, hdegQ, hcoefQ, ?_, ?_⟩
  · -- the mass returns to the original measure exactly
    rw [measureReal_restrict_apply hmeasG'] at hmassG'
    simpa [Set.inter_comm] using hmassG'
  · intro x hx j
    have hround : |G x j - commonGridValue p value (code x) j| ≤ p := by
      have hc := congrFun (hvalue x hx.1) j
      have he := coefficient_floor_error p (G x j) hp
      change ⌊G x j / p⌋ = value (code x) j at hc
      simpa [commonGridValue, ← hc] using he
    have h2 := herr x hx.2 j
    calc |G x j - eval (gridPoint (code x)) (Q j)|
        ≤ |G x j - commonGridValue p value (code x) j| +
          |commonGridValue p value (code x) j - eval (gridPoint (code x)) (Q j)| :=
          abs_sub_le _ _ _
      _ ≤ p + 3 * (1 + ((D : ℝ) + 1) * ((2 * K) / r) ^ D) ^ 3 * Err := add_le_add hround h2

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
