/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/ShiftedOutput.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.BaseCap
import Submission.Obl.k4_scalar_heavy_intercept_selection.PotentialBins

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Set MeasureTheory MvPolynomial

noncomputable section

/-- A positive selected intercept group gives one bounded polynomial
fitting every retained trajectory throughout its whole block. -/
theorem shifted_potential_whole_block {α : Type*} [MeasurableSpace α]
    (μ σ : Measure (α × ℝ)) (hσμ : σ ≤ μ) (hσ : σ univ ≠ 0)
    (P : MvPolynomial (Fin 2) ℝ) {D : ℕ} {H Hc w ε : ℝ}
    (hD : P.totalDegree ≤ D) (hH : 0 ≤ H) (hcoeff : ∀ m, |P.coeff m| ≤ H)
    (c : α → ℝ) (hbc : ∀ l, |c l| ≤ Hc) (hw : 0 < w) (g : ℤ)
    (hgroup : ∀ᵐ p ∂σ, (⌊c p.1 / w⌋ : ℤ) = g)
    (I : Set ℝ) (X : α → ℝ → ℝ) (u : α → ℝ → Fin 2 → ℝ)
    (hfit : ∀ᵐ p ∂μ, ∀ t ∈ I, |X p.1 t - eval (u p.1 t) P - c p.1| ≤ ε) :
    (P + C ((g : ℝ) * w)).totalDegree ≤ D ∧
      (∀ m, |(P + C ((g : ℝ) * w)).coeff m| ≤ H + Hc + w) ∧
      ∀ᵐ p ∂σ, ∀ t ∈ I,
        |X p.1 t - eval (u p.1 t) (P + C ((g : ℝ) * w))| ≤ ε + w := by
  have hmass : σ {p | (⌊c p.1 / w⌋ : ℤ) = g} = σ univ := by
    apply measure_congr
    filter_upwards [hgroup] with p hp
    simp only [mem_ofPred_eq, hp, mem_univ]
  have hnonzero : σ {p | (⌊c p.1 / w⌋ : ℤ) = g} ≠ 0 := by rwa [hmass]
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hnonzero
  have hcenter := intercept_bin_center_bound hw (hbc p.1) g hp
  refine ⟨shifted_potential_degree P hD _, ?_, ?_⟩
  · intro m
    exact (shifted_potential_coeff_bound (c := (g : ℝ) * w) P hH hcoeff m).trans (by linarith)
  · filter_upwards [hgroup, ae_mono hσμ hfit] with p hp hfitp
    intro t ht
    exact potential_fit_in_intercept_bin P (u p.1 t) hw g hp (hfitp t ht)

/-- The same selected group gains the exact hidden-width power in its
normalized base ceiling. Only original floor caps and the original prior
floor are used; all whole-block information is retained separately. -/
theorem shifted_potential_base_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) (hμρ : μ ≤ ρ) (b : Ω → Fin 2 → ℝ) (X c : Ω → ℝ)
    (z : Fin 2 → ℝ) (P : MvPolynomial (Fin 2) ℝ)
    {h ξ a w ε K d : ℝ} {prior : ENNReal}
    (hh : 0 < h) (hξ : 0 < ξ) (ha : 0 < a) (hw : 0 < w) (hK : 0 < K)
    (hε : ε ≤ w) (g : ℤ)
    (hcap : ∀ (q : Fin 2 → ℤ) (j : ℤ),
      ρ {p | (fun i => (⌊b p i / (h * ξ)⌋ : ℤ)) = q ∧ ⌊X p / w⌋ = j} ≤
        ENNReal.ofReal (K * (h * ξ) ^ 2 * w ^ d))
    (hprior : ENNReal.ofReal (a ^ d * h / K) ≤ prior)
    (S : Set Ω) (hS : ∀ᵐ p ∂μ, p ∈ S)
    (hgroup : ∀ᵐ p ∂μ, (⌊c p / w⌋ : ℤ) = g)
    (hfit : ∀ p ∈ S,
      |X p - eval (fun i => (b p i - z i) / h) P - c p| ≤ ε)
    (hosc : ∀ p ∈ S, ∀ p' ∈ S,
      (fun i => (⌊(b p i - z i) / h / ξ⌋ : ℤ)) =
        (fun i => (⌊(b p' i - z i) / h / ξ⌋ : ℤ)) →
      |eval (fun i => (b p i - z i) / h) P -
        eval (fun i => (b p' i - z i) / h) P| ≤ w)
    (q : Fin 2 → ℤ) :
    μ {p | (fun i => (⌊(b p i - z i) / h / ξ⌋ : ℤ)) = q} ≤
      ENNReal.ofReal (735 * K ^ 2 * h * ξ ^ 2 * (w / a) ^ d) * prior := by
  have ht := graph_cell_relative_cap μ ρ hμρ b X z hh hξ ha hw
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 1) hK
    (fun u => eval u (P + C ((g : ℝ) * w))) hcap hprior
    {p | p ∈ S ∧ (⌊c p / w⌋ : ℤ) = g} (hS.and hgroup) ?_ ?_ q
  · norm_num at ht ⊢
    exact ht
  · intro p hp
    exact (potential_fit_in_intercept_bin P _ hw g hp.2 (hfit p hp.1)).trans (by linarith)
  · intro p hp p' hp' hcode
    simpa only [eval_add, eval_C, add_sub_add_right_eq_sub, one_mul] using
      hosc p hp.1 p' hp'.1 hcode

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
