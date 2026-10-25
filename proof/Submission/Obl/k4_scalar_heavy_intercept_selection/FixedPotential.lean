/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/FixedPotential.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.BoundedBase
import Submission.Obl.k4_scalar_heavy_intercept_selection.HeavyPacket
import Submission.Obl.k4_scalar_heavy_intercept_selection.PolynomialVariation
import Submission.Obl.k4_scalar_heavy_intercept_selection.ShiftedOutput

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ContinuousKakeya

noncomputable section

def potentialVariationBound (D : ℕ) (H : ℝ) : ℝ :=
  ((2 : ℝ) * (D + 1 : ℕ) * (2 : ℝ) ^ D * (D : ℝ)) * H ^ (D + 1)

/-- Finite-packet completion of the heavy potential argument. All mass,
cell, and palette data refer to the original incidence law and its
unchanged trajectory prior. The common potential is translated by one
actual trajectory-intercept bin. -/
theorem heavy_polynomial_packet {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν]
    (μ : Measure (α × ℝ)) [IsFiniteMeasure μ] (ρ : Measure (α × ℝ))
    (K : NNReal) (hK : 1 ≤ K) {C h b ξ η w ε R a d : ℝ}
    (hC : 0 < C) (hMK : FiniteMK 2 C) (hh : 0 < h) (hb : 0 < b)
    (hξ : 0 < ξ) (hξ₁ : ξ ≤ 1) (hη : 0 < η) (hw : 0 < w) (ha : 0 < a)
    (hR : 0 < R) (hbξ : b ≤ h * ξ) (hε : ε ≤ w)
    (hν : 0 < (ν univ).toReal) (hμρ : μ ≤ ρ)
    (hdom : μ ≤ K • ν.prod volume)
    (hmass : h * (ν univ).toReal / (K : ℝ) ≤ (μ univ).toReal)
    (u v : α → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hbu : ∀ l, |u l| ≤ (K : ℝ)) (hbv : ∀ l, |v l| ≤ (K : ℝ))
    (Λ : Set α) (hΛ : MeasurableSet Λ) (hΛμ : ∀ᵐ p ∂μ, p.1 ∈ Λ)
    (z : Fin 2 → ℝ) (phys : α × ℝ → Fin 3 → ℝ) (hphys : Measurable phys)
    (hTime : ∀ p, phys p 0 = p.2)
    (hBase : ∀ p, p.1 ∈ Λ → normalizedPhysicalBase h z phys p =
      ![(p.2 - z 0) / h, u p.1 + ((p.2 - z 0) / h) * v p.1])
    (P : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hD : P.totalDegree ≤ D) (hcoeff : ∀ m, |P.coeff m| ≤ (K : ℝ))
    (c : α → ℝ) (hc : Measurable c) (hbc : ∀ l, |c l| ≤ (K : ℝ))
    (I : Set ℝ) (X : α → ℝ → ℝ) (U : α → ℝ → Fin 2 → ℝ)
    (hphysX : ∀ p, phys p 2 = X p.1 p.2)
    (hphysU : ∀ p, normalizedPhysicalBase h z phys p = U p.1 p.2)
    (htime : ∀ᵐ p ∂μ, p.2 ∈ I)
    (hbox : ∀ᵐ p ∂μ, ∀ t ∈ I, ∀ i, |U p.1 t i| ≤ (K : ℝ))
    (hfit : ∀ᵐ p ∂μ, ∀ t ∈ I, |X p.1 t - eval (U p.1 t) P - c p.1| ≤ ε)
    (hFineError : b + potentialVariationBound D (K : ℝ) * (b / h) + 2 * ε ≤ w)
    (hCoarse : potentialVariationBound D (K : ℝ) * ξ ≤ w)
    (hPencil : ∀ q w₀,
      μ {p | finePhysicalCode b phys p = q ∧ |v p.1 - w₀| < η} ≤
        ENNReal.ofReal (1 / 2000 : ℝ) * μ ((finePhysicalCode b phys) ⁻¹' {q}))
    (J : Finset ((Fin 2 → ℤ) × ℤ))
    (hJ : ∀ᵐ p ∂μ, jointPhysicalCode h ξ w z phys p ∈ J)
    (hJcard : (J.card : ℝ) ≤ (K : ℝ) / ξ ^ 2 * R)
    (hcap : ∀ (q : Fin 2 → ℤ) (j : ℤ),
      ρ {p | (fun i => (⌊phys p i.castSucc / (h * ξ)⌋ : ℤ)) = q ∧ ⌊phys p 2 / w⌋ = j} ≤
        ENNReal.ofReal ((K : ℝ) * (h * ξ) ^ 2 * w ^ d))
    (hprior : ENNReal.ofReal (a ^ d * h / (K : ℝ)) ≤ ν univ) :
    ∃ (lists : (Fin 3 → ℤ) → Finset ℤ) (g : ℤ),
      let σ := retainedGroup μ (finePhysicalCode b phys)
        (fun p => (⌊c p.1 / w⌋ : ℤ)) lists (ENNReal.ofReal (1 / 1000 : ℝ)) g
      let P' := P + MvPolynomial.C ((g : ℝ) * w)
      (∀ q, ((lists q).card : ENNReal) ≤ 7) ∧
      (∀ q g', g' ∉ lists q → μ {p | finePhysicalCode b phys p = q ∧
        (⌊c p.1 / w⌋ : ℤ) = g'} = 0) ∧
      σ ≤ μ ∧
      ENNReal.ofReal (h * (ν univ).toReal * (η / ((K : ℝ) + 1) ^ 2) /
        (13478400 * C * (K : ℝ) ^ 6 * R)) ≤ σ univ ∧
      P'.totalDegree ≤ D ∧ (∀ m, |P'.coeff m| ≤ 2 * (K : ℝ) + w) ∧
      (∀ᵐ p ∂σ, ∀ t ∈ I, |X p.1 t - eval (U p.1 t) P'| ≤ 2 * w) ∧
      ∀ q : Fin 2 → ℤ,
        σ {p | (fun i => (⌊normalizedPhysicalBase h z phys p i / ξ⌋ : ℤ)) = q} ≤
          ENNReal.ofReal (735 * (K : ℝ) ^ 2 * h * ξ ^ 2 * (w / a) ^ d) * ν univ := by
  classical
  let base := normalizedPhysicalBase h z phys
  let M := potentialVariationBound D (K : ℝ)
  let S : Set (α × ℝ) := {p | (∀ i, |base p i| ≤ (K : ℝ)) ∧
    |phys p 2 - eval (base p) P - c p.1| ≤ ε}
  have hK₁ : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK₀ : (0 : ℝ) < K := by linarith
  have hS : ∀ᵐ p ∂μ, p ∈ S := by
    filter_upwards [htime, hbox, hfit] with p ht hb hf
    refine ⟨?_, ?_⟩
    · simpa only [base, hphysU] using hb p.2 ht
    · simpa only [base, hphysU, hphysX] using hf p.2 ht
  have hOsc (p : α × ℝ) (hp : p ∈ S) (p' : α × ℝ) (hp' : p' ∈ S)
      {δ : ℝ} (hδ : 0 ≤ δ) (hd : ∀ i, |base p i - base p' i| ≤ δ) :
      |eval (base p) P - eval (base p') P| ≤ M * δ := by
    exact polynomial_eval_oscillation_power_bound P D hD hK₁ hδ hcoeff
      (base p') (base p) hp'.1 hp.1 hd
  have hFine : ∀ p ∈ S, ∀ p' ∈ S, finePhysicalCode b phys p = finePhysicalCode b phys p' →
      |eval (base p) P - eval (base p') P| ≤ M * (b / h) := by
    intro p hp p' hp' heq
    apply hOsc p hp p' hp' (by positivity)
    intro i
    exact normalized_base_close_of_fine_code hb hh z (phys p') (phys p) heq.symm i
  have hCoarse' : ∀ p ∈ S, ∀ p' ∈ S,
      (fun i => (⌊base p i / ξ⌋ : ℤ)) = (fun i => (⌊base p' i / ξ⌋ : ℤ)) →
      |eval (base p) P - eval (base p') P| ≤ w := by
    intro p hp p' hp' heq
    apply (hOsc p hp p' hp' hξ.le ?_).trans hCoarse
    intro i
    have ht := (Int.abs_sub_lt_one_of_floor_eq_floor (congrFun heq i)).le
    rw [← sub_div, abs_div, abs_of_pos hξ] at ht
    simpa only [one_mul] using (div_le_iff₀ hξ).mp ht
  obtain ⟨lists, hlist, hsupport, g, hσμ, hheavy, hgroup⟩ := select_heavy_packet ν μ K hK
    hC hMK hh hb hξ hξ₁ hη hw hR hbξ hε hFineError hν hdom hmass
    u v hu hv hbu hbv Λ hΛ hΛμ z phys hphys hTime hBase c hc hbc (fun u => eval u P)
    S hS (fun p hp => hp.1) (fun p hp => hp.2) hFine hCoarse' hPencil J hJ hJcard
  let σ := retainedGroup μ (finePhysicalCode b phys) (fun p => (⌊c p.1 / w⌋ : ℤ)) lists
    (ENNReal.ofReal (1 / 1000 : ℝ)) g
  have hσ : σ univ ≠ 0 := ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hheavy)
  have hshift := shifted_potential_whole_block μ σ hσμ hσ P hD hK₀.le hcoeff c hbc hw g
    hgroup I X U hfit
  refine ⟨lists, g, hlist, hsupport, hσμ, hheavy, hshift.1, ?_, ?_, ?_⟩
  · intro m
    simpa only [two_mul] using hshift.2.1 m
  · filter_upwards [hshift.2.2] with p hp
    intro t ht
    exact (hp t ht).trans (by linarith)
  · intro q
    exact shifted_potential_base_cap σ ρ (hσμ.trans hμρ) (fun p i => phys p i.castSucc)
      (fun p => phys p 2) (fun p => c p.1) z P hh hξ ha hw hK₀ hε g
      hcap hprior S (ae_mono hσμ hS) hgroup (fun p hp => hp.2) hCoarse' q

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
