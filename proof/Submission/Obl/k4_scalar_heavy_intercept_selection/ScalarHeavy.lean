/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/ScalarHeavy.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.FixedPotential
import Submission.Obl.k4_scalar_heavy_intercept_selection.PencilBudget
import Submission.Obl.k4_scalar_heavy_intercept_selection.ScalarFrame
import Submission.Obl.k4_scalar_heavy_intercept_selection.Scales
import Submission.Obl.k4_scalar_heavy_intercept_selection.Cons.Contract

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4ContinuousKakeya

noncomputable section

/-- The finite scalar field/potential certificate is enough for the
complete heavy potential selection once its numerical scale margins and
the original rectangular cap at the physical mesh have been prepared. -/
theorem scalar_heavy_packet
    {Nk Hf Hp d κ S Z B Rf cstar C r₀ : ℝ} (hN : 1 < Nk) (hHf : 1 ≤ Hf)
    (K : NNReal) (hK : 1 ≤ K) (hFH : Hf ≤ (K : ℝ)) (hPH : Hp ≤ (K : ℝ))
    (hC : 0 < C) (hMK : FiniteMK 2 C) (D Dp Tk : ℕ) (jj : Fin (2 ^ Tk))
    (ν : Measure (ℕ × (Fin 5 → ℝ))) (π : Measure ℝ)
    (ρ μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (A : Set (ℕ × (Fin 5 → ℝ))) (z : Fin 2 → ℝ)
    (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (c : (ℕ × (Fin 5 → ℝ)) → ℝ)
    (hField : Cons.FieldAt Nk Hf d κ S Z B Rf D ν π ρ A Tk jj μ z 𝒯)
    (hPot : Cons.PotAt Nk Hp cstar Dp Tk jj μ z P c)
    (hr₀ : Rf⁻¹ ≤ r₀) (hr₁ : r₀ ≤ Rf)
    (hsmall : 14000 * (K : ℝ) ^ 2 * Nk ^ (-S * r₀) ≤ 1) :
    let h := ((2 : ℝ) ^ Tk)⁻¹
    let ξ := Nk ^ (-Z)
    let b := Nk ^ (-B)
    let a := Nk ^ (-1 : ℝ)
    let w := Nk ^ (-1 - cstar)
    let ε := (K : ℝ) * Nk ^ (-1 - 2 * cstar)
    let η := Nk ^ (-r₀)
    let I := Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk)
      ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk)
    b ≤ h * ξ → ξ ≤ 1 → ε ≤ w →
    b + potentialVariationBound Dp (K : ℝ) * (b / h) + 2 * ε ≤ w →
    potentialVariationBound Dp (K : ℝ) * ξ ≤ w →
    a * h ^ ((1 : ℝ) / 8) ≤ w → w ≤ a →
    (∀ (q : Fin 2 → ℤ) (j : ℤ),
      ρ {p | (fun i => (⌊(![p.2, Cons.yL p.1 p.2] : Fin 2 → ℝ) i / (h * ξ)⌋ : ℤ)) = q ∧
        (⌊Cons.xL p.1 p.2 / w⌋ : ℤ) = j} ≤
          ENNReal.ofReal ((K : ℝ) * (h * ξ) ^ 2 * w ^ d)) →
    ∃ (σ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (P' : MvPolynomial (Fin 2) ℝ),
      σ ≤ μ ∧
      ENNReal.ofReal (h * (ν A).toReal * (η / ((K : ℝ) + 1) ^ 2) /
        (13478400 * C * (K : ℝ) ^ 6 * (a / w) ^ d)) ≤ σ univ ∧
      P'.totalDegree ≤ Dp ∧ (∀ m, |P'.coeff m| ≤ 2 * (K : ℝ) + w) ∧
      (∀ᵐ p ∂σ, ∀ t ∈ I, |Cons.xL p.1 t - eval (Cons.ubase z h p.1 t) P'| ≤ 2 * w) ∧
      (∀ q : Fin 2 → ℤ,
        σ {p | (fun i => (⌊Cons.ubase z h p.1 p.2 i / ξ⌋ : ℤ)) = q} ≤
          ENNReal.ofReal (735 * (K : ℝ) ^ 2 * h * ξ ^ 2 * (w / a) ^ d) * ν A) ∧
      ∀ r, Rf⁻¹ ≤ r → r ≤ Rf → ∀ (q : Fin 3 → ℤ) (j : ℤ),
        σ {p | Cons.physState b p = q ∧ (⌊p.1.2 1 / (Nk ^ (-r))⌋ : ℤ) = j} ≤
          ENNReal.ofReal (1000 * (K : ℝ)) * σ {p | Cons.physState b p = q} *
            π {v | (⌊v / (Nk ^ (-r))⌋ : ℤ) = j} := by
  dsimp only
  intro hbξ hξ₁ hε hFineError hCoarse hjointlo hjointhi hcap
  let h := ((2 : ℝ) ^ Tk)⁻¹
  let ξ := Nk ^ (-Z)
  let b := Nk ^ (-B)
  let a := Nk ^ (-1 : ℝ)
  let w := Nk ^ (-1 - cstar)
  let ε := (K : ℝ) * Nk ^ (-1 - 2 * cstar)
  let η := Nk ^ (-r₀)
  let I := Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk)
    ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk)
  rcases hField with ⟨hA, hνprob, hπprob, hcoeff, hlo, hup, hh, hh₁, hpriorlo, hpriorhi,
    hμρ, hdom, hsupport, hmass, hz₀, hz, hbox, hbase, hpalette, h𝒯coeff, h𝒯fit, hjoint⟩
  rcases hPot with ⟨hD, hPcoeff, hc, hbc, hfit⟩
  letI := hνprob
  letI := hπprob
  have hN₀ : 0 < Nk := by linarith
  have hHf₀ : 0 < Hf := by linarith
  have hK₁ : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hK₀ : (0 : ℝ) < K := by linarith
  have hb : 0 < b := Real.rpow_pos_of_pos hN₀ _
  have hξ : 0 < ξ := Real.rpow_pos_of_pos hN₀ _
  have ha : 0 < a := Real.rpow_pos_of_pos hN₀ _
  have hw : 0 < w := Real.rpow_pos_of_pos hN₀ _
  have hη : 0 < η := Real.rpow_pos_of_pos hN₀ _
  have hR : 0 < (a / w) ^ d := Real.rpow_pos_of_pos (div_pos ha hw) _
  have hsupp : ∀ᵐ p ∂μ, p.1 ∈ A ∧ p.2 ∈ I := ae_iff.mpr hsupport
  letI : IsFiniteMeasure μ := finite_incidence_of_time_support ν μ (ENNReal.ofReal Hf)
    ENNReal.ofReal_ne_top _ _ hdom (hsupp.mono (fun p hp => hp.2))
  let θ := ν.restrict A
  have hθ : θ univ = ν A := Measure.restrict_apply_univ A
  have hprior₀ : ν A ≠ 0 := ne_of_gt
    ((ENNReal.ofReal_pos.mpr (by positivity : 0 < Nk ^ (-d) * h / Hf)).trans_le hpriorlo)
  have hθ₀ : 0 < (θ univ).toReal := by
    rw [hθ]
    exact ENNReal.toReal_pos hprior₀ (measure_ne_top ν A)
  have hθdom := prior_restriction_domination ν μ (ENNReal.ofReal Hf) A hA hdom
    (hsupp.mono (fun p hp => hp.1))
  have hcoef : ENNReal.ofReal Hf ≤ (K : ENNReal) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hFH
  have hdomK : μ ≤ K • θ.prod volume := by
    intro E
    exact (hθdom E).trans (mul_le_mul' hcoef le_rfl)
  have hmassReal : h * (θ univ).toReal / (K : ℝ) ≤ (μ univ).toReal := by
    have hr := ENNReal.toReal_mono (measure_ne_top μ univ) hmass
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ h / Hf)] at hr
    rw [hθ]
    calc
      _ ≤ h * (ν A).toReal / Hf := div_le_div_of_nonneg_left (by positivity) hHf₀ hFH
      _ = h / Hf * (ν A).toReal := by ring
      _ ≤ _ := hr
  have had : a ^ d = Nk ^ (-d) := by
    dsimp [a]
    rw [← Real.rpow_mul hN₀.le]
    congr 1
    ring
  have hpriorK : ENNReal.ofReal (a ^ d * h / (K : ℝ)) ≤ θ univ := by
    rw [hθ, had]
    exact (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (by positivity) hHf₀ hFH)).trans hpriorlo
  have hboxK : ∀ᵐ p ∂μ, ∀ t ∈ I, ∀ e, |Cons.ubase z h p.1 t e| ≤ (K : ℝ) :=
    hbox.mono (fun p hp t ht e => (hp t ht e).trans hFH)
  have hcoeffK : ∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ (K : ℝ) :=
    hcoeff.mono (fun l hl e => (hl e).trans hFH)
  have ht₀ : z 0 ∈ I := by
    rw [hz₀]
    exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  obtain ⟨Λ, u, v, hΛ, hΛμ, hu, hv, hbu, hbv, hBase, hvraw⟩ :=
    scalar_bounded_frame ν μ (ENNReal.ofReal Hf) hdom hK₀.le z I ht₀ hcoeffK hboxK
  have hfitK : ∀ᵐ p ∂μ, ∀ t ∈ I,
      |Cons.xL p.1 t - eval (Cons.ubase z h p.1 t) P - c p.1| ≤ ε := by
    filter_upwards [hfit] with p hp
    intro t ht
    exact (hp t ht).trans (mul_le_mul_of_nonneg_right hPH (Real.rpow_nonneg hN₀.le _))
  have hs : Measurable (finePhysicalCode b scalarPhysical) := Cons.measurable_physState b
  have hπr := hpalette r₀ hr₀ hr₁
  have hPencilRaw : ∀ q w₀,
      μ {p | finePhysicalCode b scalarPhysical p = q ∧ |p.1.2 1 - w₀| < η} ≤
        ENNReal.ofReal (1 / 2000 : ℝ) * μ ((finePhysicalCode b scalarPhysical) ⁻¹' {q}) := by
    intro q w₀
    apply original_palette_pencil_budget μ (finePhysicalCode b scalarPhysical) hs
      (fun p => p.1.2 1) (by fun_prop) π hη hK₀.le
      (by positivity : 0 ≤ (K : ℝ) * Nk ^ (-S * r₀))
    · intro j
      exact (hπr.1 j).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hFH (Real.rpow_nonneg hN₀.le _)))
    · intro q j
      exact (hπr.2 q j).trans (mul_le_mul' (mul_le_mul'
        (ENNReal.ofReal_le_ofReal hFH) le_rfl) le_rfl)
    · convert hsmall using 1 <;> ring
  have hvrawSymm : (fun p => p.1.2 1) =ᵐ[μ] (fun p => v p.1) := by
    filter_upwards [hvraw] with p hp
    exact hp.symm
  have hPencil := state_pencil_budget_of_ae_eq μ (finePhysicalCode b scalarPhysical)
    (fun p => p.1.2 1) (fun p => v p.1) hvrawSymm η (ENNReal.ofReal (1 / 2000 : ℝ)) hPencilRaw
  obtain ⟨hfinite, hcount⟩ := hjoint w hjointlo hjointhi
  let J := hfinite.toFinset
  have hJ : ∀ᵐ p ∂μ, jointPhysicalCode h ξ w z scalarPhysical p ∈ J := by
    apply ae_mem_finite_positive_codes μ _ (measurable_scalar_joint_code h ξ w z) J
    intro q hq
    apply hfinite.mem_toFinset.mpr
    simpa only [scalar_joint_code_fiber, Cons.ubase, h, ξ, mem_ofPred_eq] using hq
  rw [Set.ncard_eq_toFinset_card _ hfinite] at hcount
  have hJcard : (J.card : ℝ) ≤ (K : ℝ) / ξ ^ 2 * (a / w) ^ d := by
    calc
      _ ≤ Hf * Nk ^ (2 * Z) * (a / w) ^ d := hcount
      _ ≤ (K : ℝ) * Nk ^ (2 * Z) * (a / w) ^ d :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hFH (Real.rpow_nonneg hN₀.le _))
          (Real.rpow_nonneg (by positivity : 0 ≤ a / w) d)
      _ = _ := by rw [inverse_normalized_mesh_square hN₀ Z]; dsimp [ξ]; ring
  have hcapK : ∀ (q : Fin 2 → ℤ) (j : ℤ),
      ρ {p | (fun i => (⌊scalarPhysical p i.castSucc / (h * ξ)⌋ : ℤ)) = q ∧
        (⌊scalarPhysical p 2 / w⌋ : ℤ) = j} ≤
          ENNReal.ofReal ((K : ℝ) * (h * ξ) ^ 2 * w ^ d) := by
    intro q j
    simpa only [scalarPhysical_base, scalarPhysical_hidden] using hcap q j
  obtain ⟨lists, g, hlist, hsupport, hσμ, hheavy, hDout, hcout, hfitout, hbaseout⟩ :=
    heavy_polynomial_packet θ μ ρ K hK hC hMK hh hb hξ hξ₁ hη hw ha hR hbξ hε hθ₀ hμρ
      hdomK hmassReal u v hu hv hbu hbv Λ hΛ hΛμ z scalarPhysical measurable_scalarPhysical
      scalarPhysical_time hBase P Dp hD (fun m => (hPcoeff m).trans hPH) c hc
      (fun l => (hbc l).trans hPH) I Cons.xL (Cons.ubase z h) scalarPhysical_hidden
      (normalized_scalarPhysical h z) (hsupp.mono (fun p hp => hp.2)) hboxK hfitK
      hFineError hCoarse hPencil J hJ hJcard hcapK hpriorK
  let σ := retainedGroup μ (finePhysicalCode b scalarPhysical) (fun p => (⌊c p.1 / w⌋ : ℤ))
    lists (ENNReal.ofReal (1 / 1000 : ℝ)) g
  let P' := P + MvPolynomial.C ((g : ℝ) * w)
  rw [hθ] at hheavy hbaseout
  refine ⟨σ, P', hσμ, hheavy, hDout, hcout, hfitout, ?_, ?_⟩
  · intro q
    simpa only [normalized_scalarPhysical] using hbaseout q
  · intro r hr₀ hr₁ q j
    have hgm : Measurable (fun p : (ℕ × (Fin 5 → ℝ)) × ℝ => (⌊c p.1 / w⌋ : ℤ)) := by fun_prop
    have ht := retained_group_event_cap μ (finePhysicalCode b scalarPhysical) hs
      (fun p => (⌊c p.1 / w⌋ : ℤ)) hgm lists (ENNReal.ofReal (1 / 1000 : ℝ))
      (ENNReal.ofReal Hf) (π {v | (⌊v / (Nk ^ (-r))⌋ : ℤ) = j}) (by norm_num)
      ENNReal.ofReal_ne_top hsupport {p | (⌊p.1.2 1 / (Nk ^ (-r))⌋ : ℤ) = j} q g
      ((hpalette r hr₀ hr₁).2 q j)
    have hscale : ENNReal.ofReal Hf / ENNReal.ofReal (1 / 1000 : ℝ) ≤
        ENNReal.ofReal (1000 * (K : ℝ)) := by
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1 / 1000)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact ht.trans (mul_le_mul' (mul_le_mul' hscale le_rfl) le_rfl)

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
