import Submission.Obl.k4_scalar_candidate_original_return.Core.Residual
import Submission.Obl.k4_scalar_candidate_original_return.Core.GreedyFacts
import Submission.Obl.k4_scalar_candidate_original_return.Core.Diagonal

/-!
# Globalization of candidates

If the first `J` menu scenarios covered at most `1/(4H)` of the weighted original mass at
all late stages, for every `J`, a slowly growing diagonal `J_k` would leave a residual
tangent input (`residual_input`).  The supplied `STI` then produces, frequently, a
candidate in that residual; it qualifies for a menu scenario of index below `J_k`, and its
mass lies outside the covered incidences, contradicting maximality of that scenario's
greedy family (`greedy_maximal`).
-/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Filter Set

namespace PreparedData

variable {a : PreparedData} (ha : a.Valid)
include ha

theorem exists_covering_menu (hSTI : STI) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ J : ℕ, ∃ᶠ k in atTop, ENNReal.ofReal ((4 * a.H k)⁻¹) < a.covMass θ J k := by
  by_contra hcon
  have hev : ∀ J, ∀ᶠ k in atTop, a.covMass θ J k ≤ ENNReal.ofReal ((4 * a.H k)⁻¹) := by
    intro J
    have h : ¬∃ᶠ k in atTop, ENNReal.ofReal ((4 * a.H k)⁻¹) < a.covMass θ J k :=
      fun h => hcon ⟨J, h⟩
    rw [Filter.not_frequently] at h
    exact h.mono fun k hk => not_lt.mp hk
  obtain ⟨Jk, hJk, hJkle⟩ := exists_diagonal
    (P := fun J k => a.covMass θ J k ≤ ENNReal.ofReal ((4 * a.H k)⁻¹))
    (fun k => by simp [covMass, covJ_zero ha])
    (fun J J' k hJ h => (covMass_mono ha θ hJ k).trans h) hev
  obtain ⟨ρ', n', e, he, hρ', hTI⟩ := residual_input ha (fun k g => a.CovJ θ (Jk k) k g)
    (fun k g => CovJ_measurable ha θ (Jk k) k g) (fun k => hJkle k)
  have hNge : ∀ k, 2 ≤ a.tangent k := hTI.1
  have hd0 : 0 ≤ a.rd := hTI.2.2.2.1
  have hd1 : a.rd < 1 := hTI.2.2.2.2.1
  obtain ⟨R, hR, hcand⟩ := STI.apply hSTI hTI
  obtain ⟨Jstar, hmenu⟩ := menu_cover θ hθ hθ1 R hR
  have hJev : ∀ᶠ k in atTop, Jstar ≤ Jk k := hJk.eventually_ge_atTop Jstar
  have hpl := hTI.2.2.2.2.2.2.2.2.2.2 R hR
  have hεpos : 0 < θ / (4 * R) := by
    have : 0 < R := by linarith
    positivity
  obtain ⟨k, ⟨s, c, i, P, hs1, hs2, hc1, hc2, hdeg, hcoeff, hmass⟩, hJk', hplk⟩ :=
    ((hcand (θ / (4 * R)) hεpos).and_eventually (hJev.and hpl)).exists
  obtain ⟨n, hn, hs₀pos, hc₀pos, hs₀θ, hs₀half, hc₀θ, hRσ, hεθ⟩ := hmenu s c hs1 hs2 hc1 hc2
  set σ := menu n with hσ
  set ℓ := a.nd k s with hℓdef
  set i₀ := e k s i with hi₀
  have hℓ : ℓ ∈ a.layersOf θ σ k := ⟨hs₀pos, hc₀pos, s, hs₀θ, hs₀half, rfl⟩
  have hn' : n < Jk k := lt_of_lt_of_le hn hJk'
  have hcovsub := cov_subset_CovJ ha θ hn' k ℓ hs₀pos hc₀pos hℓ i₀
  -- the plank floor of the residual input gives positive prior mass
  have hplank := (hplk s hs1 hs2).2.2.2.2.1 i
  have hNk : 2 ≤ a.tangent k := hNge k
  have hNpos : 0 < a.tangent k := by linarith
  have hN1 : 1 ≤ a.tangent k := by linarith
  have hT : (0 : ℝ) < (2 : ℝ) ^ (a.ls k ℓ).T := by positivity
  have hνpos : 0 < ν (a.p k) (a.sm k) ((a.ls k ℓ).world i₀) ((a.ls k ℓ).prior i₀) := by
    refine lt_of_lt_of_le ?_ hplank.1
    apply ENNReal.ofReal_pos.mpr
    have hK : 0 < 4 * a.rK k * a.H k ^ 2 := by
      have h1 : 1 ≤ a.rK k := ha.tangent_input.2.2.1.1 k
      have h2 : 2 ≤ a.H k := (ha.bounds k).2.2.1
      positivity
    exact div_pos (Real.rpow_pos_of_pos hNpos _) (mul_pos hK hT)
  have hνprob : IsProbabilityMeasure (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i₀)) :=
    ((ha.tangent_input.2.2.2.2.2.2.2.2.1 k).2.2.1 _).1
  have hνfin : ν (a.p k) (a.sm k) ((a.ls k ℓ).world i₀) ((a.ls k ℓ).prior i₀) ≠ ⊤ :=
    measure_ne_top _ _
  have hνreal : 0 < (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i₀) ((a.ls k ℓ).prior i₀)).toReal :=
    ENNReal.toReal_pos hνpos.ne' hνfin
  -- exponents
  have hexp_mass : -a.rd * σ.c₀ - θ * σ.c₀ ≤ -a.rd * c - θ / (4 * R) := by
    have h1 : a.rd * (c - σ.c₀) ≤ θ * σ.c₀ / 4 := by
      have habs : |c - σ.c₀| ≤ θ * σ.c₀ / 4 := hc₀θ
      calc a.rd * (c - σ.c₀) ≤ a.rd * |c - σ.c₀| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hd0
        _ ≤ 1 * |c - σ.c₀| := mul_le_mul_of_nonneg_right hd1.le (abs_nonneg _)
        _ ≤ θ * σ.c₀ / 4 := by linarith
    nlinarith
  have hexp_fit : θ / (4 * R) + (-s - c) ≤ θ * σ.c₀ - σ.s₀ - σ.c₀ := by
    have h1 : σ.s₀ - s ≤ θ * σ.c₀ / 4 := by
      have := neg_abs_le (s - σ.s₀)
      linarith [abs_sub_comm s σ.s₀]
    have h2 : σ.c₀ - c ≤ θ * σ.c₀ / 4 := by
      have := neg_abs_le (c - σ.c₀)
      linarith [abs_sub_comm c σ.c₀]
    linarith
  -- the STI candidate set lies in the scenario candidate set
  have hsub : {p : Inc | p.1 ∈ (a.ls k ℓ).prior i₀ ∧ p.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i₀) ∧
      ∀ t ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i₀),
        |x p.1 t - MvPolynomial.eval ![t, y p.1 t] P| ≤
          a.tangent k ^ (θ / (4 * R)) * a.tangent k ^ (-s - c)} ⊆
      a.candSet θ σ k ℓ i₀ P := by
    rintro p ⟨hpA, hpI, hpfit⟩
    refine ⟨⟨hpA, ?_⟩, hpI⟩
    intro t ht
    have hle : a.tangent k ^ (θ / (4 * R)) * a.tangent k ^ (-s - c) ≤ a.fitTol θ σ k := by
      rw [← Real.rpow_add hNpos]
      exact Real.rpow_le_rpow_of_exponent_le hN1 hexp_fit
    exact (hpfit t ht).trans hle
  -- admissibility
  have hadm : a.Admissible σ k P := by
    refine ⟨hdeg, fun b => (hcoeff b).trans ?_⟩
    exact Real.rpow_le_rpow_of_exponent_le hN1 hRσ
  -- threshold comparison
  have hthr_le : a.thr θ σ k ℓ i₀ ≤
      a.tangent k ^ (-a.rd * c - θ / (4 * R)) / (2 : ℝ) ^ (a.ls k ℓ).T *
        (ν (a.p k) (a.sm k) ((a.ls k ℓ).world i₀) ((a.ls k ℓ).prior i₀)).toReal := by
    unfold thr
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    apply div_le_div_of_nonneg_right _ hT.le
    exact Real.rpow_le_rpow_of_exponent_le hN1 hexp_mass
  have hthr_pos : 0 < a.thr θ σ k ℓ i₀ := by
    unfold thr
    exact mul_pos (div_pos (Real.rpow_pos_of_pos hNpos _) hT) hνreal
  have hmax := greedy_maximal ha θ σ k ℓ i₀ P hadm hthr_pos
  -- residual mass sits outside the covered incidences
  have hρ'le : ρ' k ((a.ls k ℓ).world i₀) {p : Inc | p.1 ∈ (a.ls k ℓ).prior i₀ ∧
      p.2 ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i₀) ∧
      ∀ t ∈ I (a.ls k ℓ).T ((a.ls k ℓ).time i₀),
        |x p.1 t - MvPolynomial.eval ![t, y p.1 t] P| ≤
          a.tangent k ^ (θ / (4 * R)) * a.tangent k ^ (-s - c)} ≤
      a.ρ k ((a.ls k ℓ).world i₀) (a.candSet θ σ k ℓ i₀ P \ a.cov θ σ k ℓ i₀) := by
    refine (hρ' k _ _).trans ?_
    rw [Measure.restrict_apply' (CovJ_measurable ha θ (Jk k) k _).compl]
    apply measure_mono
    intro p hp
    exact ⟨hsub hp.1, fun hc => hp.2 (hcovsub hc)⟩
  have hchain : ENNReal.ofReal (a.thr θ σ k ℓ i₀) ≤
      a.ρ k ((a.ls k ℓ).world i₀) (a.candSet θ σ k ℓ i₀ P \ a.cov θ σ k ℓ i₀) := by
    refine le_trans ?_ (hmass.trans hρ'le)
    rw [← ENNReal.ofReal_toReal hνfin, ← ENNReal.ofReal_mul
      (div_nonneg (Real.rpow_nonneg hNpos.le _) hT.le)]
    exact ENNReal.ofReal_le_ofReal hthr_le
  exact absurd (hchain.trans_lt hmax) (lt_irrefl _)

end PreparedData

end Submission.Obl.k4_scalar_candidate_original_return
