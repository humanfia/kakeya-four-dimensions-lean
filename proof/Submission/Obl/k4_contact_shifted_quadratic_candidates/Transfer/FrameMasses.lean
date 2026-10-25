/- Adapted from this LOT tree, obligation o243, sessions x0835 and x0843, commits 03b09f7027bd (x0835)
   and d7d4b04a4e3e (x0843) merged, Submission/Obl/k4_contact_affine_residual_candidate_transfer/FrameMasses.lean.
   Namespace and module paths renamed; instances scoped; existing attributions below are preserved. -/
import Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer.FramePriors

/-!
# Residual incidence masses, palette caps, coverage and contact

The residual law of a label's incidence is the core mass of its node over the
parent reference; the core floor gives the residual mass floor, and the
original joint palette cap with the prior floor gives the residual palette cap.
Every core point lies in a retained node at every level (coverage), and the
residual contact defect is the original one over `q₀`.
-/

namespace Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer

open MeasureTheory Set MvPolynomial ProbabilityTheory
open Submission.Obl.k4_critical_switching_state_preparation
open Submission.Lib.K4ContactNormalization
open Frame

noncomputable section

variable {α : Type} [MeasurableSpace α] {D : Data α} {k : ℕ} {s₀ U' : ℝ}
variable {f : Frame D k s₀ U'} {Rk θ K₂ e₀' : ℝ}

theorem FrameGood.scale_eq (hg : FrameGood f Rk θ K₂ e₀') :
    f.scale = ENNReal.ofReal (f.q₀ * (D.ν k).real f.parentSet) := by
  have := hg.νprob
  rw [scale, ENNReal.ofReal_mul f.q₀_pos.le, ofReal_measureReal]

/-- The parent-time preimage of a label incidence is its node incidence. -/
theorem FrameGood.preimage_label (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) :
    f.toChart ⁻¹' ((f.level h).B i ×ˢ Data.I (f.level h).T ((f.level h).j i)) =
      f.event h (f.node h i).1 (f.node h i).2 := by
  ext p
  simp only [mem_preimage, mem_prod, event, toChart]
  rw [f.mem_resBlock_time (hg.inside hh i).1]
  rfl

theorem FrameGood.measurableSet_resBlock {h : ℕ} (i : Fin (f.retained h).card) :
    MeasurableSet (Data.I (f.level h).T ((f.level h).j i)) := measurableSet_Icc

/-- The residual incidence mass floor. -/
theorem FrameGood.res_mass (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(f.resT h : ℤ)) / θ⁻¹) *
        cond (D.ν k) f.parentSet ((f.level h).A i) ≤
      f.resμ ((f.level h).B i ×ˢ Data.I (f.level h).T ((f.level h).j i)) := by
  have := hg.νprob
  have hθ := hg.θ_pos
  have hq := f.q₀_pos
  set oi := (f.node h i).1
  obtain ⟨-, hhist⟩ := hg.inside hh i
  have hA' : MeasurableSet ((f.level h).A i) := hg.measurableSet_hist hh _ _
  have hE : MeasurableSet ((f.level h).B i ×ˢ Data.I (f.level h).T ((f.level h).j i)) :=
    hA'.prod measurableSet_Icc
  rw [f.resμ_apply hE hg.core_meas, hg.preimage_label hh i, hg.cond_eq hA' hhist,
    hg.scale_eq]
  have hPpos : 0 < (D.ν k).real f.parentSet :=
    ENNReal.toReal_pos hg.parent_pos.ne' hg.parent_ne_top
  have hfl := hg.core_floor h hh oi _ (f.node_retained h i)
  rw [← ofReal_measureReal (μ := D.ν k),
    ← ENNReal.ofReal_mul (mul_nonneg hθ.le (f.ql_pos h).le)] at hfl
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  calc
    _ ≤ ENNReal.ofReal ((f.q₀ * (D.ν k).real f.parentSet)⁻¹ *
          (θ * f.ql h * (D.ν k).real (D.A k (f.depth h) oi))) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hg.resq hh]
      have hsub : (D.ν k).real ((f.level h).A i) ≤ (D.ν k).real (D.A k (f.depth h) oi) :=
        measureReal_mono (f.hist_subset_A h oi _)
      have hql := f.ql_pos h
      calc
        f.ql h / f.q₀ / θ⁻¹ * ((D.ν k).real ((f.level h).A i) / (D.ν k).real f.parentSet) =
            (f.q₀ * (D.ν k).real f.parentSet)⁻¹ *
              (θ * f.ql h * (D.ν k).real ((f.level h).A i)) := by field_simp
        _ ≤ _ := by gcongr
    _ ≤ ENNReal.ofReal ((f.q₀ * (D.ν k).real f.parentSet)⁻¹) *
          D.μ k (f.event h oi (f.node h i).2 ∩ f.core) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      gcongr

theorem FrameGood.coeff_three (l : α) : f.coeff l 3 = D.b k l 3 := by
  rw [f.coeff_base l 3 (by decide)]; rfl

/-- The residual joint palette cap. -/
theorem FrameGood.res_joint (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m)
    (i : Fin (f.retained h).card) (v : ℝ) (v₀ : ℤ) (hv1 : Rk⁻¹ ≤ v) (hv2 : v ≤ Rk) :
    f.resμ {p | p.1 ∈ (f.level h).B i ∧ p.2 ∈ Data.I (f.level h).T ((f.level h).j i) ∧
        ⌊f.coeff p.1 3 / (D.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (D.K k ^ 2 / θ * (2 : ℝ) ^ (-(f.resT h : ℤ))) *
        cond (D.ν k) f.parentSet ((f.level h).A i) *
          D.π k {w : ℝ | ⌊w / (D.N k ^ (-v))⌋ = v₀} := by
  have := hg.νprob
  have hθ := hg.θ_pos
  have hq := f.q₀_pos
  have hK : 1 ≤ D.K k := hg.K_ge
  set oi := (f.node h i).1
  obtain ⟨-, hhist⟩ := hg.inside hh i
  have hA' : MeasurableSet ((f.level h).A i) := hg.measurableSet_hist hh _ _
  have hbin : Measurable (fun l : α => f.coeff l 3) := by
    simp only [FrameGood.coeff_three]; exact (measurable_pi_apply 3).comp hg.bmeas
  have hE : MeasurableSet {p : α × ℝ | p.1 ∈ (f.level h).B i ∧
      p.2 ∈ Data.I (f.level h).T ((f.level h).j i) ∧
        ⌊f.coeff p.1 3 / (D.N k ^ (-v))⌋ = v₀} := by
    refine (measurable_fst hA').inter ((measurable_snd measurableSet_Icc).inter ?_)
    exact measurableSet_eq_fun ((hbin.comp measurable_fst).div_const _).floor measurable_const
  rw [f.resμ_apply hE hg.core_meas, hg.cond_eq hA' hhist, hg.scale_eq]
  have hsub : f.toChart ⁻¹' {p : α × ℝ | p.1 ∈ (f.level h).B i ∧
      p.2 ∈ Data.I (f.level h).T ((f.level h).j i) ∧
        ⌊f.coeff p.1 3 / (D.N k ^ (-v))⌋ = v₀} ∩ f.core ⊆
      {p | p.1 ∈ D.B k (f.depth h) oi ∧ p.2 ∈ f.block h oi ∧
        ⌊D.b k p.1 3 / (D.N k ^ (-v))⌋ = v₀} := by
    intro p hp
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := hp
    refine ⟨f.entry_subset_B h oi _ (f.hist_subset_entry h oi _ h1), ?_, ?_⟩
    · exact (f.mem_resBlock_time (hg.inside hh i).1 p.2).mp h2
    · simpa [toChart, FrameGood.coeff_three] using h3
  have hcap := (measure_mono hsub).trans (hg.joint h hh oi v v₀ hv1 hv2)
  have hPpos : 0 < (D.ν k).real f.parentSet :=
    ENNReal.toReal_pos hg.parent_pos.ne' hg.parent_ne_top
  have hpr := hg.prior_floor_real hh oi _ (f.node_retained h i)
  have hql := f.ql_pos h
  have hKq : 0 ≤ D.K k * f.ql h := mul_nonneg (by linarith) hql.le
  have hνA : 0 ≤ (D.ν k).real (D.A k (f.depth h) oi) := measureReal_nonneg
  rw [← ofReal_measureReal (μ := D.ν k) (s := D.A k (f.depth h) oi),
    ← ENNReal.ofReal_mul hKq] at hcap
  rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
  calc
    _ ≤ ENNReal.ofReal ((f.q₀ * (D.ν k).real f.parentSet)⁻¹) *
        (ENNReal.ofReal (D.K k * f.ql h * (D.ν k).real (D.A k (f.depth h) oi)) *
          D.π k {w : ℝ | ⌊w / (D.N k ^ (-v))⌋ = v₀}) := by
      gcongr
    _ = ENNReal.ofReal ((f.q₀ * (D.ν k).real f.parentSet)⁻¹ *
          (D.K k * f.ql h * (D.ν k).real (D.A k (f.depth h) oi))) *
          D.π k {w : ℝ | ⌊w / (D.N k ^ (-v))⌋ = v₀} := by
      rw [ENNReal.ofReal_mul (p := (f.q₀ * (D.ν k).real f.parentSet)⁻¹) (by positivity)]
      ring
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
      rw [hg.resq hh]
      have hKθ : D.K k * (D.ν k).real (D.A k (f.depth h) oi) ≤
          D.K k ^ 2 / θ * (D.ν k).real ((f.level h).A i) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hθ]
        have hpr' : θ * (D.ν k).real (D.A k (f.depth h) oi) ≤
            D.K k * (D.ν k).real ((f.level h).A i) := hpr
        have := mul_le_mul_of_nonneg_left hpr' (by linarith : (0 : ℝ) ≤ D.K k)
        linarith [this]
      calc
        (f.q₀ * (D.ν k).real f.parentSet)⁻¹ *
            (D.K k * f.ql h * (D.ν k).real (D.A k (f.depth h) oi)) =
            f.ql h / f.q₀ * (D.K k * (D.ν k).real (D.A k (f.depth h) oi)) /
              (D.ν k).real f.parentSet := by field_simp
        _ ≤ f.ql h / f.q₀ * (D.K k ^ 2 / θ * (D.ν k).real ((f.level h).A i)) /
              (D.ν k).real f.parentSet := by gcongr
        _ = D.K k ^ 2 / θ * (f.ql h / f.q₀) *
              ((D.ν k).real ((f.level h).A i) / (D.ν k).real f.parentSet) := by ring

/-- A property of the residual law holds almost everywhere if it holds at the
parent-time image of every core point. -/
theorem FrameGood.ae_resμ (hg : FrameGood f Rk θ K₂ e₀') {P : α × ℝ → Prop}
    (hP : MeasurableSet {p | P p}) (h : ∀ p ∈ f.core, P (f.toChart p)) :
    ∀ᵐ p ∂f.resμ, P p := by
  apply Measure.ae_smul_measure
  rw [ae_map_iff f.toChart_measurable.aemeasurable hP]
  exact (ae_restrict_iff' hg.core_meas).mpr (Filter.Eventually.of_forall h)

/-- Every core point lies in a residual label at every level. -/
theorem FrameGood.res_cover (hg : FrameGood f Rk θ K₂ e₀') {h : ℕ} (hh : h ≤ f.m) :
    ∀ᵐ p ∂f.resμ, ∃ i : Fin (f.level h).n,
      p.1 ∈ (f.level h).B i ∧ p.2 ∈ Data.I (f.level h).T ((f.level h).j i) := by
  classical
  apply hg.ae_resμ
  · have : {p : α × ℝ | ∃ i : Fin (f.level h).n,
        p.1 ∈ (f.level h).B i ∧ p.2 ∈ Data.I (f.level h).T ((f.level h).j i)} =
        ⋃ i : Fin (f.level h).n, (f.level h).B i ×ˢ Data.I (f.level h).T ((f.level h).j i) := by
      ext p; simp [mem_prod]
    rw [this]
    exact MeasurableSet.iUnion fun i =>
      (hg.measurableSet_hist hh _ _).prod measurableSet_Icc
  · intro p hp
    obtain ⟨oi, u, hpev⟩ := hg.core_cover p hp h hh
    have hret : (oi, u) ∈ f.retained h := f.mem_retained ⟨p, hpev, hp⟩
    set j := f.labelOf h (oi, u) hret
    have hnode : f.node h j = (oi, u) := f.node_labelOf h (oi, u) hret
    refine ⟨j, ?_, ?_⟩
    · change p.1 ∈ f.hist h (f.node h j).1 (f.node h j).2
      rw [hnode]; exact hpev.1
    · change (p.2 - f.t₀) / f.q₀ ∈ Data.I (f.level h).T ((f.level h).j j)
      rw [f.mem_resBlock_time (hg.inside hh j).1, hnode]
      exact hpev.2

/-- The residual contact defect. -/
theorem FrameGood.res_contact (hg : FrameGood f Rk θ K₂ e₀') :
    ∀ᵐ p ∂f.resμ, |f.coeff p.1 4 + f.coeff p.1 0| ≤ D.N k ^ (-e₀') := by
  apply hg.ae_resμ
  · have hm : Measurable (fun l : α => f.coeff l 4 + f.coeff l 0) := by
      have : (fun l : α => f.coeff l 4 + f.coeff l 0) =
          fun l => (D.b k l 4 + D.b k l 0) / f.q₀ := by
        funext l; rw [f.coeff_base l 4 (by decide), f.coeff_base l 0 (by decide),
          contactChart_contact_error]
      rw [this]
      exact (((measurable_pi_apply 4).comp hg.bmeas).add
        ((measurable_pi_apply 0).comp hg.bmeas)).div_const _
    exact measurableSet_le (hm.comp measurable_fst).abs measurable_const
  · intro p hp
    change |f.coeff p.1 4 + f.coeff p.1 0| ≤ _
    rw [f.coeff_base p.1 4 (by decide), f.coeff_base p.1 0 (by decide),
      contactChart_contact_error, abs_div, abs_of_pos f.q₀_pos]
    exact hg.contact p hp

end

end Submission.Obl.k4_contact_shifted_quadratic_candidates.Transfer
