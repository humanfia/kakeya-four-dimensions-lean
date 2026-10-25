import Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets.FinalTest

set_option autoImplicit false

/-!
# Recovering labelled time fibers (paper, end of the proof of `prop:higher-jets`)

If at every test time `t'` of the root block where the row misses a polynomial `P` by more than
`θ`, the trajectories of `D` labelled at `t'` carry prior mass at most `εb`, and the labelled
mass of `D` integrated over the block exceeds `h εb + τ`, then one trajectory of `D` has good
labelled times of total length `> τ` in the block (Tonelli), and any of them is a fitted incidence.
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

open MeasureTheory Set

noncomputable section

/-- The half-open dyadic block of length `2⁻ᵀ` containing `u`. -/
def blockIco (T : ℕ) (u : ℝ) : Set ℝ :=
  Ico ((⌊u * 2 ^ T⌋ : ℝ) / 2 ^ T) (((⌊u * 2 ^ T⌋ : ℝ) + 1) / 2 ^ T)

theorem measurableSet_blockIco (T : ℕ) (u : ℝ) : MeasurableSet (blockIco T u) :=
  measurableSet_Ico

theorem volume_blockIco (T : ℕ) (u : ℝ) : volume (blockIco T u) = ENNReal.ofReal ((2 ^ T)⁻¹) := by
  rw [blockIco, Real.volume_Ico]
  congr 1
  field_simp
  ring

theorem floor_eq_of_mem_blockIco {T : ℕ} {u t : ℝ} (ht : t ∈ blockIco T u) :
    ⌊t * 2 ^ T⌋ = ⌊u * 2 ^ T⌋ := by
  have h2 : (0 : ℝ) < 2 ^ T := by positivity
  obtain ⟨h1, h3⟩ := ht
  rw [Int.floor_eq_iff]
  constructor
  · rw [div_le_iff₀ h2] at h1; exact h1
  · rw [lt_div_iff₀ h2] at h3; exact h3

theorem dyadicBlock_eq_of_mem_blockIco {T : ℕ} {u t : ℝ} (ht : t ∈ blockIco T u) :
    dyadicBlock T t = dyadicBlock T u := by
  simp only [dyadicBlock, floor_eq_of_mem_blockIco ht]

theorem blockIco_subset_dyadicBlock (T : ℕ) (u : ℝ) : blockIco T u ⊆ dyadicBlock T u :=
  Ico_subset_Icc_self

theorem mem_blockIco_self (T : ℕ) (u : ℝ) : u ∈ blockIco T u := by
  have h2 : (0 : ℝ) < 2 ^ T := by positivity
  constructor
  · rw [div_le_iff₀ h2]; exact Int.floor_le _
  · rw [lt_div_iff₀ h2]; exact Int.lt_floor_add_one _

theorem abs_sub_le_of_mem_blockIco {T : ℕ} {u t : ℝ} (ht : t ∈ blockIco T u) :
    |t - u| ≤ (2 ^ T)⁻¹ := by
  have hu := mem_blockIco_self T u
  obtain ⟨a1, a2⟩ := ht
  obtain ⟨b1, b2⟩ := hu
  have : ((⌊u * 2 ^ T⌋ : ℝ) + 1) / 2 ^ T - (⌊u * 2 ^ T⌋ : ℝ) / 2 ^ T = (2 ^ T)⁻¹ := by
    field_simp; ring
  rw [abs_le]; constructor <;> linarith

variable {Λ : Type*} [MeasurableSpace Λ]

/-- **Fiber recovery.** -/
theorem root_fiber {ν : Measure Λ} [IsFiniteMeasure ν] {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    {F : ℝ → ℝ} (hF : Measurable F) {D : Set Λ} (hD : MeasurableSet D) (hDν : ν D ≤ 1)
    {u : ℝ} {T : ℕ} {θ εb τ : ℝ} (P : Polynomial ℝ) (hεb : 0 ≤ εb) (hτ : 0 ≤ τ)
    (hbad : ∀ t' ∈ blockIco T u, θ < |F t' - P.eval t'| →
      ν {l | l ∈ D ∧ (l, t') ∈ E} ≤ ENNReal.ofReal εb)
    (hmass : ENNReal.ofReal ((2 ^ T)⁻¹ * εb + τ) <
      ∫⁻ t' in blockIco T u, ν {l | l ∈ D ∧ (l, t') ∈ E}) :
    ∃ l ∈ D, ∃ t', (l, t') ∈ E ∧ t' ∈ blockIco T u ∧ |F t' - P.eval t'| ≤ θ ∧
      ENNReal.ofReal τ ≤ volume {v | v ∈ blockIco T u ∧ (l, v) ∈ E ∧ |F v - P.eval v| ≤ θ} := by
  classical
  set J := blockIco T u
  have hJ : MeasurableSet J := measurableSet_blockIco T u
  set G : Set ℝ := {v | |F v - P.eval v| ≤ θ}
  have hG : MeasurableSet G :=
    measurableSet_le ((hF.sub P.continuous.measurable).abs) measurable_const
  set Z : Set (Λ × ℝ) := {p | p.1 ∈ D ∧ p.2 ∈ J ∧ p ∈ E ∧ p.2 ∈ G}
  have hZ : MeasurableSet Z :=
    (measurable_fst hD).inter ((measurable_snd hJ).inter (hE.inter (measurable_snd hG)))
  -- lower bound on the good part
  have hsplit : ∫⁻ t' in J, ν {l | l ∈ D ∧ (l, t') ∈ E} ≤
      (∫⁻ t' in J, ν {l | (l, t') ∈ Z}) + ENNReal.ofReal ((2 ^ T)⁻¹ * εb) := by
    have hpt : ∀ t' ∈ J, ν {l | l ∈ D ∧ (l, t') ∈ E} ≤
        ν {l | (l, t') ∈ Z} + (if t' ∈ G then 0 else ENNReal.ofReal εb) := by
      intro t' ht'
      by_cases hg : t' ∈ G
      · simp only [hg, if_true, add_zero]
        refine measure_mono fun l hl => ⟨hl.1, ht', hl.2, hg⟩
      · simp only [hg, if_false]
        have : θ < |F t' - P.eval t'| := lt_of_not_ge hg
        exact (hbad t' ht' this).trans le_add_self
    calc ∫⁻ t' in J, ν {l | l ∈ D ∧ (l, t') ∈ E}
        ≤ ∫⁻ t' in J, (ν {l | (l, t') ∈ Z} + (if t' ∈ G then 0 else ENNReal.ofReal εb)) :=
          setLIntegral_mono' hJ hpt
      _ = (∫⁻ t' in J, ν {l | (l, t') ∈ Z}) +
            ∫⁻ t' in J, (if t' ∈ G then 0 else ENNReal.ofReal εb) := by
          have hm : Measurable (fun t' : ℝ => if t' ∈ G then (0 : ENNReal) else ENNReal.ofReal εb) :=
            Measurable.ite hG measurable_const measurable_const
          rw [lintegral_add_right _ hm]
      _ ≤ (∫⁻ t' in J, ν {l | (l, t') ∈ Z}) + ∫⁻ _t' in J, ENNReal.ofReal εb := by
          gcongr with t'
          split_ifs <;> simp
      _ = (∫⁻ t' in J, ν {l | (l, t') ∈ Z}) + ENNReal.ofReal ((2 ^ T)⁻¹ * εb) := by
          rw [setLIntegral_const, volume_blockIco, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  have hZmass : ENNReal.ofReal τ < (ν.prod volume) Z := by
    have h1 : (ν.prod volume) Z = ∫⁻ t', ν {l | (l, t') ∈ Z} := by
      rw [Measure.prod_apply_symm hZ]; rfl
    have h2 : ∫⁻ t', ν {l | (l, t') ∈ Z} = ∫⁻ t' in J, ν {l | (l, t') ∈ Z} := by
      rw [← lintegral_indicator hJ]
      congr 1
      ext t'
      by_cases ht : t' ∈ J
      · simp [ht]
      · simp only [ht, not_false_eq_true, indicator_of_notMem]
        have : {l | (l, t') ∈ Z} = ∅ := by
          ext l; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro h; exact ht h.2.1
        rw [this, measure_empty]
    rw [h1, h2]
    by_contra hle
    push Not at hle
    have := hmass.trans_le (hsplit.trans (add_le_add hle le_rfl))
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_comm] at this
    exact lt_irrefl _ this
  -- some fiber is long
  have hex : ∃ l, ENNReal.ofReal τ < volume {v | (l, v) ∈ Z} := by
    by_contra hall
    push Not at hall
    have h1 : (ν.prod volume) Z = ∫⁻ l, volume (Prod.mk l ⁻¹' Z) ∂ν := Measure.prod_apply hZ
    have h2 : ∫⁻ l, volume (Prod.mk l ⁻¹' Z) ∂ν ≤ ∫⁻ l, D.indicator (fun _ => ENNReal.ofReal τ) l ∂ν := by
      apply lintegral_mono
      intro l
      by_cases hl : l ∈ D
      · simp only [hl, indicator_of_mem]; exact hall l
      · simp only [hl, not_false_eq_true, indicator_of_notMem]
        have : Prod.mk l ⁻¹' Z = ∅ := by
          ext v; simp only [mem_preimage, mem_empty_iff_false, iff_false]
          intro h; exact hl h.1
        rw [this, measure_empty]
    rw [lintegral_indicator_const hD] at h2
    have h3 : ENNReal.ofReal τ * ν D ≤ ENNReal.ofReal τ := by
      calc ENNReal.ofReal τ * ν D ≤ ENNReal.ofReal τ * 1 := by gcongr
        _ = ENNReal.ofReal τ := mul_one _
    have := hZmass.trans_le (h1 ▸ h2.trans h3)
    exact lt_irrefl _ this
  obtain ⟨l, hl⟩ := hex
  have hpos : volume {v | (l, v) ∈ Z} ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hl)
  obtain ⟨t', ht'⟩ := nonempty_of_measure_ne_zero hpos
  obtain ⟨hlD, ht'J, ht'E, ht'G⟩ := ht'
  refine ⟨l, hlD, t', ht'E, ht'J, ht'G, hl.le.trans (measure_mono ?_)⟩
  intro v hv
  exact ⟨hv.2.1, hv.2.2.1, hv.2.2.2⟩

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
