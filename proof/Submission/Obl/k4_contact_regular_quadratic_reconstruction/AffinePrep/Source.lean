import Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep.Witness
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.QuarterSource
import Submission.Obl.k4_contact_regular_quadratic_reconstruction.Transfer.SourceBounds

/-!
# The quarter-band source of a shifted candidate

From the witnesses of a shifted candidate we keep the incidences with bounded horizontal
coefficients and the contact equation (a null exception), trim observed times near the block
ends (charged to the original product domination), and select a quarter band of the residual
`w - L` at observation (`exists_quarter_residual_source`).
-/

namespace Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep

open MeasureTheory Set MvPolynomial Filter
open Submission.Obl.k4_critical_switching_state_preparation.Data

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem I_eq_Icc (T : ℕ) (j : Fin (2 ^ T)) :
    I T j = Icc (((j : ℕ) : ℝ) / (2 : ℝ) ^ T) (((j : ℕ) : ℝ) / (2 : ℝ) ^ T + ((2 : ℝ) ^ T)⁻¹) := by
  unfold I
  congr 1
  rw [add_div, one_div]

/-- The trimmed observed times. -/
def trimSet (t₀ q h : ℝ) : Set (α × ℝ) := {p | t₀ + q * h ≤ p.2 ∧ p.2 ≤ t₀ + q - q * h}

theorem measurableSet_trimSet (t₀ q h : ℝ) : MeasurableSet (trimSet (α := α) t₀ q h) := by
  unfold trimSet
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_const)

/-- Observed times near the ends of a block cost little original mass. -/
theorem trim_loss (μ : Measure (α × ℝ)) (ν : Measure α) {K : ℝ}
    (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume)) (B : Set α) (hB : MeasurableSet B)
    {t₀ q h : ℝ} (hq : 0 ≤ q) (hh : 0 ≤ h) (W : Set (α × ℝ))
    (hW : ∀ p ∈ W, p.1 ∈ B ∧ p.2 ∈ Icc t₀ (t₀ + q)) :
    μ (W ∩ (trimSet t₀ q h)ᶜ) ≤ ENNReal.ofReal K * (ν B * ENNReal.ofReal (2 * (q * h))) := by
  set Ends : Set ℝ := Icc t₀ (t₀ + q * h) ∪ Icc (t₀ + q - q * h) (t₀ + q) with hEnds
  have hsub : W ∩ (trimSet t₀ q h)ᶜ ⊆ B ×ˢ Ends := by
    intro p ⟨hpW, hpT⟩
    obtain ⟨hpB, hpI⟩ := hW p hpW
    refine ⟨hpB, ?_⟩
    simp only [trimSet, mem_compl_iff, mem_setOf_eq, not_and_or, not_le] at hpT
    rcases hpT with h1 | h1
    · exact Or.inl ⟨hpI.1, h1.le⟩
    · exact Or.inr ⟨h1.le, hpI.2⟩
  have hEm : MeasurableSet Ends := measurableSet_Icc.union measurableSet_Icc
  have hvol : volume Ends ≤ ENNReal.ofReal (2 * (q * h)) := by
    calc volume Ends ≤ volume (Icc t₀ (t₀ + q * h)) + volume (Icc (t₀ + q - q * h) (t₀ + q)) :=
          measure_union_le _ _
      _ = ENNReal.ofReal (q * h) + ENNReal.ofReal (q * h) := by
          rw [Real.volume_Icc, Real.volume_Icc]
          congr 1 <;> congr 1 <;> ring
      _ = ENNReal.ofReal (2 * (q * h)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  calc μ (W ∩ (trimSet t₀ q h)ᶜ) ≤ μ (B ×ˢ Ends) := measure_mono hsub
    _ ≤ (ENNReal.ofReal K • (ν.prod volume)) (B ×ˢ Ends) := hdom _
    _ = ENNReal.ofReal K * (ν B * volume Ends) := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod]
    _ ≤ ENNReal.ofReal K * (ν B * ENNReal.ofReal (2 * (q * h))) := by gcongr

/-- **Quarter-band source.** -/
theorem quarter_source {cfg : Model α} (h : cfg.Valid) {k : ℕ} {s v η : ℝ}
    {i : Fin (cfg.n k s)} {L : Fin 4 → ℝ} {G : MvPolynomial (Fin 4) ℝ}
    (hB : MeasurableSet (cfg.B k s i)) {hm : ℝ} (hhm : 0 ≤ hm)
    (htrim : ENNReal.ofReal (cfg.K k) * (cfg.ν k (cfg.B k s i) *
      ENNReal.ofReal (2 * (((2 : ℝ) ^ cfg.T k s)⁻¹ * hm))) ≤
        cfg.ρ k (shiftedWitness cfg k s v η i L G) / 2) :
    ∃ (γ : ℝ) (E : Set (α × ℝ)), |γ| ≤ 9 / 8 ∧ MeasurableSet E ∧
      E ⊆ shiftedWitness cfg k s v η i L G ∧ E ⊆ goodSet cfg k ∧
      E ⊆ trimSet (((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s)
        (((2 : ℝ) ^ cfg.T k s)⁻¹) hm ∧
      cfg.ρ k (shiftedWitness cfg k s v η i L G) / 18 ≤ cfg.ρ k E ∧
      ∀ p ∈ E, |cfg.shiftedPoint k L p.1 p.2 3 - γ| ≤ 1 / 8 := by
  set t₀ : ℝ := ((cfg.j k s i : ℕ) : ℝ) / (2 : ℝ) ^ cfg.T k s with ht₀
  set q : ℝ := ((2 : ℝ) ^ cfg.T k s)⁻¹ with hqdef
  have hq : 0 ≤ q := by positivity
  obtain ⟨hb, hν, _, hdom, hρμ, _⟩ := h.basic k
  set W := shiftedWitness cfg k s v η i L G with hWdef
  have hWm : MeasurableSet W := measurableSet_shiftedWitness cfg k s v η i L G hb hB
  set W₀ := W ∩ goodSet cfg k ∩ trimSet t₀ q hm with hW₀def
  have hW₀m : MeasurableSet W₀ :=
    (hWm.inter (measurableSet_goodSet cfg k hb)).inter (measurableSet_trimSet t₀ q hm)
  -- the null exception
  have hgood0 : cfg.ρ k (goodSet cfg k)ᶜ = 0 := by
    apply le_antisymm _ bot_le
    calc cfg.ρ k (goodSet cfg k)ᶜ ≤ cfg.μ k (goodSet cfg k)ᶜ := hρμ _
      _ = 0 := by
        have := ae_goodSet h k
        rwa [ae_iff] at this
  -- the trimmed ends
  have hWI : ∀ p ∈ W, p.1 ∈ cfg.B k s i ∧ p.2 ∈ Icc t₀ (t₀ + q) := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    have := hp.2.1
    rwa [I_eq_Icc] at this
  have hends : cfg.ρ k (W ∩ (trimSet t₀ q hm)ᶜ) ≤ cfg.ρ k W / 2 :=
    ((hρμ _).trans (trim_loss (cfg.μ k) (cfg.ν k) hdom _ hB hq hhm W hWI)).trans htrim
  have hsplit : W ⊆ W₀ ∪ (goodSet cfg k)ᶜ ∪ (W ∩ (trimSet t₀ q hm)ᶜ) := by
    intro p hp
    by_cases hg : p ∈ goodSet cfg k
    · by_cases ht : p ∈ trimSet t₀ q hm
      · exact Or.inl (Or.inl ⟨⟨hp, hg⟩, ht⟩)
      · exact Or.inr ⟨hp, ht⟩
    · exact Or.inl (Or.inr hg)
  have hfin : cfg.ρ k W ≠ ⊤ := by
    have : IsFiniteMeasure (cfg.μ k) := Transfer.basic_incidence_finite cfg h.basic k
    exact ((hρμ W).trans_lt (measure_lt_top (cfg.μ k) W)).ne
  have hW₀mass : cfg.ρ k W / 2 ≤ cfg.ρ k W₀ := by
    have h1 : cfg.ρ k W ≤ cfg.ρ k W₀ + cfg.ρ k W / 2 := by
      calc cfg.ρ k W ≤ cfg.ρ k (W₀ ∪ (goodSet cfg k)ᶜ ∪ (W ∩ (trimSet t₀ q hm)ᶜ)) :=
            measure_mono hsplit
        _ ≤ cfg.ρ k (W₀ ∪ (goodSet cfg k)ᶜ) + cfg.ρ k (W ∩ (trimSet t₀ q hm)ᶜ) :=
            measure_union_le _ _
        _ ≤ (cfg.ρ k W₀ + cfg.ρ k (goodSet cfg k)ᶜ) + cfg.ρ k W / 2 :=
            add_le_add (measure_union_le _ _) hends
        _ = cfg.ρ k W₀ + cfg.ρ k W / 2 := by rw [hgood0, add_zero]
    have hh : cfg.ρ k W / 2 ≠ ⊤ := ENNReal.div_ne_top hfin (by norm_num)
    have h3 : cfg.ρ k W / 2 + cfg.ρ k W / 2 ≤ cfg.ρ k W₀ + cfg.ρ k W / 2 := by
      calc cfg.ρ k W / 2 + cfg.ρ k W / 2 = cfg.ρ k W := ENNReal.add_halves _
        _ ≤ _ := h1
    exact (ENNReal.add_le_add_iff_right hh).mp h3
  -- the quarter band
  have hy : Measurable fun p : α × ℝ => cfg.shiftedPoint k L p.1 p.2 3 := by
    have e : (fun p : α × ℝ => cfg.shiftedPoint k L p.1 p.2 3) =
        fun p => shiftedPt L (cfg.b k p.1) p.2 3 := by
      funext p; rw [shiftedPoint_eq]
    rw [e]
    have hc : Continuous fun x : (Fin 6 → ℝ) × ℝ => shiftedPt L x.1 x.2 3 :=
      (continuous_apply 3).comp (continuous_shiftedPt L)
    have hj : Measurable fun p : α × ℝ => ((cfg.b k p.1, p.2) : (Fin 6 → ℝ) × ℝ) :=
      (hb.comp measurable_fst).prodMk measurable_snd
    have hm' := hc.measurable.comp hj
    exact hm'
  have hbound : ∀ᵐ p ∂cfg.ρ k, p ∈ W₀ → |cfg.shiftedPoint k L p.1 p.2 3| ≤ 1 := by
    refine Filter.Eventually.of_forall fun p hp => ?_
    exact (hp.1.1.2.2.1 p.2 hp.1.1.2.1).1
  obtain ⟨γ, E, hγ, hEm, hEW₀, hEmass, hEband⟩ :=
    Transfer.exists_quarter_residual_source (cfg.ρ k) W₀ hW₀m _ hy hbound
  refine ⟨γ, E, hγ, hEm, fun p hp => (hEW₀ hp).1.1, fun p hp => (hEW₀ hp).1.2,
    fun p hp => (hEW₀ hp).2, ?_, hEband⟩
  calc cfg.ρ k W / 18 = cfg.ρ k W / 2 / 9 := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ← mul_assoc,
          ← ENNReal.mul_inv (by norm_num) (by norm_num)]
        norm_num
    _ ≤ cfg.ρ k W₀ / 9 := ENNReal.div_le_div_right hW₀mass 9
    _ ≤ cfg.ρ k E := hEmass

end

end Submission.Obl.k4_contact_regular_quadratic_reconstruction.AffinePrep
