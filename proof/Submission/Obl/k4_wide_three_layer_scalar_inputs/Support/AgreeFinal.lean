import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.AgreeSums
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Agreement

set_option linter.unusedVariables false

/-!
# Coefficient agreement and consensus for a compared block

At fine states with conditional velocity domination, the coarse coefficient classes of a
compared block agree, after discarding a power-small fraction: the accepted state consensus
supplies a center class for every fine state and a measurable set on which every incidence
agrees with the center of its fine state, keeping half of every occupied state.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_critical_conditional_row_preparation

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H R : ℝ}

namespace ComparedBlock

attribute [local instance] ComparedBlock.instΓ ComparedBlock.instΛ

variable (CB : ComparedBlock cfg k s u v χ H) (P : AgreeParams)

/-- The box of fine states of good incidences. -/
def sigBox (_CB : ComparedBlock cfg k s u v χ H) (P : AgreeParams) : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun i : Fin 4 => Finset.Icc
    ((![0, ⌊-cfg.K k / P.δz⌋, ⌊-cfg.K k / P.δU⌋, ⌊-cfg.K k / P.δX⌋] : Fin 4 → ℤ) i)
    ((![⌊1 / P.δz⌋, ⌊cfg.K k / P.δz⌋, ⌊cfg.K k / P.δU⌋, ⌊cfg.K k / P.δX⌋] : Fin 4 → ℤ) i))

theorem good_sig_mem (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k) (hK : 1 ≤ cfg.K k)
    (hL : HorizontalForm (cfg.F k s CB.i) CB.L) (hδz : 0 < P.δz) (hδU : 0 < P.δU)
    (hδX : 0 < P.δX) {p : α × ℝ} (hp : CB.Good p) : CB.sig P p ∈ CB.sigBox P := by
  obtain ⟨hzt, hzZ, htr, hres, -⟩ := CB.good_bounds hB hN hK hL hp
  simp only [sigBox, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  fin_cases i <;> simp only [sig, sigmaState, coords, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three] <;> constructor
  · exact Int.floor_nonneg.mpr (div_nonneg hzt.1 hδz.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right hzt.2 hδz.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith [(abs_le.mp hzZ).1]) hδz.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith [(abs_le.mp hzZ).2]) hδz.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith [(abs_le.mp htr).1]) hδU.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith [(abs_le.mp htr).2]) hδU.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith [(abs_le.mp hres).1]) hδX.le)
  · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith [(abs_le.mp hres).2]) hδX.le)

/-- The finite encoding of fine states. -/
def sigF (q₀ : CB.sigBox P) (p : α × ℝ) : CB.sigBox P :=
  if h : CB.sig P p ∈ CB.sigBox P then ⟨CB.sig P p, h⟩ else q₀

theorem measurable_sig (hb : Measurable (cfg.b k)) : Measurable (CB.sig P) :=
  measurable_sigmaState CB.frame P.δz P.δU P.δX hb

theorem measurable_sigF (hb : Measurable (cfg.b k)) (q₀ : CB.sigBox P) :
    Measurable (CB.sigF P q₀) := by
  apply measurable_to_countable'
  intro q
  have hs := CB.measurable_sig P hb
  have hset : CB.sigF P q₀ ⁻¹' {q} = (CB.sig P ⁻¹' {q.1}) ∪
      (if q = q₀ then {p | CB.sig P p ∉ CB.sigBox P} else ∅) := by
    ext p
    simp only [sigF, mem_preimage, mem_singleton_iff, mem_union]
    split_ifs with h1 h2 h2
    · subst h2
      constructor
      · intro h; left; rw [← h]
      · rintro (h | h)
        · exact Subtype.ext h
        · exact (h h1).elim
    · constructor
      · intro h; left; rw [← h]
      · rintro (h | h)
        · exact Subtype.ext h
        · exact h.elim
    · subst h2
      constructor
      · intro _; right; exact h1
      · rintro (h | h)
        · exact (h1 (h ▸ q.2)).elim
        · rfl
    · constructor
      · intro h; exact (h2 h.symm).elim
      · rintro (h | h)
        · exact (h1 (h ▸ q.2)).elim
        · exact h.elim
  rw [hset]
  apply MeasurableSet.union (hs (measurableSet_singleton _))
  split_ifs
  · exact (hs (Finset.measurableSet _)).compl
  · exact MeasurableSet.empty

theorem sigF_of_mem (q₀ : CB.sigBox P) {p : α × ℝ} (h : CB.sig P p ∈ CB.sigBox P) :
    CB.sigF P q₀ p = ⟨CB.sig P p, h⟩ := by
  simp [sigF, h]

/-- The explicit loss bound of the coefficient agreement. -/
def agreeLoss (C₁ : ℝ≥0∞) (r s' v' θm w LipU ρN : ℝ) : ℝ≥0∞ :=
  C₁ * ENNReal.ofReal (θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
        4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm) *
    ENNReal.ofReal (2 * H * (2 * ρN / χ + 1)) *
    ((Finset.Icc (0 : ℤ) ⌊1 / P.δt⌋).card *
      (ENNReal.ofReal (6000 * cfg.K k * (CB.frame.q * P.δt / 2) * χ *
        (CB.frame.q * CB.frame.g * P.δU / 2 + cfg.K k * χ) * (cfg.N k ^ (-s')) ^ cfg.d) *
      (ENNReal.ofReal (H * cfg.N k ^ (cfg.d * u)) *
        ENNReal.ofReal (2 * H * (2 * (cfg.K k * CB.frame.q + 2 * χ) / χ + 1))) /
      ENNReal.ofReal P.δU))

open scoped Classical in
/-- **Coefficient agreement and consensus.** -/
theorem agreement_final (hcap : CapsAt cfg k R) (hB : BlocksAt cfg k s R) (hN : 0 < cfg.N k)
    (hK : 1 ≤ cfg.K k) (hb : Measurable (cfg.b k)) (hL : HorizontalForm (cfg.F k s CB.i) CB.L)
    (hχ : 0 < χ) (hH : 1 ≤ H) (hπ : IsProbabilityMeasure (cfg.π k))
    (hδt : 0 < P.δt) (hδt2 : P.δt ≤ 2) (hδz : 0 < P.δz) (hδU : 0 < P.δU) (hδX : 0 < P.δX)
    (he : 0 < P.e)
    {ρ2 ρN w : ℝ}
    (hρ2 : χ / CB.frame.q + P.δt * (2 * cfg.K k + χ) / 2 ≤ ρ2)
    (hρN : 2 * χ + (CB.frame.q * P.δt + CB.frame.q * P.δz) * (3 * cfg.K k + χ) +
        (cfg.K k + 1) * (CB.frame.q * P.δz) ≤ ρN)
    (hgap : P.e + 2 * H * (P.δz + P.δt / 2 + ρ2) ≤ P.eR)
    (hw : (2 * H + 2) * cfg.N k ^ (-u) + P.δX + H * ((1 + 2 * 2 + (cfg.K k + ρ2) + cfg.K k) *
        (2 * (P.δt / 2) + P.δz) + (1 + 2 + 2 * (cfg.K k + ρ2) + cfg.K k) * (2 * ρ2 + P.δz) +
        (1 + 2 + (cfg.K k + ρ2) + 2 * cfg.K k) * P.δU) ≤ w) (hw0 : 0 ≤ w)
    {r s' v' Lb θm LipU : ℝ} (hr1 : R⁻¹ ≤ r) (hr2 : r ≤ R) (hs1 : 0 ≤ s') (hs2 : s' ≤ R)
    (hv1 : R⁻¹ ≤ v') (hv2 : v' ≤ R)
    (hwin : CB.frame.a * (2 * H + 1) * cfg.N k ^ (-u) = cfg.N k ^ (-s'))
    (hLb : ∀ e, |CB.L e| ≤ Lb) (hg1 : CB.frame.g ≤ 1)
    (hδv : cfg.N k ^ (-v') ≤ χ) (hχK : χ ≤ cfg.K k)
    (hm1 : cfg.N k ^ (-r) ≤ CB.frame.q * P.δt / 2)
    (hm2 : 5 * cfg.K k ^ 2 * cfg.N k ^ (-r) ≤ χ)
    (hm3 : 5 * cfg.K k ^ 2 * cfg.N k ^ (-r) ≤ CB.frame.q * CB.frame.g * P.δU / 2)
    (hm4 : (3 + 3 * cfg.K k) * cfg.N k ^ (-r) ≤ CB.frame.q * CB.frame.g)
    (hlip : 3 * Lb * cfg.N k ^ (-r) + CB.frame.a * H * (3 * cfg.K k + 7) * (3 * cfg.K k + 3) *
      cfg.N k ^ (-r) / (CB.frame.q * CB.frame.g) ≤ cfg.N k ^ (-s'))
    (hθm : 0 < θm) (hθme : θm ≤ P.e / 2)
    (hLipU : ∀ sr ∈ CB.SrcF, ∀ c ∈ Finset.Icc (0 : ℤ) ⌊1 / P.δt⌋,
      ∀ γ', CB.Near P ρN sr c γ' →
        CB.lam {p | CB.src p = sr ∧ CB.cell P p = c} ≠ 0 →
        |CB.cδ₁ P sr c γ'| + 2 * |CB.cδ₂ sr γ'| * (cfg.K k + P.δU) ≤ LipU)
    (lam1 : Measure (α × ℝ)) [IsFiniteMeasure lam1] (hlam1 : lam1 ≤ CB.lam)
    (hlamμ : lam1 ≤ cfg.μ k) (C₁ : ℝ≥0∞) (hC₁ : C₁ ≠ ∞) (hΓ : Nonempty CB.Γ)
    (hdom : ∀ (q : Fin 4 → ℤ) (A : Set ℤ),
      lam1 {p | CB.sig P p = q ∧ vbin (cfg.N k ^ (-v')) (cfg.b k p.1 3) ∈ A} ≤
        C₁ * lam1 (CB.sig P ⁻¹' {q}) * paletteBins (cfg.π k) (cfg.N k ^ (-v')) A) :
    ∃ (center : (Fin 4 → ℤ) → CB.Γ) (Hc : Set (α × ℝ)), MeasurableSet Hc ∧
      (∀ p ∈ Hc, CB.Rg P (CB.sig P p) (CB.cls p) (center (CB.sig P p))) ∧
      (∀ q, lam1.real (Hc ∩ CB.sig P ⁻¹' {q}) = 0 ∨
        lam1.real (CB.sig P ⁻¹' {q}) / 2 ≤ lam1.real (Hc ∩ CB.sig P ⁻¹' {q})) ∧
      lam1.real univ ≤ lam1.real Hc + 2 * (CB.agreeLoss P C₁ r s' v' θm w LipU ρN).toReal := by
  have hK0 : 0 ≤ cfg.K k := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hq : 0 < CB.frame.q := by simp only [frame, blockFrame]; positivity
  have hac : lam1 ≪ CB.lam := Measure.absolutelyContinuous_of_le hlam1
  have hgood : ∀ᵐ p ∂lam1, CB.Good p := hac.ae_le CB.ae_good
  set δv := cfg.N k ^ (-v') with hδvdef
  have hv0 : 0 < δv := Real.rpow_pos_of_pos hN _
  -- the encoding of fine states
  set lo : Fin 4 → ℤ := ![0, ⌊-cfg.K k / P.δz⌋, ⌊-cfg.K k / P.δU⌋, ⌊-cfg.K k / P.δX⌋]
  have hlo : lo ∈ CB.sigBox P := by
    simp only [sigBox, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    fin_cases i <;> simp only [lo, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val_three] <;> refine ⟨le_rfl, ?_⟩
    · exact Int.floor_nonneg.mpr (by positivity)
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδz.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδU.le)
    · exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith) hδX.le)
  set q₀ : CB.sigBox P := ⟨lo, hlo⟩
  set σF := CB.sigF P q₀ with hσFdef
  have hσF : Measurable σF := CB.measurable_sigF P hb q₀
  letI : MeasurableSpace CB.Γ := ⊤
  have : MeasurableSingletonClass CB.Γ := ⟨fun _ => trivial⟩
  have hclsm : Measurable CB.cls := by
    intro S _
    have : CB.cls ⁻¹' S = ⋃ x ∈ Finset.univ.filter (fun x : CB.Λ => CB.crs x ∈ S),
        (fun p : α × ℝ => CB.lab p.1) ⁻¹' {x} := by
      ext p; simp [cls]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun x _ => measurable_fst (CB.lab_meas x)
  have hinbox : ∀ᵐ p ∂lam1, CB.sig P p ∈ CB.sigBox P :=
    hgood.mono fun p hp => CB.good_sig_mem P hB hN hK hL hδz hδU hδX hp
  have hiff : ∀ q : CB.sigBox P, ∀ᵐ p ∂lam1, (σF p = q ↔ CB.sig P p = q.1) := by
    intro q
    filter_upwards [hinbox] with p hp
    rw [hσFdef, CB.sigF_of_mem P q₀ hp, Subtype.ext_iff]
  have hcongr : ∀ (q : CB.sigBox P) (Φ : α × ℝ → Prop),
      lam1 {p | σF p = q ∧ Φ p} = lam1 {p | CB.sig P p = q.1 ∧ Φ p} := by
    intro q Φ
    apply measure_congr
    refine Filter.Eventually.set_eq ?_
    filter_upwards [hiff q] with p hp
    simp only [hp]
  have hcongr' : ∀ q : CB.sigBox P, lam1 (σF ⁻¹' {q}) = lam1 (CB.sig P ⁻¹' {q.1}) := by
    intro q
    have h1 := hcongr q (fun _ => True)
    simp only [and_true] at h1
    exact h1
  -- domination for the encoding
  have hdomF : ∀ (q : CB.sigBox P) (A : Set ℤ),
      lam1 {p | σF p = q ∧ vbin δv (cfg.b k p.1 3) ∈ A} ≤
        C₁ * lam1 (σF ⁻¹' {q}) * paletteBins (cfg.π k) δv A := by
    intro q A
    rw [hcongr q (fun p => vbin δv (cfg.b k p.1 3) ∈ A), hcongr' q]
    exact hdom q.1 A
  -- velocity bins of the coarse classes
  have hvb : ∀ᵐ p ∂lam1, vbin δv (cfg.b k p.1 3) ∈ Vt δv χ (CB.chartOf (CB.cls p)).1 := by
    filter_upwards [hgood] with p hp
    have hch : CB.chart p = CB.chartOf (CB.cls p) := hp.chart
    rw [← hch]
    exact vbin_mem_Vt hv0 hχ hδv
  have hπV : IsProbabilityMeasure (paletteBins (cfg.π k) δv) := isProbabilityMeasure_paletteBins _ _
  have hpair := consensus_pair_le lam1 σF CB.cls hσF hclsm CB.cls Finset.univ
    (ae_of_all _ fun p => Finset.mem_univ _) id (fun p => vbin δv (cfg.b k p.1 3))
    (fun γ => Vt δv χ (CB.chartOf γ).1) (paletteBins (cfg.π k) δv) C₁ hC₁
    (ae_of_all _ fun _ => rfl) hvb hdomF (fun q γ γ' => CB.Rg P q.1 γ γ')
  -- the matching step for the encoding
  set CF : Finset ℤ := Finset.Icc 0 ⌊1 / P.δt⌋
  have hsrc : ∀ᵐ p ∂lam1, CB.src p ∈ CB.SrcF ∧ CB.cell P p ∈ CF := by
    filter_upwards [hgood] with p hp
    refine ⟨CB.good_src_mem hB hN hK hL hχ hp, ?_⟩
    obtain ⟨hzt, -⟩ := CB.good_bounds hB hN hK hL hp
    simp only [CF, Finset.mem_Icc, cell]
    exact ⟨Int.floor_nonneg.mpr (div_nonneg hzt.1 hδt.le),
      Int.floor_mono (div_le_div_of_nonneg_right hzt.2 hδt.le)⟩
  have hmatch0 := CB.match_step P hB hN hK hL hχ hH hδt hδt2 hδz hδU hδX lam1 hlam1 hρ2 hρN hgap hw
  have hmatchF : ∀ᵐ p ∂lam1, ∀ γ, lam1 {x | σF x = σF p ∧ CB.cls x = γ} ≠ 0 →
      ¬ CB.Rg P (σF p).1 γ (CB.cls p) →
      CB.Near P ρN (CB.src p) (CB.cell P p) γ ∧
        CB.frame.tr (cfg.b k p.1) p.2 ∈ CB.Mset P w (cfg.K k) (CB.src p) (CB.cell P p) γ := by
    filter_upwards [hmatch0, hinbox] with p hp hpbox γ hocc hR
    have hσp : σF p = ⟨CB.sig P p, hpbox⟩ := CB.sigF_of_mem P q₀ hpbox
    rw [hσp] at hocc hR
    apply hp γ _ hR
    rwa [hcongr ⟨CB.sig P p, hpbox⟩ (fun x => CB.cls x = γ)] at hocc
  -- the density and palette steps
  have hdens : ∀ sr ∈ CB.SrcF, ∀ c ∈ CF, ∀ γ, CB.Near P ρN sr c γ →
      lam1 {p | CB.src p = sr ∧ CB.cell P p = c ∧
        (fun p : α × ℝ => CB.frame.tr (cfg.b k p.1) p.2) p ∈ CB.Mset P w (cfg.K k) sr c γ} ≤
        (CB.capcell P r s' v' sr / ENNReal.ofReal P.δU) *
          ENNReal.ofReal (θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
            4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm) := by
    intro sr hsr c hc γ hnear
    by_cases hzero : CB.lam {p | CB.src p = sr ∧ CB.cell P p = c} = 0
    · calc lam1 {p | CB.src p = sr ∧ CB.cell P p = c ∧
          (fun p : α × ℝ => CB.frame.tr (cfg.b k p.1) p.2) p ∈ CB.Mset P w (cfg.K k) sr c γ}
          ≤ CB.lam {p | CB.src p = sr ∧ CB.cell P p = c} :=
            (hlam1 _).trans (measure_mono fun p hp => ⟨hp.1, hp.2.1⟩)
        _ = 0 := hzero
        _ ≤ _ := zero_le
    exact CB.dens_step P hcap hB hN hK hb hL hχ hH hδt hδU he hr1 hr2 hs1 hs2 hv1 hv2 hwin hLb
      hg1 hδv hχK hm1 hm2 hm3 hm4 hlip hθm hθme hw0 lam1 hlam1 hlamμ sr c γ
        (hLipU sr hsr c hc γ hnear hzero)
  have hPi : ∀ sr ∈ CB.SrcF, ∀ c ∈ CF,
      ∑ γ ∈ Finset.univ.filter (fun γ => CB.Near P ρN sr c γ),
        paletteBins (cfg.π k) δv (Vt δv χ (CB.chartOf γ).1) ≤
        ENNReal.ofReal (2 * H * (2 * ρN / χ + 1)) := by
    intro sr _ c _
    have hρN0 : 0 ≤ ρN := le_trans (by
      have : 0 ≤ CB.frame.q * P.δt + CB.frame.q * P.δz := by positivity
      have : 0 ≤ 3 * cfg.K k + χ := by linarith
      have : 0 ≤ (cfg.K k + 1) * (CB.frame.q * P.δz) := by positivity
      nlinarith) hρN
    exact CB.near_sum_le P hπ hχ hH0 hρN0 δv sr c
  have hsum := agreement_sum_bound lam1 σF CB.cls hσF hclsm (fun q γ γ' => CB.Rg P q.1 γ γ')
    (fun γ => paletteBins (cfg.π k) δv (Vt δv χ (CB.chartOf γ).1)) CB.src CB.SrcF (CB.cell P) CF
    (fun p => CB.frame.tr (cfg.b k p.1) p.2) (CB.Near P ρN) (CB.Mset P w (cfg.K k)) hsrc hmatchF
    (fun sr c => CB.capcell P r s' v' sr / ENNReal.ofReal P.δU) _ _ hdens hPi
  -- the explicit bound
  set ℓ := ENNReal.ofReal (θm * (4 * (cfg.K k + P.δU) + 2) / P.e +
    4 * (H * cfg.N k ^ (cfg.d * u)) * (w + P.δU * LipU) / θm)
  set Pi := ENNReal.ofReal (2 * H * (2 * ρN / χ + 1))
  set capsum := ENNReal.ofReal (6000 * cfg.K k * (CB.frame.q * P.δt / 2) * χ *
        (CB.frame.q * CB.frame.g * P.δU / 2 + cfg.K k * χ) * (cfg.N k ^ (-s')) ^ cfg.d) *
      (ENNReal.ofReal (H * cfg.N k ^ (cfg.d * u)) *
        ENNReal.ofReal (2 * H * (2 * (cfg.K k * CB.frame.q + 2 * χ) / χ + 1)))
  have hδU' : ENNReal.ofReal P.δU ≠ 0 := by simpa using hδU
  have hSig : ∑ sr ∈ CB.SrcF, ∑ c ∈ CF, CB.capcell P r s' v' sr / ENNReal.ofReal P.δU ≤
      (CF.card : ℝ≥0∞) * (capsum / ENNReal.ofReal P.δU) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum, ← ENNReal.sum_div]
    gcongr
    exact CB.src_cap_sum_le P hπ hχ hH0 hK0 hq r s' v'
  set B := ℓ * Pi * ((CF.card : ℝ≥0∞) * (capsum / ENNReal.ofReal P.δU))
  have hY := hsum.trans (mul_le_mul_right hSig _)
  have hBfin : B ≠ ∞ := by
    simp only [B, ℓ, Pi, capsum]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_)
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hδU'
  -- real form of the palette table
  have hXY : (∑ q, ∑ j, Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam1 σF CB.cls q j *
      ∑ τ ∈ Finset.univ.filter (fun τ => lam1 {p | σF p = q ∧ CB.cls p = τ} ≠ 0 ∧
        ¬ CB.Rg P q.1 (id τ) j), (paletteBins (cfg.π k) δv (Vt δv χ (CB.chartOf τ).1)).toReal) =
      (∑ q, ∑ j, lam1 {p | σF p = q ∧ CB.cls p = j} *
        ∑ γ ∈ Finset.univ.filter (fun γ => lam1 {p | σF p = q ∧ CB.cls p = γ} ≠ 0 ∧
          ¬ CB.Rg P q.1 γ j), paletteBins (cfg.π k) δv (Vt δv χ (CB.chartOf γ).1)).toReal := by
    rw [ENNReal.toReal_sum (fun q _ => ENNReal.sum_ne_top.mpr fun j _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.sum_ne_top.mpr fun _ _ => measure_ne_top _ _))]
    apply Finset.sum_congr rfl; intro q _
    rw [ENNReal.toReal_sum (fun j _ =>
      ENNReal.mul_ne_top (measure_ne_top _ _) (ENNReal.sum_ne_top.mpr fun _ _ => measure_ne_top _ _))]
    apply Finset.sum_congr rfl; intro j _
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
    rfl
  have hPS : (∑ q, (∑ j, Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam1 σF CB.cls q j *
        ∑ i, if CB.Rg P q.1 i j then 0 else
          Submission.Lib.K4OriginalStatePreparation.stateEntryWeight lam1 σF CB.cls q i) /
          lam1.real (σF ⁻¹' {q})) ≤ (CB.agreeLoss P C₁ r s' v' θm w LipU ρN).toReal := by
    refine hpair.trans ?_
    rw [hXY]
    have h1 := ENNReal.toReal_mono hBfin hY
    calc C₁.toReal * _ ≤ C₁.toReal * B.toReal := by gcongr
      _ = (C₁ * B).toReal := (ENNReal.toReal_mul).symm
      _ = _ := by
          simp only [agreeLoss, B, ℓ, Pi, capsum, CF]
          congr 1
          ring
  -- consensus
  obtain ⟨centerF, Hc, hHc, hRc, hhalf, hmass⟩ :=
    Submission.Lib.K4OriginalStatePreparation.measurable_state_consensus lam1 σF CB.cls hσF hclsm
      (fun q γ γ' => CB.Rg P q.1 γ γ')
  have hboxm : MeasurableSet {p : α × ℝ | CB.sig P p ∈ CB.sigBox P} :=
    (CB.measurable_sig P hb) (Finset.measurableSet _)
  refine ⟨fun q => if h : q ∈ CB.sigBox P then centerF ⟨q, h⟩ else Classical.choice hΓ,
    Hc ∩ {p | CB.sig P p ∈ CB.sigBox P}, hHc.inter hboxm, ?_, ?_, ?_⟩
  · rintro p ⟨hp, hpbox⟩
    have h := hRc p hp
    have hσp : σF p = ⟨CB.sig P p, hpbox⟩ := CB.sigF_of_mem P q₀ hpbox
    rw [hσp] at h
    simp only [dif_pos (show CB.sig P p ∈ CB.sigBox P from hpbox)]
    exact h
  · intro q
    by_cases hq : q ∈ CB.sigBox P
    · have s1 : (Hc ∩ {p | CB.sig P p ∈ CB.sigBox P}) ∩ CB.sig P ⁻¹' {q} =
          {p | CB.sig P p = (⟨q, hq⟩ : CB.sigBox P).1 ∧ p ∈ Hc} := by
        ext p
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h3, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1 ▸ hq⟩, h1⟩
      have s2 : Hc ∩ σF ⁻¹' {⟨q, hq⟩} = {p | σF p = ⟨q, hq⟩ ∧ p ∈ Hc} := by
        ext p
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
        exact and_comm
      have e1 : lam1.real ((Hc ∩ {p | CB.sig P p ∈ CB.sigBox P}) ∩ CB.sig P ⁻¹' {q}) =
          lam1.real (Hc ∩ σF ⁻¹' {⟨q, hq⟩}) := by
        rw [s1, s2, measureReal_def, measureReal_def, hcongr ⟨q, hq⟩ (fun p => p ∈ Hc)]
      have e2 : lam1.real (CB.sig P ⁻¹' {q}) = lam1.real (σF ⁻¹' {⟨q, hq⟩}) := by
        rw [measureReal_def, measureReal_def, hcongr' ⟨q, hq⟩]
      rw [e1, e2]
      exact hhalf ⟨q, hq⟩
    · left
      have : (Hc ∩ {p | CB.sig P p ∈ CB.sigBox P}) ∩ CB.sig P ⁻¹' {q} = ∅ := by
        ext p
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff,
          mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, hpbox⟩, hpq⟩
        exact hq (hpq ▸ hpbox)
      rw [this, measureReal_empty]
  · have e : lam1.real (Hc ∩ {p | CB.sig P p ∈ CB.sigBox P}) = lam1.real Hc := by
      rw [measureReal_def, measureReal_def]
      congr 1
      apply measure_congr
      refine Filter.Eventually.set_eq ?_
      filter_upwards [hinbox] with p hp
      exact ⟨fun h => h.1, fun h => ⟨h, hp⟩⟩
    rw [e]
    linarith

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
