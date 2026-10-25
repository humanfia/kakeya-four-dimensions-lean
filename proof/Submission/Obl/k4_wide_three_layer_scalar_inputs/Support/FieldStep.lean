import Submission.Obl.k4_wide_three_layer_scalar_inputs.Field.ChartMenus
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Field.Transport
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Good
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.Sigma
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Support.PolyLip
import Submission.Obl.k4_critical_conditional_row_preparation.Pruning
import Submission.Obl.k4_contact_affine_residual_candidate_transfer.ShearedCells
import Submission.Obl.k4_scalar_initial_true_horizon.Basic

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Support

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- The center of one coordinate of the original fine state. -/
def stateCenter (δ : ℝ) (Q : Fin 4 → ℤ) (e : Fin 4) : ℝ := ((Q e : ℝ) + 1 / 2) * δ

/-- The coefficient pair chosen at one original fine state. -/
def stateFieldValue {Γ : Type*} (tc : Γ → Fin 4 → ℝ)
    (center : (Fin 4 → ℤ) → Γ) (δ : ℝ) (Q : Fin 4 → ℤ) : Fin 2 → ℝ :=
  ![lin1 (tc (center Q)) (stateCenter δ Q 0) (stateCenter δ Q 1), tc (center Q) 3]

/-- The common-field state forgets the transverse and residual coordinates,
and appends the bins of the state-constant coefficient pair. -/
def fieldStateOf {Γ : Type*} (tc : Γ → Fin 4 → ℝ)
    (center : (Fin 4 → ℤ) → Γ) (δ e : ℝ) (Q : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![Q 0, Q 1, ⌊stateFieldValue tc center δ Q 0 / e⌋, ⌊stateFieldValue tc center δ Q 1 / e⌋]

theorem measurable_stateFieldValue {Γ : Type*} (tc : Γ → Fin 4 → ℝ)
    (center : (Fin 4 → ℤ) → Γ) (δ : ℝ) : Measurable (stateFieldValue tc center δ) :=
  measurable_of_countable _

theorem measurable_fieldStateOf {Γ : Type*} (tc : Γ → Fin 4 → ℝ)
    (center : (Fin 4 → ℤ) → Γ) (δ e : ℝ) : Measurable (fieldStateOf tc center δ e) :=
  measurable_of_countable _

/-- Coarsening to the field state preserves the conditional ORIGINAL palette. -/
theorem stateField_palette {Ω Γ : Type*} [MeasurableSpace Ω]
    (lam : Measure Ω) (σ : Ω → Fin 4 → ℤ) (hσ : Measurable σ)
    (vel : Ω → ℝ) (hv : Measurable vel) (π : Measure ℝ)
    (tc : Γ → Fin 4 → ℝ) (center : (Fin 4 → ℤ) → Γ)
    {δ e : ℝ} (hδ : 0 < δ) {C : ℝ≥0∞}
    (hdom : ∀ (Q : Fin 4 → ℤ) (A : Set ℤ),
      lam {p | σ p = Q ∧ vbin δ (vel p) ∈ A} ≤
        C * lam (σ ⁻¹' {Q}) * paletteBins π δ A) :
    ∀ (Q : Fin 4 → ℤ) (j : ℤ),
      lam {p | fieldStateOf tc center δ e (σ p) = Q ∧ ⌊vel p / δ⌋ = j} ≤
        C * lam {p | fieldStateOf tc center δ e (σ p) = Q} *
          π (Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ)) := by
  intro Q j
  have hh := Submission.Obl.k4_critical_conditional_row_preparation.coarsen_palette_cap
    lam σ hσ (fun p => vbin δ (vel p)) ((measurable_vbin δ).comp hv)
    (paletteBins π δ) (fieldStateOf tc center δ e) (measurable_fieldStateOf tc center δ e) C
    (fun Q A _ => hdom Q A) Q {j} (measurableSet_singleton j)
  rw [paletteBins_singleton, vbin_set_eq hδ] at hh
  simpa only [mem_singleton_iff, vbin] using hh

theorem stateCenter_close {δ x : ℝ} (hδ : 0 < δ) (Q : Fin 4 → ℤ) (i : Fin 4)
    (hi : ⌊x / δ⌋ = Q i) : |x - stateCenter δ Q i| ≤ δ / 2 := by
  exact Submission.Obl.k4_contact_affine_residual_candidate_transfer.abs_sub_center_of_floor hδ hi

/-- Evaluating a bounded affine coefficient at the fine-state center costs
one base mesh width. -/
theorem lin1_stateCenter_error {tc : Fin 4 → ℝ} {H δ x y : ℝ}
    (hH : 0 ≤ H) (htc : ∀ i, |tc i| ≤ H) (hδ : 0 < δ)
    (Q : Fin 4 → ℤ) (hx : ⌊x / δ⌋ = Q 0) (hy : ⌊y / δ⌋ = Q 1) :
    |lin1 tc (stateCenter δ Q 0) (stateCenter δ Q 1) - lin1 tc x y| ≤ H * δ := by
  have hx' : |stateCenter δ Q 0 - x| ≤ δ / 2 := by
    rw [abs_sub_comm]; exact stateCenter_close hδ Q 0 hx
  have hy' : |stateCenter δ Q 1 - y| ≤ δ / 2 := by
    rw [abs_sub_comm]; exact stateCenter_close hδ Q 1 hy
  have hid : lin1 tc (stateCenter δ Q 0) (stateCenter δ Q 1) - lin1 tc x y =
      tc 1 * (stateCenter δ Q 0 - x) + tc 2 * (stateCenter δ Q 1 - y) := by
    unfold lin1; ring
  rw [hid]
  calc _ ≤ |tc 1| * |stateCenter δ Q 0 - x| + |tc 2| * |stateCenter δ Q 1 - y| := by
        simpa only [abs_mul] using abs_add_le (tc 1 * (stateCenter δ Q 0 - x))
          (tc 2 * (stateCenter δ Q 1 - y))
    _ ≤ H * (δ / 2) + H * (δ / 2) := by gcongr <;> exact htc _
    _ = H * δ := by ring

theorem stateFieldValue_bound {Γ : Type*} (tc : Γ → Fin 4 → ℝ)
    (center : (Fin 4 → ℤ) → Γ) {H K δ x y : ℝ} (hH : 0 ≤ H) (hK : 1 ≤ K)
    (htc : ∀ γ e, |tc γ e| ≤ H) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (Q : Fin 4 → ℤ) (hx : ⌊x / δ⌋ = Q 0) (hy : ⌊y / δ⌋ = Q 1)
    (hxb : |x| ≤ 1) (hyb : |y| ≤ K) :
    ∀ e, |stateFieldValue tc center δ Q e| ≤ H * (K + 4) := by
  have hxc : |stateCenter δ Q 0| ≤ 2 := by
    have hclose := stateCenter_close hδ Q 0 hx
    calc _ = |x - (x - stateCenter δ Q 0)| := by congr 1; ring
      _ ≤ |x| + |x - stateCenter δ Q 0| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hyc : |stateCenter δ Q 1| ≤ K + 1 := by
    have hclose := stateCenter_close hδ Q 1 hy
    calc _ = |y - (y - stateCenter δ Q 1)| := by congr 1; ring
      _ ≤ |y| + |y - stateCenter δ Q 1| := abs_sub _ _
      _ ≤ K + 1 := by linarith
  intro e
  fin_cases e
  · change |lin1 (tc (center Q)) (stateCenter δ Q 0) (stateCenter δ Q 1)| ≤ _
    unfold lin1
    calc _ ≤ |tc (center Q) 0| + |tc (center Q) 1| * |stateCenter δ Q 0| +
          |tc (center Q) 2| * |stateCenter δ Q 1| := by
          simpa only [abs_mul] using abs_add_three (tc (center Q) 0)
            (tc (center Q) 1 * stateCenter δ Q 0) (tc (center Q) 2 * stateCenter δ Q 1)
      _ ≤ H + H * 2 + H * (K + 1) := by gcongr <;> exact htc _ _
      _ = H * (K + 4) := by ring
  · change |tc (center Q) 3| ≤ _
    exact (htc _ _).trans (by nlinarith)

namespace ComparedBlock

open Submission.Obl.k4_critical_conditional_row_preparation

attribute [local instance] ComparedBlock.instΓ ComparedBlock.instΛ

variable {α : Type} [MeasurableSpace α] {cfg : Data α} {k : ℕ} {s u v χ H : ℝ}

/-- The measurable coefficient field chosen by consensus on the fine state. -/
def consensusField (CB : ComparedBlock cfg k s u v χ H)
    (center : (Fin 4 → ℤ) → CB.Γ) (δ δU δX : ℝ) (p : α × ℝ) : Fin 2 → ℝ :=
  stateFieldValue CB.tc center δ (sigmaState CB.frame δ δU δX (cfg.b k p.1) p.2)

theorem measurable_consensusField (CB : ComparedBlock cfg k s u v χ H)
    (center : (Fin 4 → ℤ) → CB.Γ) (δ δU δX : ℝ) (hb : Measurable (cfg.b k)) :
    Measurable (CB.consensusField center δ δU δX) :=
  (measurable_stateFieldValue CB.tc center δ).comp (measurable_sigmaState CB.frame δ δU δX hb)

/-- **The common-field theorem at one original true block.** The only cap
inputs are a normalized base-cell ceiling and the original palette's interval
ceiling. All conditional palette bounds are inherited by coarsening the
consensus states; all affine menus come from the original chart lists. -/
theorem field_step (CB : ComparedBlock cfg k s u v χ H)
    {S C₀ A θF εF η δ δU δX eR R : ℝ}
    (hF : Field.FieldAt S C₀ A θF εF η (cfg.N k))
    (hN : 0 < cfg.N k) (hδ : δ = cfg.N k ^ (-(C₀ * (A + θF)))) (hδ1 : δ ≤ 1)
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hχq : χ / CB.frame.q ≤ 1)
    (hχA : cfg.N k ^ (-A) ≤ χ) (hχbA : cfg.N k ^ (-A) ≤ χ / CB.frame.q)
    (hK : 1 ≤ cfg.K k) (hKη : 3 * cfg.K k ≤ cfg.N k ^ η)
    (hHη : H * (5 + 3 * cfg.K k) ≤ cfg.N k ^ η)
    (hfitnum : eR + H * (δ + χ / CB.frame.q + χ) ≤ cfg.N k ^ η * cfg.N k ^ (-θF))
    [IsProbabilityMeasure (cfg.ν k)] [IsProbabilityMeasure (cfg.π k)]
    (hb : Measurable (cfg.b k)) (hB : BlocksAt cfg k s R)
    (hA0 : cfg.ν k (cfg.A k s CB.i) ≠ 0)
    (lam : Measure (α × ℝ)) (hlam : lam ≤ CB.lam)
    (hdom : lam ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume)
    (hvel : ∀ᵐ p ∂lam, |cfg.b k p.1 3| ≤ cfg.K k)
    (hmass : ENNReal.ofReal (cfg.N k ^ (-η)) *
      (ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)) ≤ lam univ)
    (center : (Fin 4 → ℤ) → CB.Γ)
    (hagree : ∀ᵐ p ∂lam,
      let Q := sigmaState CB.frame δ δU δX (cfg.b k p.1) p.2
      |lin1 (CB.tc (CB.crs (CB.lab p.1))) (stateCenter δ Q 0) (stateCenter δ Q 1) -
        lin1 (CB.tc (center Q)) (stateCenter δ Q 0) (stateCenter δ Q 1)| +
        |CB.tc (CB.crs (CB.lab p.1)) 3 - CB.tc (center Q) 3| < eR)
    (hstate : ∀ (Q : Fin 4 → ℤ) (V : Set ℤ),
      lam {p | sigmaState CB.frame δ δU δX (cfg.b k p.1) p.2 = Q ∧
        vbin δ (cfg.b k p.1 3) ∈ V} ≤
      ENNReal.ofReal (cfg.N k ^ η) *
        lam ((fun p : α × ℝ => sigmaState CB.frame δ δU δX (cfg.b k p.1) p.2) ⁻¹' {Q}) *
          paletteBins (cfg.π k) δ V)
    (hcell : ∀ Q : Fin 2 → ℤ,
      lam {p | ⌊CB.frame.zt p.2 / δ⌋ = Q 0 ∧ ⌊CB.frame.zZ (cfg.b k p.1) p.2 / δ⌋ = Q 1} ≤
        ENNReal.ofReal (cfg.N k ^ η * δ ^ 2) *
          (ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)))
    (hfrost : ∀ x r : ℝ, δ ≤ r → r ≤ 1 →
      cfg.π k (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (cfg.N k ^ η * r ^ S)) :
    ∃ C : Fin 4 → ℝ, (∀ e, |C e| ≤ cfg.N k ^ εF) ∧
      ENNReal.ofReal (cfg.N k ^ (-εF)) *
        (ENNReal.ofReal CB.frame.q * cfg.ν k (cfg.A k s CB.i)) ≤
      lam {p | |CB.consensusField center δ δU δX p 0 - C 0 - C 1 * CB.frame.zt p.2 -
          C 2 * CB.frame.zZ (cfg.b k p.1) p.2| ≤ cfg.N k ^ εF * cfg.N k ^ (-θF) ∧
        |CB.consensusField center δ δU δX p 1 - C 3| ≤ cfg.N k ^ εF * cfg.N k ^ (-θF)} := by
  classical
  have hδpos : 0 < δ := by rw [hδ]; exact Real.rpow_pos_of_pos hN _
  have hq : 0 < CB.frame.q := by dsimp [frame, blockFrame]; positivity
  have hH : 0 ≤ H := zero_le_one.trans CB.H_one
  have hK0 : 0 ≤ cfg.K k := zero_le_one.trans hK
  have hHK : 0 ≤ H * cfg.K k := mul_nonneg hH hK0
  let σ : α × ℝ → Fin 4 → ℤ := fun p => sigmaState CB.frame δ δU δX (cfg.b k p.1) p.2
  let f := CB.consensusField center δ δU δX
  have hσ : Measurable σ := measurable_sigmaState CB.frame δ δU δX hb
  have hf : Measurable f := CB.measurable_consensusField center δ δU δX hb
  have hσ0 (p : α × ℝ) : σ p 0 = ⌊CB.frame.zt p.2 / δ⌋ := rfl
  have hσ1 (p : α × ℝ) : σ p 1 = ⌊CB.frame.zZ (cfg.b k p.1) p.2 / δ⌋ := rfl
  have hac : lam ≪ CB.lam := Measure.absolutelyContinuous_of_le hlam
  have hsupp := hac.ae_le CB.lam_supp
  have hgood := hac.ae_le CB.ae_good
  have ht₀I : CB.frame.t₀ ∈ Data.I (cfg.T k s) (cfg.j k s CB.i) := by
    dsimp only [frame, blockFrame, Data.I, mem_Icc]
    exact ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) (by positivity)⟩
  have ht₀ : |CB.frame.t₀| ≤ 1 := by
    have ht := Submission.Obl.k4_scalar_initial_true_horizon.I_subset_unit
      (cfg.T k s) (cfg.j k s CB.i) ht₀I
    exact (abs_of_nonneg ht.1).trans_le ht.2
  have hc₁ : |CB.frame.c 1| ≤ cfg.K k := hB.c_bd CB.i 1
  have hgeom : ∀ᵐ p ∂lam,
      p.1 ∈ cfg.A k s CB.i ∧ p.2 ∈ Icc CB.frame.t₀ (CB.frame.t₀ + CB.frame.q) ∧
      |Field.normalizedIntercept CB.frame.t₀ CB.frame.q (CB.frame.c 0) (CB.frame.c 1)
        (cfg.b k p.1 0) (cfg.b k p.1 3)| ≤ cfg.K k ∧
      |cfg.b k p.1 3| ≤ cfg.K k ∧ |CB.frame.zt p.2| ≤ 1 ∧
      |CB.frame.zZ (cfg.b k p.1) p.2| ≤ cfg.K k := by
    filter_upwards [hsupp, hgood, hvel] with p hsp hgp hvp
    have hlA := (hB.sets CB.i).2.2 hsp.1
    have hG := (hB.geom CB.i p.1 hlA p.2 hgp.I).1
    have hG₀ := (hB.geom CB.i p.1 hlA CB.frame.t₀ ht₀I).1
    have hI : p.2 ∈ Icc CB.frame.t₀ (CB.frame.t₀ + CB.frame.q) := hsp.2
    refine ⟨hlA, hI, ?_, hvp, ?_, ?_⟩
    · change |(cfg.b k p.1 0 + CB.frame.t₀ * cfg.b k p.1 3 - CB.frame.c 0 -
          CB.frame.t₀ * CB.frame.c 1) / CB.frame.q| ≤ cfg.K k
      rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
      exact hG₀
    · rw [Frame.zt, abs_le]
      constructor
      · exact (div_nonneg (sub_nonneg.mpr hI.1) hq.le).trans' (by norm_num)
      · rw [div_le_iff₀ hq]; linarith [hI.2]
    · rw [Frame.zZ, abs_div, abs_of_pos hq, div_le_iff₀ hq]
      exact hG
  let L := Field.affineMenu CB.G CB.tc CB.frame.t₀ CB.frame.q (CB.frame.c 0)
    (CB.frame.c 1) χ H (cfg.K k)
  have hLcard : ∀ ch, ((L ch).card : ℝ) ≤ cfg.N k ^ η := by
    intro ch
    exact (Field.affineMenu_card CB.G CB.tc _ _ _ _ _ _ _ hH CB.G_card ch).trans
      (by nlinarith)
  have hLbd : ∀ ch, ∀ a ∈ L ch, ∀ e, |a e| ≤ cfg.N k ^ η := by
    intro ch a ha e
    exact (Field.affineMenu_bound CB.G CB.tc _ _ _ _ _ _ _ ch a ha e).trans (by nlinarith)
  have hfb : ∀ᵐ p ∂lam, ∀ e, |f p e| ≤ cfg.N k ^ η := by
    filter_upwards [hgeom] with p hp e
    have hh := stateFieldValue_bound CB.tc center hH hK CB.tc_bd hδpos hδ1 (σ p)
      (hσ0 p).symm (hσ1 p).symm hp.2.2.2.2.1 hp.2.2.2.2.2 e
    exact hh.trans (by nlinarith)
  have hfit : ∀ᵐ p ∂lam, ∃ a ∈ L
      (⌊Field.normalizedIntercept CB.frame.t₀ CB.frame.q (CB.frame.c 0) (CB.frame.c 1)
        (cfg.b k p.1 0) (cfg.b k p.1 3) / (χ / CB.frame.q)⌋, ⌊cfg.b k p.1 3 / χ⌋),
      |f p 0 - a 0 - a 1 * CB.frame.zt p.2| ≤ cfg.N k ^ η * cfg.N k ^ (-θF) ∧
        |f p 1 - a 2| ≤ cfg.N k ^ η * cfg.N k ^ (-θF) := by
    filter_upwards [hgeom, hgood, hagree] with p hp hg ha
    let γ := CB.crs (CB.lab p.1)
    let β := Field.normalizedIntercept CB.frame.t₀ CB.frame.q (CB.frame.c 0) (CB.frame.c 1)
      (cfg.b k p.1 0) (cfg.b k p.1 3)
    let a := Field.affineOption (CB.tc γ) ((χ / CB.frame.q) * (⌊β / (χ / CB.frame.q)⌋ : ℝ))
      (χ * (⌊cfg.b k p.1 3 / χ⌋ : ℝ)) (CB.frame.c 1)
    refine ⟨a, Field.mem_affineMenu CB.G CB.tc hq hχ ht₀ hH hK (CB.tc_bd γ)
      hp.2.2.1 hp.2.2.2.1 hc₁ hχq hχ1 hg.coarse, ?_, ?_⟩
    · have hnear := lin1_stateCenter_error hH (CB.tc_bd γ) hδpos (σ p) (hσ0 p).symm (hσ1 p).symm
      have hrep : |f p 0 - lin1 (CB.tc γ) (stateCenter δ (σ p) 0) (stateCenter δ (σ p) 1)| ≤ eR := by
        change |lin1 (CB.tc (center (σ p))) _ _ - lin1 (CB.tc γ) _ _| ≤ eR
        rw [abs_sub_comm]
        exact (le_add_of_nonneg_right (abs_nonneg _)).trans ha.le
      have hline : CB.frame.zZ (cfg.b k p.1) p.2 = β + CB.frame.zt p.2 * (cfg.b k p.1 3 - CB.frame.c 1) := by
        dsimp [β, Field.normalizedIntercept, Frame.zZ, Frame.zt]
        field_simp [hq.ne']
        ring
      have hmenu := Field.affineOption_fit (β := β) (v := cfg.b k p.1 3) (c₁ := CB.frame.c 1)
        hH (CB.tc_bd γ 2) (div_pos hχ hq) hχ hp.2.2.2.2.1
      have hmenu' : |lin1 (CB.tc γ) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) -
          a 0 - a 1 * CB.frame.zt p.2| ≤ H * (χ / CB.frame.q + χ) := by
        rw [hline]
        exact hmenu
      calc _ ≤ |f p 0 - lin1 (CB.tc γ) (stateCenter δ (σ p) 0) (stateCenter δ (σ p) 1)| +
          |lin1 (CB.tc γ) (stateCenter δ (σ p) 0) (stateCenter δ (σ p) 1) -
            lin1 (CB.tc γ) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2)| +
          |lin1 (CB.tc γ) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) - a 0 - a 1 * CB.frame.zt p.2| := by
            have hid : f p 0 - a 0 - a 1 * CB.frame.zt p.2 =
                (f p 0 - lin1 (CB.tc γ) (stateCenter δ (σ p) 0) (stateCenter δ (σ p) 1)) +
                (lin1 (CB.tc γ) (stateCenter δ (σ p) 0) (stateCenter δ (σ p) 1) -
                  lin1 (CB.tc γ) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2)) +
                (lin1 (CB.tc γ) (CB.frame.zt p.2) (CB.frame.zZ (cfg.b k p.1) p.2) - a 0 - a 1 * CB.frame.zt p.2) := by ring
            rw [hid]
            exact abs_add_three _ _ _
        _ ≤ eR + H * δ + H * (χ / CB.frame.q + χ) := by gcongr
        _ ≤ cfg.N k ^ η * cfg.N k ^ (-θF) := by nlinarith [hfitnum]
    · change |CB.tc (center (σ p)) 3 - CB.tc γ 3| ≤ _
      rw [abs_sub_comm]
      have hh : |CB.tc γ 3 - CB.tc (center (σ p)) 3| ≤ eR :=
        (le_add_of_nonneg_left (abs_nonneg _)).trans ha.le
      exact hh.trans (by nlinarith [mul_nonneg hH (by positivity : 0 ≤ δ + χ / CB.frame.q + χ)])
  have hstate' := stateField_palette lam σ hσ (fun p => cfg.b k p.1 3)
    (((measurable_pi_apply 3).comp hb).comp measurable_fst) (cfg.π k) CB.tc center hδpos hstate
      (e := cfg.N k ^ (-θF))
  apply Field.field_transport hF hN hδ rfl (cfg.ν k) (cfg.π k) (cfg.b k) hb
    (cfg.A k s CB.i) (hB.sets CB.i).1 hA0 CB.frame.t₀ CB.frame.q (CB.frame.c 0)
      (CB.frame.c 1) (χ / CB.frame.q) χ (cfg.K k) hq lam f hf L hχbA hχq hχA hχ1
  · linarith
  · linarith
  · exact hdom
  · filter_upwards [hgeom] with p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1.trans (by linarith), hp.2.2.2.1.trans (by linarith)⟩
  · exact hmass
  · exact hfb
  · exact hcell
  · exact hfrost
  · exact hstate'
  · exact hLcard
  · exact hLbd
  · exact hfit

end ComparedBlock

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Support
