/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/HeavyPacket.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_scalar_heavy_intercept_selection.AssignedArea
import Submission.Obl.k4_scalar_heavy_intercept_selection.BaseCap
import Submission.Obl.k4_scalar_heavy_intercept_selection.HeavyFamily
import Submission.Obl.k4_scalar_heavy_intercept_selection.PotentialBins

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Set MeasureTheory
open Submission.Lib.K4ContinuousKakeya

noncomputable section

def finePhysicalCode {Ω : Type*} (b : ℝ) (phys : Ω → Fin 3 → ℝ) : Ω → Fin 3 → ℤ :=
  fun p j => ⌊phys p j / b⌋

def normalizedPhysicalBase {Ω : Type*} (h : ℝ) (z : Fin 2 → ℝ)
    (phys : Ω → Fin 3 → ℝ) : Ω → Fin 2 → ℝ :=
  fun p i => (phys p i.castSucc - z i) / h

def jointPhysicalCode {Ω : Type*} (h ξ w : ℝ) (z : Fin 2 → ℝ)
    (phys : Ω → Fin 3 → ℝ) : Ω → (Fin 2 → ℤ) × ℤ :=
  fun p => ((fun i => ⌊normalizedPhysicalBase h z phys p i / ξ⌋), ⌊phys p 2 / w⌋)

/-- The finite packet selection after a common potential and bounded
line intercept are known. The selected measure is an actual restriction
of the original incidence law. Its original fine-state palette ceilings
are consequently inherited through `retained_group_event_cap`. -/
theorem select_heavy_packet {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν]
    (μ : Measure (α × ℝ)) [IsFiniteMeasure μ]
    (K : NNReal) (hK : 1 ≤ K) {C h b ξ η w ε V R : ℝ}
    (hC : 0 < C) (hMK : FiniteMK 2 C) (hh : 0 < h) (hb : 0 < b)
    (hξ : 0 < ξ) (hξ₁ : ξ ≤ 1) (hη : 0 < η) (hw : 0 < w) (hR : 0 < R)
    (hbξ : b ≤ h * ξ) (hε : ε ≤ w) (herror : b + V + 2 * ε ≤ w)
    (hν : 0 < (ν univ).toReal)
    (hdom : μ ≤ K • ν.prod volume)
    (hmass : h * (ν univ).toReal / (K : ℝ) ≤ (μ univ).toReal)
    (u v : α → ℝ) (hu : Measurable u) (hv : Measurable v)
    (hbu : ∀ l, |u l| ≤ (K : ℝ)) (hbv : ∀ l, |v l| ≤ (K : ℝ))
    (Λ : Set α) (hΛ : MeasurableSet Λ) (hΛμ : ∀ᵐ p ∂μ, p.1 ∈ Λ)
    (z : Fin 2 → ℝ) (phys : α × ℝ → Fin 3 → ℝ) (hphys : Measurable phys)
    (hTime : ∀ p, phys p 0 = p.2)
    (hBase : ∀ p, p.1 ∈ Λ → normalizedPhysicalBase h z phys p =
      ![(p.2 - z 0) / h, u p.1 + ((p.2 - z 0) / h) * v p.1])
    (c : α → ℝ) (hc : Measurable c) (hbc : ∀ l, |c l| ≤ (K : ℝ))
    (f : (Fin 2 → ℝ) → ℝ) (S : Set (α × ℝ)) (hS : ∀ᵐ p ∂μ, p ∈ S)
    (hbox : ∀ p ∈ S, ∀ i, |normalizedPhysicalBase h z phys p i| ≤ (K : ℝ))
    (hfit : ∀ p ∈ S, |phys p 2 - f (normalizedPhysicalBase h z phys p) - c p.1| ≤ ε)
    (hFine : ∀ p ∈ S, ∀ p' ∈ S, finePhysicalCode b phys p = finePhysicalCode b phys p' →
      |f (normalizedPhysicalBase h z phys p) - f (normalizedPhysicalBase h z phys p')| ≤ V)
    (hCoarse : ∀ p ∈ S, ∀ p' ∈ S,
      (fun i => (⌊normalizedPhysicalBase h z phys p i / ξ⌋ : ℤ)) =
        (fun i => (⌊normalizedPhysicalBase h z phys p' i / ξ⌋ : ℤ)) →
      |f (normalizedPhysicalBase h z phys p) - f (normalizedPhysicalBase h z phys p')| ≤ w)
    (hPencil : ∀ q w₀,
      μ {p | finePhysicalCode b phys p = q ∧ |v p.1 - w₀| < η} ≤
        ENNReal.ofReal (1 / 2000 : ℝ) * μ ((finePhysicalCode b phys) ⁻¹' {q}))
    (J : Finset ((Fin 2 → ℤ) × ℤ))
    (hJ : ∀ᵐ p ∂μ, jointPhysicalCode h ξ w z phys p ∈ J)
    (hJcard : (J.card : ℝ) ≤ (K : ℝ) / ξ ^ 2 * R) :
    ∃ lists : (Fin 3 → ℤ) → Finset ℤ,
      (∀ q, ((lists q).card : ENNReal) ≤ 7) ∧
      (∀ q g, g ∉ lists q → μ {p | finePhysicalCode b phys p = q ∧
        (⌊c p.1 / w⌋ : ℤ) = g} = 0) ∧
      ∃ g : ℤ,
        let σ := retainedGroup μ (finePhysicalCode b phys)
          (fun p => (⌊c p.1 / w⌋ : ℤ)) lists (ENNReal.ofReal (1 / 1000 : ℝ)) g
        σ ≤ μ ∧
        ENNReal.ofReal (h * (ν univ).toReal * (η / ((K : ℝ) + 1) ^ 2) /
          (13478400 * C * (K : ℝ) ^ 6 * R)) ≤ σ univ ∧
        (∀ᵐ p ∂σ, (⌊c p.1 / w⌋ : ℤ) = g) := by
  classical
  let state := finePhysicalCode b phys
  let group : α → ℤ := fun l => ⌊c l / w⌋
  let base := normalizedPhysicalBase h z phys
  let joint := jointPhysicalCode h ξ w z phys
  let assigned : α × ℝ → Fin 2 → ℤ :=
    fun p => assignedBaseCode h b ξ z (state p)
  let δ := ENNReal.ofReal (1 / 1000 : ℝ)
  have hs : Measurable state := by
    change Measurable (fun p : α × ℝ => fun j : Fin 3 => (⌊phys p j / b⌋ : ℤ))
    fun_prop
  have hg : Measurable group := by dsimp [group]; fun_prop
  have ha : Measurable assigned := (measurable_assignedBaseCode h b ξ z).comp hs
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast zero_lt_one.trans_le hK
  have hK₁ : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hδ₀ : δ ≠ 0 := by dsimp [δ]; norm_num
  have hδtop : δ ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨lists, hlists, hmem⟩ := fine_cell_intercept_lists S phys (fun p => c p.1)
    (fun p => f (base p)) hb hw herror hfit hFine
  have hlist : ∀ q, ((lists q).card : ENNReal) ≤ 7 := by
    intro q
    exact_mod_cast hlists q
  have hsupport := state_group_support_of_ae_list μ state (fun p => group p.1) lists
    (hS.mono (fun p hp => hmem p hp))
  let σ : ℤ → Measure (α × ℝ) :=
    fun g => retainedGroup μ state (fun p => group p.1) lists δ g
  letI (g : ℤ) : IsFiniteMeasure (σ g) := by
    dsimp only [σ, retainedGroup]
    infer_instance
  have hσμ (g : ℤ) : σ g ≤ μ :=
    Measure.restrict_le_self.trans Measure.restrict_le_self
  have hσgroup (g : ℤ) : ∀ᵐ p ∂σ g, group p.1 = g :=
    ae_restrict_mem ((hg.comp measurable_fst) (measurableSet_singleton g))
  let G := Finset.Icc ⌊-(K : ℝ) / w⌋ ⌊(K : ℝ) / w⌋
  have hglobal : ∀ᵐ p ∂μ, group p.1 ∈ G :=
    Filter.Eventually.of_forall (fun p => intercept_bin_mem_finite_window hw (hbc p.1))
  let Fbox := assignedBaseWindow ξ (K : ℝ)
  have hcarrier : ∀ᵐ p ∂μ, assigned p ∈ Fbox := by
    filter_upwards [hS] with p hp
    exact assigned_code_mem_window hh hb hξ hξ₁ hbξ z (phys p) (hbox p hp)
  let cells : ℤ → Finset (Fin 2 → ℤ) :=
    fun g => positiveCodeWindow (σ g) assigned Fbox
  have hcells (g : ℤ) : ∀ᵐ p ∂σ g, assigned p ∈ cells g :=
    ae_mem_positiveCodeWindow μ (σ g) (hσμ g) assigned ha Fbox hcarrier
  have hcoarsePencil (g : ℤ) (q : Fin 2 → ℤ) (w₀ : ℝ) :
      σ g {p | assigned p = q ∧ |v p.1 - w₀| < η} ≤
        ENNReal.ofReal (1 / 2 : ℝ) * σ g (assigned ⁻¹' {q}) := by
    have hfine (r : Fin 3 → ℤ) :
        σ g {p | state p = r ∧ |v p.1 - w₀| < η} ≤
          ENNReal.ofReal (1 / 2 : ℝ) * σ g (state ⁻¹' {r}) := by
      have ht := retained_group_event_cap μ state hs (fun p => group p.1)
        (hg.comp measurable_fst) lists δ (ENNReal.ofReal (1 / 2000 : ℝ)) 1
        hδ₀ hδtop hsupport {p | |v p.1 - w₀| < η} r g
        (by simpa only [state, mem_ofPred_eq, mul_one] using hPencil r w₀)
      have heq : ENNReal.ofReal (1 / 2000 : ℝ) / δ = ENNReal.ofReal (1 / 2 : ℝ) := by
        dsimp [δ]
        rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 1 / 1000)]
        congr 1 <;> norm_num
      simpa only [σ, mem_ofPred_eq, heq, mul_one] using ht
    exact state_union_event_cap (σ g) state hs {p | |v p.1 - w₀| < η}
      (ENNReal.ofReal (1 / 2 : ℝ)) hfine
      {r | assignedBaseCode h b ξ z r = q}
  have hfloor (g : ℤ) (hgG : g ∈ G) (hm : 0 < (σ g univ).toReal)
      (heff : h / (4 * (K : ℝ)) * (ν (group ⁻¹' {g})).toReal ≤ (σ g univ).toReal) :
      (η / ((K : ℝ) + 1) ^ 2) / (28800 * C * (K : ℝ) ^ 4 * ξ ^ 2) ≤
        (cells g).card := by
    have hprior : ((ν.restrict (group ⁻¹' {g})) univ).toReal ≤
        (4 * (K : ℝ) / h) * (σ g univ).toReal := by
      rw [Measure.restrict_apply_univ]
      calc
        _ ≤ (σ g univ).toReal / (h / (4 * (K : ℝ))) :=
          (le_div_iff₀ (by positivity : 0 < h / (4 * (K : ℝ)))).2
            (by simpa only [mul_comm] using heff)
        _ = _ := by field_simp [hh.ne', hK₀.ne'] <;> ring
    have hdomg := retained_group_prior_domination ν μ (K : ENNReal) state group hg lists δ g hdom
    exact assigned_group_area_floor (ν.restrict (group ⁻¹' {g})) (σ g) K hK hC hMK
      hh hb hξ hη hbξ u v hu hv hbu hbv Λ hΛ (ae_mono (hσμ g) hΛμ)
      z phys hphys hTime hBase hdomg hprior hm (cells g) (hcells g)
      (fun q hq w₀ => hcoarsePencil g q w₀)
  obtain ⟨allowed, hallowed, hallowedmem⟩ := joint_cell_intercept_lists S base
    (fun p => phys p 2) (fun p => c p.1) f hξ hw hε hfit hCoarse
  have hbudget : (∑ g ∈ G, ((cells g).card : ℝ)) ≤ 117 * (K : ℝ) / ξ ^ 2 * R := by
    have hgood : ∀ᵐ p ∂μ, joint p ∈ J ∧ group p.1 ∈ allowed (joint p) ∧
        ∃ o ∈ baseAssignmentOffsets, assigned p = (joint p).1 + o := by
      filter_upwards [hJ, hS] with p hpJ hpS
      exact ⟨hpJ, hallowedmem p hpS, assigned_code_has_small_offset hh hb hξ hbξ z (phys p)⟩
    have ht := measured_group_cell_budget μ σ G cells J baseAssignmentOffsets
      (fun p => group p.1) assigned joint allowed (fun j o => j.1 + o)
      (fun j hj => hallowed j) (fun g hg => hσμ g) (fun g hg => hσgroup g) hgood
      (fun g hg q hq => (Finset.mem_filter.mp hq).2)
    calc
      _ ≤ (J.card : ℝ) * 9 * 13 := by
        simpa only [card_baseAssignmentOffsets, Nat.cast_ofNat] using ht
      _ ≤ ((K : ℝ) / ξ ^ 2 * R) * 9 * 13 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hJcard (by norm_num)) (by norm_num)
      _ = _ := by ring
  obtain ⟨g, hgG, hmg, heff, hheavy, hle⟩ := select_heavy_original_group ν μ state hs
    group hg lists hlist G hglobal cells hK₁ hC hξ hh hR
    (by positivity : 0 < η / ((K : ℝ) + 1) ^ 2) hν hmass hfloor hbudget
  exact ⟨lists, hlist, hsupport, g, hle, hheavy, hσgroup g⟩

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
