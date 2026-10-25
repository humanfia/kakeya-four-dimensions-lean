/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Native/ShortCaps.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native.KeyCaps

set_option autoImplicit false

/-!
# Caps of block and piece entries over slot keys

Incidences of one slot key during the slot, with the hidden value near
* the affine graph of a true block (`block_key_cap`),
* a projected sheet (`sheet_key_cap`),
* a normalized key-coordinate graph `a · quad2 r` (`quad_key_cap`),
are charged to the frozen joint cap by `key_window_cap`.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native

open MeasureTheory Set Filter
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGML2D
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.CompareSheets
open Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Core

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Events of labels of key `κ` (at slot start `t₀`) in a label set `S`, during the slot, with
slice coordinate in `[x - w, x]`. -/
def keySliceEvents (b : α → Fin 6 → ℝ) (χ m t₀ q x w : ℝ) (κ : Fin 3 → ℤ) (S : Set α) :
    Set (α × ℝ) :=
  {p | p.1 ∈ S ∧ slotKey b χ m t₀ p.1 = κ ∧ p.2 ∈ Icc t₀ (t₀ + q) ∧
    sliceY b m t₀ p.1 ∈ Icc (x - w) x}

/-- The horizontal set of incidences. -/
def horizSet (b : α → Fin 6 → ℝ) (ζ : ℝ) : Set (α × ℝ) := {p | |b p.1 4 + b p.1 0| ≤ ζ}

theorem measurableSet_horizSet {b : α → Fin 6 → ℝ} (hb : Measurable b) (ζ : ℝ) :
    MeasurableSet (horizSet b ζ) := by
  have h0 : Measurable fun p : α × ℝ => b p.1 0 :=
    (measurable_pi_apply 0).comp (hb.comp measurable_fst)
  have h4 : Measurable fun p : α × ℝ => b p.1 4 :=
    (measurable_pi_apply 4).comp (hb.comp measurable_fst)
  exact measurableSet_le (h4.add h0).abs measurable_const

/-- **Block entries.** -/
theorem block_key_cap {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {N K d r s₁ v' : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hcap : JointCapAt μ π b N K d r s₁ v') (κ : Fin 3 → ℤ) {t₀ q m x w ζ Lv : ℝ}
    (hq : 0 < q) (hm : 0 < m) (hw : 0 ≤ w) (hζ : 0 ≤ ζ) (hLv : 0 ≤ Lv)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * N ^ (-v')| ≤ Lv) (hL1 : |(κ 1 : ℝ) * N ^ (-v')| ≤ Lv)
    (hdr : N ^ (-r) ≤ q / 2) (hdZ : N ^ (-r) ≤ 2 * N ^ (-v'))
    (hdY : N ^ (-r) ≤ m * w + q * (ζ + N ^ (-v')))
    (hmZ : Lv * N ^ (-r) ≤ 2 * N ^ (-v')) (hmY : Lv * N ^ (-r) ≤ m * w + q * (ζ + N ^ (-v')))
    (F : MvPolynomial (Fin 4) ℝ) (Lc : Fin 4 → ℝ) (hF : HorizontalForm F Lc) {Lb W : ℝ}
    (hLb : ∀ e, |Lc e| ≤ Lb) (hvar : 3 * Lb * N ^ (-r) ≤ N ^ (-s₁)) (hW : W ≤ N ^ (-s₁))
    (S : Set α) (hfit : ∀ p ∈ keySliceEvents b (N ^ (-v')) m t₀ q x w κ S,
      |MvPolynomial.eval ![p.2, b p.1 0 + p.2 * b p.1 3, b p.1 1 + p.2 * b p.1 4,
        b p.1 2 + p.2 * b p.1 5] F| ≤ W) :
    μ (keySliceEvents b (N ^ (-v')) m t₀ q x w κ S ∩ horizSet b ζ) ≤
      ENNReal.ofReal (12000 * K * q * N ^ (-v') * (m * w + q * (ζ + N ^ (-v'))) *
        (N ^ (-s₁)) ^ d) * π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
  apply key_window_cap hb hN hK hcap κ (fun y => blockGraph F (y 0) (y 1) (y 2)) _ hq hm hw hζ
    hLv hunit hL0 hL1 hdr hdZ hdY hmZ hmY
  · intro p _ y hy
    rw [blockGraph_eq hF, blockGraph_eq hF]
    have e : Lc 0 + Lc 1 * basePt b p 0 + Lc 2 * basePt b p 1 + Lc 3 * basePt b p 2 -
        (Lc 0 + Lc 1 * y 0 + Lc 2 * y 1 + Lc 3 * y 2) =
        Lc 1 * (basePt b p 0 - y 0) + Lc 2 * (basePt b p 1 - y 1) +
          Lc 3 * (basePt b p 2 - y 2) := by ring
    rw [e]
    have hB : 0 ≤ Lb := (abs_nonneg _).trans (hLb 0)
    have t1 : |Lc 1 * (basePt b p 0 - y 0)| ≤ Lb * N ^ (-r) := by
      rw [abs_mul]; exact mul_le_mul (hLb 1) (hy 0) (abs_nonneg _) hB
    have t2 : |Lc 2 * (basePt b p 1 - y 1)| ≤ Lb * N ^ (-r) := by
      rw [abs_mul]; exact mul_le_mul (hLb 2) (hy 1) (abs_nonneg _) hB
    have t3 : |Lc 3 * (basePt b p 2 - y 2)| ≤ Lb * N ^ (-r) := by
      rw [abs_mul]; exact mul_le_mul (hLb 3) (hy 2) (abs_nonneg _) hB
    calc _ ≤ |Lc 1 * (basePt b p 0 - y 0) + Lc 2 * (basePt b p 1 - y 1)| +
          |Lc 3 * (basePt b p 2 - y 2)| := abs_add_le _ _
      _ ≤ |Lc 1 * (basePt b p 0 - y 0)| + |Lc 2 * (basePt b p 1 - y 1)| +
          |Lc 3 * (basePt b p 2 - y 2)| := by gcongr; exact abs_add_le _ _
      _ ≤ 3 * Lb * N ^ (-r) := by linarith
      _ ≤ N ^ (-s₁) := hvar
  · rintro p ⟨hp, hh⟩
    obtain ⟨hS, hκ, ht, hy⟩ := hp
    refine ⟨hκ, ht, hy, hh, ?_⟩
    have := hfit p ⟨hS, hκ, ht, hy⟩
    rw [eval_horizontalForm hF] at this
    have e : (![p.2, b p.1 0 + p.2 * b p.1 3, b p.1 1 + p.2 * b p.1 4,
        b p.1 2 + p.2 * b p.1 5] : Fin 4 → ℝ) 3 = hidden b p := rfl
    rw [e] at this
    exact this.trans hW

/-- **Sheet entries.** A projected sheet `G` over the strip
`Y = y₀ + t v + D (4 η - 2)` with coefficients bounded by `H` there. -/
theorem sheet_key_cap {μ : Measure (α × ℝ)} {π : Measure ℝ} {b : α → Fin 6 → ℝ}
    (hb : Measurable b) {N K d r s₁ v' : ℝ} (hN : 0 < N) (hK : 0 ≤ K)
    (hcap : JointCapAt μ π b N K d r s₁ v') (κ : Fin 3 → ℤ) {t₀ q m x w ζ Lv : ℝ}
    (hq : 0 < q) (hm : 0 < m) (hw : 0 ≤ w) (hζ : 0 ≤ ζ) (hLv : 0 ≤ Lv)
    (hunit : 0 ≤ t₀ ∧ t₀ + q ≤ 1)
    (hL0 : |(κ 0 : ℝ) * N ^ (-v')| ≤ Lv) (hL1 : |(κ 1 : ℝ) * N ^ (-v')| ≤ Lv)
    (hdr : N ^ (-r) ≤ q / 2) (hdZ : N ^ (-r) ≤ 2 * N ^ (-v'))
    (hdY : N ^ (-r) ≤ m * w + q * (ζ + N ^ (-v')))
    (hmZ : Lv * N ^ (-r) ≤ 2 * N ^ (-v')) (hmY : Lv * N ^ (-r) ≤ m * w + q * (ζ + N ^ (-v')))
    (G : MvPolynomial (Fin 2) ℝ) (hG : G.totalDegree ≤ 2) {y₀ v D H W : ℝ} (hD : 0 < D)
    (hH : ∀ k', |sheetCoeff G y₀ v D k'| ≤ H)
    (hvar : H * (1 + 3 * 2) * (N ^ (-r) + (N ^ (-r) + |v| * N ^ (-r)) / (4 * D)) ≤ N ^ (-s₁))
    (hW : W ≤ N ^ (-s₁))
    (S : Set α)
    (hstrip : ∀ p ∈ keySliceEvents b (N ^ (-v')) m t₀ q x w κ S,
      |etaFun y₀ v D p.2 (b p.1 1 + p.2 * b p.1 4)| ≤ 2 - (N ^ (-r) + |v| * N ^ (-r)) / (4 * D))
    (hfit : ∀ p ∈ keySliceEvents b (N ^ (-v')) m t₀ q x w κ S,
      |hidden b p - MvPolynomial.eval ![p.2, b p.1 1 + p.2 * b p.1 4] G| ≤ W) :
    μ (keySliceEvents b (N ^ (-v')) m t₀ q x w κ S ∩ horizSet b ζ) ≤
      ENNReal.ofReal (12000 * K * q * N ^ (-v') * (m * w + q * (ζ + N ^ (-v'))) *
        (N ^ (-s₁)) ^ d) * π {w | ⌊w / N ^ (-v')⌋ = κ 0} := by
  apply key_window_cap hb hN hK hcap κ (fun y => quad2 (sheetCoeff G y₀ v D) (y 0)
    (etaFun y₀ v D (y 0) (y 2))) _ hq hm hw hζ hLv hunit hL0 hL1 hdr hdZ hdY hmZ hmY
  · rintro p ⟨hp, -⟩ y hy
    have hp0 : basePt b p 0 = p.2 := rfl
    have hp2 : basePt b p 2 = b p.1 1 + p.2 * b p.1 4 := rfl
    have ht := hp.2.2.1
    have ht01 : |p.2| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2, hunit.1, hunit.2]
    have hy0 := hy 0
    have hy2 := hy 2
    rw [hp0] at hy0
    have hdη := etaFun_sub (y₀ := y₀) (v := v) hD p.2 (basePt b p 2) (y 0) (y 2)
    have hdη' : |etaFun y₀ v D p.2 (basePt b p 2) - etaFun y₀ v D (y 0) (y 2)| ≤
        (N ^ (-r) + |v| * N ^ (-r)) / (4 * D) := by
      refine hdη.trans (div_le_div_of_nonneg_right ?_ (by positivity))
      have := mul_le_mul_of_nonneg_left (show |p.2 - y 0| ≤ N ^ (-r) from hy0) (abs_nonneg v)
      linarith
    have hη := hstrip p hp
    rw [← hp2] at hη
    have hr0 : 0 ≤ N ^ (-r) := (Real.rpow_pos_of_pos hN _).le
    have hη2 : |etaFun y₀ v D (y 0) (y 2)| ≤ 2 := by
      rw [abs_le] at hdη' hη ⊢
      constructor <;> linarith [hdη'.1, hdη'.2, hη.1, hη.2]
    have hη2' : |etaFun y₀ v D p.2 (basePt b p 2)| ≤ 2 := by
      have : 0 ≤ (N ^ (-r) + |v| * N ^ (-r)) / (4 * D) := by positivity
      linarith
    have hy0' : |y 0| ≤ 2 := by
      rw [abs_le] at hy0 ht01 ⊢
      have : N ^ (-r) ≤ 1 := by linarith [hdr, hunit.2, hq]
      constructor <;> linarith
    have hlip := quad2_lipschitz (L := 2) hH (t := p.2) (t' := y 0)
      (η := etaFun y₀ v D p.2 (basePt b p 2)) (η' := etaFun y₀ v D (y 0) (y 2))
      (by linarith) hy0' hη2' hη2
    rw [hp0]
    refine hlip.trans (le_trans ?_ hvar)
    have hH0 : 0 ≤ H := (abs_nonneg _).trans (hH 0)
    gcongr
  · rintro p ⟨hp, hh⟩
    refine ⟨hp.2.1, hp.2.2.1, hp.2.2.2, hh, ?_⟩
    have hval : MvPolynomial.eval ![p.2, b p.1 1 + p.2 * b p.1 4] G =
        quad2 (sheetCoeff G y₀ v D) (basePt b p 0) (etaFun y₀ v D (basePt b p 0) (basePt b p 2)) := by
      rw [quad2_sheetCoeff_etaFun hG hD.ne']
      rfl
    rw [← hval]
    exact (hfit p hp).trans hW

end

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Native
