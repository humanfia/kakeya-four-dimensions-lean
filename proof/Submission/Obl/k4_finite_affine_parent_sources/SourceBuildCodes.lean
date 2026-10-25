-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0812 f7bed5fb, x0891 a669339c, x0923 e8a77b3e, x0807 989bea46 (SourceParentPalette: x0812's version); namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildPieces
import Submission.Obl.k4_finite_affine_parent_sources.PathBaseLocalization
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionJoint

/-!
# End labels of the window parent and their state codes

Below the window parent `b₀`, the end labels `h` of a deeper level `e` whose retained mass is
below the no-candidate floor `N^(-ρ h L - ε) packet(h)` are deleted (their packets fill at most
the parent's packet). Every other end label is localized in base, both in the frame of its
ancestor `Q` at the intermediate level `q` and in the parent's frame (x0923's
`labelFrame_original_descendant_base_diameter`, which uses that no mixed candidate exists).
With the oscillation groups of `Q` (`q_level_groups`), the incidences of one end label then
carry at most `81 K` state codes in the parent's frame (`piece_state_codes`):
`end_state_codes`.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_finite_forest_width_selection
open Submission.Obl.k4_stable_native_signal_oscillation Submission.Lib.K4XInterface
open scoped Classical

noncomputable section

local instance optMeasBC (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingBC (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The original packet of a label is its time block times its assignment. -/
theorem packet_measure (b : Fin p.C) :
    ((ν (p.world b)).prod volume) (p.packet b) =
      ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) * ν (p.world b) (p.assigned b) := by
  rw [PathData.packet, Measure.prod_prod, Real.volume_Icc, mul_comm]
  congr 2
  rw [← sub_div]
  ring

/-- **End labels of the window parent and their state codes.** -/
theorem end_state_codes (hν : ∀ w, IsProbabilityMeasure (ν w)) (hNk : 1 < Nk)
    {Mc : ℕ} {d₁ ρ gain ε : ℝ} {Hres : Fin W → Set Incidence}
    (hno : ¬MixedCandidate Nk L W ν B Mc d₁ ρ gain ε p.r p.T p.C p.lev p.world p.bin
      p.velocity p.frame p.assigned Hres)
    (b₀ : Fin p.C) (q e : ℕ) (hq : p.lev b₀ ≤ q) (hqe : q ≤ e) (hem : e ≤ m - 1)
    (hB : 0 < B (p.world b₀))
    (S1' : Set Incidence) (hS1'm : MeasurableSet S1') (hS1'H : S1' ⊆ Hres (p.world b₀))
    (hS1' : ∀ x ∈ S1', p.history m (p.lev b₀) (p.world b₀, x) = some b₀ ∧
      x ∈ TerminalInc W p.C m p.lev p.world p.counted (p.world b₀))
    {nG : Fin p.C → ℕ} (G : (Q : Fin p.C) → Fin (nG Q) → Set Incidence) {Kc M a : ℝ}
    (hnG : ∀ Q, (nG Q : ℝ) ≤ Kc)
    (hcov : ∀ x ∈ S1', ∀ Q, p.history m q (p.world b₀, x) = some Q → ∃ i, x ∈ G Q i)
    (hsig : ∀ Q i x y, x ∈ G Q i → y ∈ G Q i →
      |(δ Nk (p.r (p.lev b₀)))⁻¹ * eval (gx x.1 x.2) (p.test b₀) -
        (δ Nk (p.r (p.lev b₀)))⁻¹ * eval (gx y.1 y.2) (p.test b₀)| ≤
      M * (a + ‖nativeBase (framePoint (labelFrame p Q (B (p.world b₀))
          (δ Nk (p.r (p.lev b₀)))) x) -
        nativeBase (framePoint (labelFrame p Q (B (p.world b₀))
          (δ Nk (p.r (p.lev b₀)))) y)‖))
    {hl Hx mesh : ℝ} (hgain : gain ≤ hl) (hupper : hl ≤ 1 / 8)
    (hroom : p.r e + 2 * hl * L ≤ L) (hbias : 2 * p.κ ≤ Nk ^ Mc)
    (hH : 1 ≤ Hx) (hκH : 6 * p.κ ≤ Hx)
    (hrow : 12 * p.κ / (Nk ^ (ρ * hl * L + ε) * Nk ^ (-hl * L)) ≤ Hx)
    (hmesh : 0 < mesh) (hM : 0 ≤ M)
    (hd' : 16 * Hx ^ 4 * (((2 : ℝ) ^ p.T e)⁻¹ / ((2 : ℝ) ^ p.T (p.lev b₀))⁻¹) ≤ mesh)
    (hsmall : M * (a + 16 * Hx ^ 4 * (((2 : ℝ) ^ p.T e)⁻¹ / ((2 : ℝ) ^ p.T q)⁻¹)) +
      16 * Hx ^ 4 * (((2 : ℝ) ^ p.T e)⁻¹ / ((2 : ℝ) ^ p.T (p.lev b₀))⁻¹) ≤ mesh) :
    ∃ S2 : Set Incidence, MeasurableSet S2 ∧ S2 ⊆ S1' ∧
      ((ν (p.world b₀)).prod volume) (S1' \ S2) ≤
        ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε)) *
          ((ν (p.world b₀)).prod volume) (p.packet b₀) ∧
      ∀ hopt : Option (Fin p.C), ∃ V : Finset (Fin 4 → ℤ), (V.card : ℝ) ≤ 81 * Kc ∧
        ∀ x ∈ S2, p.history m e (p.world b₀, x) = hopt →
          stateCode (frameBase (labelFrame p b₀ (B (p.world b₀)) (δ Nk (p.r (p.lev b₀)))))
            (frameSignal (labelFrame p b₀ (B (p.world b₀)) (δ Nk (p.r (p.lev b₀))))
              ((labelFrame p b₀ (B (p.world b₀)) (δ Nk (p.r (p.lev b₀)))).normTest
                (δ Nk (p.r (p.lev b₀))) (p.test b₀))) mesh x ∈ V := by
  set w₀ := p.world b₀ with hw₀
  set δp := δ Nk (p.r (p.lev b₀)) with hδp
  have hNk0 : 0 < Nk := by linarith
  have hδ (r : ℝ) : 0 < δ Nk r := lt_of_lt_of_le (Real.rpow_pos_of_pos hNk0 _) (δ_bounds hNk r).1
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  have hhm : ∀ h, MeasurableSet {x : Incidence | p.history m e (w₀, x) = some h} := fun h =>
    (hp.measurable_history _).comp measurable_prodMk_left (measurableSet_singleton _)
  set Sh : Fin p.C → Set Incidence := fun h => S1' ∩ {x | p.history m e (w₀, x) = some h}
    with hSh
  have hrel : ∀ h, (Sh h).Nonempty → p.lev h = e ∧
      forestAncestor p.lev p.par h (p.lev b₀) = b₀ ∧ p.world h = w₀ ∧ Sh h ⊆ p.counted h := by
    intro h ⟨x, hx⟩
    obtain ⟨h1, h2, h3, -⟩ := history_below hp (hq.trans hqe) hem (hS1' x hx.1).1 hx.2
    refine ⟨h1, h2, h3, fun y hy => ?_⟩
    exact (history_below hp (hq.trans hqe) hem (hS1' y hy.1).1 hy.2).2.2.2
  -- heavy end labels
  let heavy : Fin p.C → Prop := fun h =>
    ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε)) * ((ν w₀).prod volume) (p.packet h) ≤
      ((ν w₀).prod volume) (Sh h)
  set S2 : Set Incidence := S1' ∩ ⋂ h, ({x | p.history m e (w₀, x) = some h}ᶜ ∪
    (if heavy h then univ else ∅)) with hS2
  have hS2m : MeasurableSet S2 := by
    refine hS1'm.inter (MeasurableSet.iInter fun h => (hhm h).compl.union ?_)
    split_ifs
    · exact MeasurableSet.univ
    · exact MeasurableSet.empty
  have hS2heavy : ∀ x ∈ S2, ∀ h, p.history m e (w₀, x) = some h → heavy h := by
    intro x hx h hh
    rcases mem_iInter.mp hx.2 h with h1 | h1
    · exact absurd hh h1
    · by_contra hn
      rw [if_neg hn] at h1
      exact h1
  refine ⟨S2, hS2m, inter_subset_left, ?_, ?_⟩
  · -- the light end labels
    have hcover : S1' \ S2 ⊆ ⋃ h, (if heavy h then ∅ else Sh h) := by
      intro x hx
      have hnot : ¬ ∀ h, x ∈ ({x | p.history m e (w₀, x) = some h}ᶜ ∪
          (if heavy h then univ else ∅)) := by
        intro hall
        exact hx.2 ⟨hx.1, mem_iInter.mpr hall⟩
      push Not at hnot
      obtain ⟨h, hh⟩ := hnot
      simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hh
      refine mem_iUnion.mpr ⟨h, ?_⟩
      by_cases hhv : heavy h
      · rw [if_pos hhv] at hh; exact absurd (mem_univ x) hh.2
      · rw [if_neg hhv]; exact ⟨hx.1, hh.1⟩
    have hlight : ∀ h, ((ν w₀).prod volume) (if heavy h then ∅ else Sh h) ≤
        if p.lev h = e ∧ p.lev b₀ ≤ p.lev h ∧ forestAncestor p.lev p.par h (p.lev b₀) = b₀
        then ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε)) * ((ν w₀).prod volume) (p.packet h)
        else 0 := by
      intro h
      by_cases hhv : heavy h
      · rw [if_pos hhv, measure_empty]; exact bot_le
      · rw [if_neg hhv]
        by_cases hne : (Sh h).Nonempty
        · obtain ⟨hlevh, hdesc, -, -⟩ := hrel h hne
          rw [if_pos ⟨hlevh, hlevh ▸ (hq.trans hqe), hdesc⟩]
          exact (not_le.mp hhv).le
        · rw [not_nonempty_iff_eq_empty.mp hne, measure_empty]; exact bot_le
    calc ((ν w₀).prod volume) (S1' \ S2)
        ≤ ((ν w₀).prod volume) (⋃ h, (if heavy h then ∅ else Sh h)) := measure_mono hcover
      _ ≤ ∑ h, ((ν w₀).prod volume) (if heavy h then ∅ else Sh h) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ h, (if p.lev h = e ∧ p.lev b₀ ≤ p.lev h ∧
            forestAncestor p.lev p.par h (p.lev b₀) = b₀
          then ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε)) * ((ν w₀).prod volume) (p.packet h)
          else 0) := Finset.sum_le_sum fun h _ => hlight h
      _ = ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε)) * ∑ h ∈ Finset.univ.filter (fun h =>
            p.lev h = e ∧ p.lev b₀ ≤ p.lev h ∧ forestAncestor p.lev p.par h (p.lev b₀) = b₀),
            ((ν w₀).prod volume) (p.packet h) := by
          rw [Finset.mul_sum, Finset.sum_filter]
      _ ≤ _ := by gcongr; exact desc_packets_le hp b₀ e
  · -- the state codes of one end history
    intro hopt
    have hKc0 : 0 ≤ Kc := le_trans (Nat.cast_nonneg _) (hnG b₀)
    cases hopt with
    | none =>
      refine ⟨∅, by simp only [Finset.card_empty, CharP.cast_eq_zero]; positivity,
        fun x hx hh => ?_⟩
      exact absurd hh (history_ne_none (y := (w₀, x)) (hS1' x hx.1).2)
    | some h =>
      by_cases hne : (S2 ∩ {x | p.history m e (w₀, x) = some h}).Nonempty
      · obtain ⟨x₀, hx₀⟩ := hne
        have hSh0 : (Sh h).Nonempty := ⟨x₀, hx₀.1.1, hx₀.2⟩
        obtain ⟨hlevh, hdesc, hwh, hsub⟩ := hrel h hSh0
        have hheavy := hS2heavy x₀ hx₀.1 h hx₀.2
        set Q := forestAncestor p.lev p.par h q with hQ
        have hlevQ : p.lev Q = q :=
          forestAncestor_level (fun b hb => (hp.parent b hb).1) h q (by omega)
        have hdescQ : forestAncestor p.lev p.par h (p.lev Q) = Q := by rw [hlevQ]
        -- the hypotheses of the base localization
        have hdetQ : 0 < |(p.frame h).det| := abs_pos.mpr (hp.chart h).1
        have hprior : 0 < ν (p.world h) (p.assigned h) :=
          lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by
            have := hp.one_le_slack; positivity)) (label_prior_floor hp hNk0 h)
        have hfloor : ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε) / (2 : ℝ) ^ p.T (p.lev h)) *
            ν (p.world h) (p.assigned h) ≤ (ν (p.world h)).prod volume (Sh h) := by
          have hpk := packet_measure hp h
          rw [hwh] at hpk ⊢
          calc ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε) / (2 : ℝ) ^ p.T (p.lev h)) *
                ν w₀ (p.assigned h)
              = ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε)) *
                  (ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev h))⁻¹) * ν w₀ (p.assigned h)) := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv]
            _ = ENNReal.ofReal (Nk ^ (-ρ * hl * L - ε)) * ((ν w₀).prod volume) (p.packet h) := by
                rw [hpk]
            _ ≤ _ := hheavy
        have hV : ∀ z ∈ Sh h, z ∈ Hres (p.world h) ∧ z.1 ∈ p.assigned h ∧
            z.2 ∈ Icc ((p.bin h : ℝ) / (2 : ℝ) ^ p.T (p.lev h))
              (((p.bin h : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev h)) := by
          intro z hz
          have hcs := hp.counted_support h z (hsub hz)
          exact ⟨by rw [hwh]; exact hS1'H hz.1, hcs.2.1, hcs.2.2.1⟩
        have hroom' : p.r (p.lev h) + 2 * hl * L ≤ L := by rw [hlevh]; exact hroom
        have hlocQ := labelFrame_original_descendant_base_diameter hp hNk0 Mc d₁ ρ gain ε Hres
          hno Q h (by rw [hlevQ, hlevh]; exact hqe) hdescQ (B w₀) δp hl Hx hgain hupper hroom'
          hprior hbias (Sh h) hSh0 hV hfloor hH hκH hrow
        have hlocP := labelFrame_original_descendant_base_diameter hp hNk0 Mc d₁ ρ gain ε Hres
          hno b₀ h (by rw [hlevh]; exact hq.trans hqe) hdesc (B w₀) δp hl Hx hgain hupper hroom'
          hprior hbias (Sh h) hSh0 hV hfloor hH hκH hrow
        rw [hlevh, hlevQ] at hlocQ
        rw [hlevh] at hlocP
        -- the piece of the end label
        set F : Set Incidence := S2 ∩ {x | p.history m e (w₀, x) = some h} with hF
        have hFpk : ∀ x ∈ F, x ∈ p.packet h := by
          intro x hx
          have hcs := hp.counted_support h x (hsub ⟨hx.1.1, hx.2⟩)
          exact ⟨hcs.2.1, hcs.2.2.1⟩
        have hqP := labelFrame_q_pos hp b₀ (B w₀) δp
        have hDP := labelFrame_det hp b₀ (B w₀) δp
        have hscP : (labelFrame p b₀ (B w₀) δp).sc ≠ 0 := by
          rw [labelFrame_sc]; exact (div_pos hB (hδ _)).ne'
        have hsignal : ∀ i x, x ∈ G Q i → ∀ y, y ∈ G Q i →
            |frameSignal (labelFrame p b₀ (B w₀) δp)
                ((labelFrame p b₀ (B w₀) δp).normTest δp (p.test b₀)) x -
              frameSignal (labelFrame p b₀ (B w₀) δp)
                ((labelFrame p b₀ (B w₀) δp).normTest δp (p.test b₀)) y| ≤
            M * (a + ‖nativeBase (framePoint (labelFrame p Q (B w₀) δp) x) -
              nativeBase (framePoint (labelFrame p Q (B w₀) δp) y)‖) := by
          intro i x hx y hy
          rw [frameSignal, frameSignal,
            value_normTest_framePoint _ hqP hDP hscP, value_normTest_framePoint _ hqP hDP hscP]
          exact hsig Q i x y hx hy
        have hd0 : 0 ≤ 16 * Hx ^ 4 * (((2 : ℝ) ^ p.T e)⁻¹ / ((2 : ℝ) ^ p.T q)⁻¹) := by
          positivity
        obtain ⟨V, hVcard, hVmem⟩ := piece_state_codes
          (fun x => nativeBase (framePoint (labelFrame p Q (B w₀) δp) x))
          (frameBase (labelFrame p b₀ (B w₀) δp))
          (frameSignal (labelFrame p b₀ (B w₀) δp)
            ((labelFrame p b₀ (B w₀) δp).normTest δp (p.test b₀)))
          (G Q) F mesh M a _ _ hmesh hM hd0 hd' hsmall
          (fun x hx y hy => hlocQ x y (hFpk x hx) (hFpk y hy))
          (fun x hx y hy => hlocP x y (hFpk x hx) (hFpk y hy)) hsignal
        refine ⟨V, ?_, fun x hx hh => hVmem x ⟨hx, hh⟩ ?_⟩
        · calc (V.card : ℝ) ≤ ((81 * nG Q : ℕ) : ℝ) := by exact_mod_cast hVcard
            _ = 81 * (nG Q : ℝ) := by push_cast; ring
            _ ≤ 81 * Kc := by gcongr; exact hnG Q
        · have href := history_refines' hp hqe (w₀, x)
          rw [hh] at href
          simp only [PathData.ancestorCode, Option.map_some] at href
          exact hcov x hx.1 Q href
      · refine ⟨∅, by simp only [Finset.card_empty, CharP.cast_eq_zero]; positivity,
          fun x hx hh => absurd ⟨x, hx, hh⟩ hne⟩

end

end

end Submission.Obl.k4_finite_affine_parent_sources
