-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0812 f7bed5fb, x0891 a669339c, x0923 e8a77b3e, x0807 989bea46 (SourceParentPalette: x0812's version); namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceBuildWindow
import Submission.Obl.k4_finite_affine_parent_sources.SourceLabelGroups
import Submission.Obl.k4_finite_affine_parent_sources.SourceVelCaps

/-!
# Pieces of the window parent: label groups at an intermediate level

Every label `Q` of an intermediate level `q` below the window parent `b₀` carries the retained
incidences `S_Q = S1 ∩ {history at q = Q}`. Labels with `S_Q` below the floor `τQ packet(Q)` are
deleted (their packets fill at most the parent's packet); every other label is cut into the
accepted oscillation groups in its own frame with the parent's hidden scale
(`path_label_groups`), and the uncovered part is deleted. On one group the parent's normalised
test varies by at most `K^C (δ(r_q)/δ(r_{b₀}) + |Δ base|)` in the coordinates of `Q`
(`q_level_groups`).

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_finite_forest_width_selection
open Submission.Obl.k4_stable_native_signal_oscillation Submission.Lib.K4XInterface
open scoped Classical

noncomputable section

local instance optMeasBP (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingBP (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- A retained incidence below the parent with a history `Q` at a deeper level: `Q` is a
descendant of the parent in its world, at that level, and counts the incidence. -/
theorem history_below {b₀ Q : Fin p.C} {q : ℕ} (hq : p.lev b₀ ≤ q) (hqm : q ≤ m - 1)
    {x : Incidence}
    (h0 : p.history m (p.lev b₀) (p.world b₀, x) = some b₀)
    (hQ : p.history m q (p.world b₀, x) = some Q) :
    p.lev Q = q ∧ forestAncestor p.lev p.par Q (p.lev b₀) = b₀ ∧ p.world Q = p.world b₀ ∧
      x ∈ p.counted Q := by
  have hlevQ := history_level hp hqm hQ
  have href := history_refines' hp hq (p.world b₀, x)
  rw [hQ, h0] at href
  simp only [PathData.ancestorCode, Option.map_some, Option.some.injEq] at href
  have hs := history_some hp hQ
  exact ⟨hlevQ, href.symm, hs.1.symm, hs.2⟩

/-- **Label groups at an intermediate level below the window parent.** -/
theorem q_level_groups (hν : ∀ w, IsProbabilityMeasure (ν w)) (hNk : 1 < Nk)
    {A C : ℕ} (hC : GroupsProp A C)
    (b₀ : Fin p.C) (q : ℕ) (hq : p.lev b₀ ≤ q) (hqm : q ≤ m - 1) (hB : 0 < B (p.world b₀))
    (S1 : Set Incidence) (hS1m : MeasurableSet S1)
    (hS1 : ∀ x ∈ S1, p.history m (p.lev b₀) (p.world b₀, x) = some b₀)
    {τQ : ℝ} (hτQ : 0 < τQ)
    {g : Observation → ENNReal} (hg : Measurable g) {rj τ h : ℝ}
    (hlaw : (((ν (p.world b₀)).prod volume).restrict (E (p.world b₀))).map
      (obs (B (p.world b₀)) (δ Nk rj)) = (volume.prod Measure.count).withDensity g)
    (hmask : S1 ⊆ E (p.world b₀) ∩
      {x | g (obs (B (p.world b₀)) (δ Nk rj) x) ≤ ENNReal.ofReal (Nk ^ (-f rj + τ))})
    (hh : 0 ≤ h) (hratio : δ Nk (p.r q) ≤ 2 * Nk ^ h * δ Nk rj)
    (hprof : f (p.r q) - 2 * (δ₀ * L) ≤ f rj)
    (ha1 : δ Nk (p.r q) ≤ δ Nk (p.r (p.lev b₀)))
    {K : ℝ} (hK2 : 2 ≤ K) (hK7 : 7 * p.κ ≤ K)
    (hKbig : p.κ * (4 * Nk ^ h + 2) * Nk ^ (τ + 2 * (δ₀ * L)) *
      (16 * (1 + (7 * p.κ) ^ 2)) ≤ K * τQ) :
    ∃ (S1' : Set Incidence) (n : Fin p.C → ℕ) (G : (Q : Fin p.C) → Fin (n Q) → Set Incidence),
      MeasurableSet S1' ∧ S1' ⊆ S1 ∧ (∀ Q, (n Q : ℝ) ≤ K ^ C) ∧
      (∀ Q i, MeasurableSet (G Q i)) ∧
      (∀ x ∈ S1', ∀ Q, p.history m q (p.world b₀, x) = some Q → ∃ i, x ∈ G Q i) ∧
      ((ν (p.world b₀)).prod volume) (S1 \ S1') ≤
        ENNReal.ofReal τQ * ((ν (p.world b₀)).prod volume) (p.packet b₀) +
          ENNReal.ofReal ((K ^ A)⁻¹) * ((ν (p.world b₀)).prod volume) S1 ∧
      ∀ Q i x y, x ∈ G Q i → y ∈ G Q i →
        |(δ Nk (p.r (p.lev b₀)))⁻¹ * eval (gx x.1 x.2) (p.test b₀) -
          (δ Nk (p.r (p.lev b₀)))⁻¹ * eval (gx y.1 y.2) (p.test b₀)| ≤
        K ^ C * (δ Nk (p.r q) / δ Nk (p.r (p.lev b₀)) +
          ‖nativeBase (framePoint (labelFrame p Q (B (p.world b₀))
              (δ Nk (p.r (p.lev b₀)))) x) -
            nativeBase (framePoint (labelFrame p Q (B (p.world b₀))
              (δ Nk (p.r (p.lev b₀)))) y)‖) := by
  set w₀ := p.world b₀ with hw₀
  set δp := δ Nk (p.r (p.lev b₀)) with hδp
  have hNk0 : 0 < Nk := by linarith
  have hδ (r : ℝ) : 0 < δ Nk r := lt_of_lt_of_le (Real.rpow_pos_of_pos hNk0 _) (δ_bounds hNk r).1
  letI : ∀ w, IsProbabilityMeasure (ν w) := hν
  -- the pieces of the labels
  set SQ : Fin p.C → Set Incidence := fun Q => S1 ∩ {x | p.history m q (w₀, x) = some Q}
    with hSQ
  have hhm : ∀ Q, MeasurableSet {x : Incidence | p.history m q (w₀, x) = some Q} := fun Q =>
    (hp.measurable_history _).comp measurable_prodMk_left (measurableSet_singleton _)
  have hSQm : ∀ Q, MeasurableSet (SQ Q) := fun Q => hS1m.inter (hhm Q)
  have hrel : ∀ Q, (SQ Q).Nonempty → p.lev Q = q ∧
      forestAncestor p.lev p.par Q (p.lev b₀) = b₀ ∧ p.world Q = w₀ ∧ SQ Q ⊆ p.counted Q := by
    intro Q ⟨x, hx⟩
    obtain ⟨h1, h2, h3, -⟩ := history_below hp hq hqm (hS1 x hx.1) hx.2
    refine ⟨h1, h2, h3, fun y hy => ?_⟩
    exact (history_below hp hq hqm (hS1 y hy.1) hy.2).2.2.2
  -- heavy labels
  let heavy : Fin p.C → Prop := fun Q => (SQ Q).Nonempty ∧
    ENNReal.ofReal τQ * ((ν w₀).prod volume) (p.packet Q) ≤ ((ν w₀).prod volume) (SQ Q)
  have hgroups : ∀ Q, ∃ (n : ℕ) (Eg : Fin n → Set (Trajectory × ℝ)), (n : ℝ) ≤ K ^ C ∧
      (∀ i, MeasurableSet (Eg i)) ∧ (¬ heavy Q → n = 0) ∧
      (heavy Q →
        muE (ν w₀) (p.assigned Q) (labelFrame p Q (B w₀) δp).F.t₀
            (labelFrame p Q (B w₀) δp).F.q (SQ Q) (⋃ i, Eg i)ᶜ ≤
          ENNReal.ofReal ((K ^ A)⁻¹) * muE (ν w₀) (p.assigned Q)
            (labelFrame p Q (B w₀) δp).F.t₀ (labelFrame p Q (B w₀) δp).F.q (SQ Q) univ ∧
        ∀ i y, y ∈ Eg i → ∀ y', y' ∈ Eg i →
          |value ((labelFrame p Q (B w₀) δp).normTest δp (p.test b₀))
              (pointS (labelFrame p Q (B w₀) δp).eb y) -
            value ((labelFrame p Q (B w₀) δp).normTest δp (p.test b₀))
              (pointS (labelFrame p Q (B w₀) δp).eb y')| ≤
            K ^ C * (δ Nk (p.r (p.lev Q)) / δp +
              ‖nativeBase (pointS (labelFrame p Q (B w₀) δp).eb y) -
                nativeBase (pointS (labelFrame p Q (B w₀) δp).eb y')‖)) := by
    intro Q
    by_cases hQ : heavy Q
    · obtain ⟨hlevQ, hdesc, hwQ, hsub⟩ := hrel Q hQ.1
      have hB' : 0 < B (p.world Q) := by rw [hwQ]; exact hB
      have hfloor : ENNReal.ofReal τQ * ((ν (p.world Q)).prod volume) (p.packet Q) ≤
          ((ν (p.world Q)).prod volume) (SQ Q) := by rw [hwQ]; exact hQ.2
      have hlaw' : (((ν (p.world Q)).prod volume).restrict (E (p.world Q))).map
          (obs (B (p.world Q)) (δ Nk rj)) = (volume.prod Measure.count).withDensity g := by
        rw [hwQ]; exact hlaw
      have hmask' : SQ Q ⊆ E (p.world Q) ∩
          {x | g (obs (B (p.world Q)) (δ Nk rj) x) ≤ ENNReal.ofReal (Nk ^ (-f rj + τ))} := by
        rw [hwQ]; exact fun x hx => hmask hx.1
      have hratio' : δ Nk (p.r (p.lev Q)) ≤ 2 * Nk ^ h * δ Nk rj := by rw [hlevQ]; exact hratio
      have hprof' : f (p.r (p.lev Q)) - 2 * (δ₀ * L) ≤ f rj := by rw [hlevQ]; exact hprof
      have ha1' : δ Nk (p.r (p.lev Q)) ≤ δ Nk (p.r (p.lev b₀)) := by rw [hlevQ]; exact ha1
      have hlev' : p.lev b₀ ≤ p.lev Q := by rw [hlevQ]; exact hq
      obtain ⟨n, Eg, hn, hEgm, -, hcov, hsig⟩ := path_label_groups hp hν hNk hC Q b₀ hdesc
        hlev' hB' (hSQm Q) hsub hτQ hfloor hg hlaw' hmask' hh hratio' hprof' ha1' hK2 hK7 hKbig
      rw [hwQ] at hcov hsig
      exact ⟨n, Eg, hn, hEgm, fun h => absurd hQ h, fun _ => ⟨hcov, hsig⟩⟩
    · refine ⟨0, Fin.elim0, ?_, fun i => i.elim0, fun _ => rfl, fun h => absurd h hQ⟩
      simp only [CharP.cast_eq_zero]
      positivity
  choose n Eg hn hEgm hzero hprop using hgroups
  set G : (Q : Fin p.C) → Fin (n Q) → Set Incidence := fun Q i =>
    tnorm (labelFrame p Q (B w₀) δp).F.t₀ (labelFrame p Q (B w₀) δp).F.q ⁻¹' Eg Q i with hG
  have hGm : ∀ Q i, MeasurableSet (G Q i) := fun Q i => measurable_tnorm _ _ (hEgm Q i)
  -- the covered part
  set S1' : Set Incidence := S1 ∩ ⋂ Q, ({x | p.history m q (w₀, x) = some Q}ᶜ ∪
    (if heavy Q then ⋃ i, G Q i else ∅)) with hS1'
  have hS1'm : MeasurableSet S1' := by
    refine hS1m.inter (MeasurableSet.iInter fun Q => (hhm Q).compl.union ?_)
    split_ifs
    · exact MeasurableSet.iUnion fun i => hGm Q i
    · exact MeasurableSet.empty
  refine ⟨S1', n, G, hS1'm, inter_subset_left, hn, hGm, ?_, ?_, ?_⟩
  · intro x hx Q hQ
    have hx2 := mem_iInter.mp hx.2 Q
    rcases hx2 with h1 | h1
    · exact absurd hQ h1
    · split_ifs at h1 with hh'
      · exact mem_iUnion.mp h1
      · simp at h1
  · -- the deleted mass
    have hcover : S1 \ S1' ⊆ ⋃ Q, (if heavy Q then SQ Q \ ⋃ i, G Q i else SQ Q) := by
      intro x hx
      have hnot : ¬ ∀ Q, x ∈ ({x | p.history m q (w₀, x) = some Q}ᶜ ∪
          (if heavy Q then ⋃ i, G Q i else ∅)) := by
        intro hall
        exact hx.2 ⟨hx.1, mem_iInter.mpr hall⟩
      push_neg at hnot
      obtain ⟨Q, hQ⟩ := hnot
      simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hQ
      refine mem_iUnion.mpr ⟨Q, ?_⟩
      split_ifs with hh'
      · refine ⟨⟨hx.1, hQ.1⟩, ?_⟩
        have := hQ.2
        rw [if_pos hh'] at this
        exact this
      · exact ⟨hx.1, hQ.1⟩
    have hlight : ∀ Q, ¬ heavy Q → ((ν w₀).prod volume) (SQ Q) ≤
        if p.lev Q = q ∧ p.lev b₀ ≤ p.lev Q ∧ forestAncestor p.lev p.par Q (p.lev b₀) = b₀
        then ENNReal.ofReal τQ * ((ν w₀).prod volume) (p.packet Q) else 0 := by
      intro Q hQ
      by_cases hne : (SQ Q).Nonempty
      · obtain ⟨hlevQ, hdesc, -, -⟩ := hrel Q hne
        rw [if_pos ⟨hlevQ, hlevQ ▸ hq, hdesc⟩]
        by_contra hlt
        exact hQ ⟨hne, (not_le.mp hlt).le⟩
      · rw [not_nonempty_iff_eq_empty.mp hne, measure_empty]
        exact bot_le
    have hheavy : ∀ Q, heavy Q → ((ν w₀).prod volume) (SQ Q \ ⋃ i, G Q i) ≤
        ENNReal.ofReal ((K ^ A)⁻¹) * ((ν w₀).prod volume) (SQ Q) := by
      intro Q hQ
      obtain ⟨hlevQ, hdesc, hwQ, hsub⟩ := hrel Q hQ.1
      have hcov := (hprop Q hQ).1
      have hq0 := labelFrame_q_pos hp Q (B w₀) δp
      have hprior := label_prior_floor hp hNk0 Q
      have hdetQ : 0 < |(p.frame Q).det| := abs_pos.mpr (hp.chart Q).1
      have hA0 : 0 < ν w₀ (p.assigned Q) := by
        rw [← hwQ]
        exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by
          have := hp.one_le_slack; positivity)) hprior
      have hA0t : ν w₀ (p.assigned Q) ≠ ⊤ := measure_ne_top _ _
      have hc0 : ENNReal.ofReal (labelFrame p Q (B w₀) δp).F.q * ν w₀ (p.assigned Q) ≠ 0 :=
        mul_ne_zero (ENNReal.ofReal_pos.mpr hq0).ne' hA0.ne'
      have hct : ENNReal.ofReal (labelFrame p Q (B w₀) δp).F.q * ν w₀ (p.assigned Q) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA0t
      have hUm : MeasurableSet (⋃ i, Eg Q i)ᶜ := (MeasurableSet.iUnion fun i => hEgm Q i).compl
      rw [muE_apply _ _ _ _ _ hUm, muE_apply _ _ _ _ _ MeasurableSet.univ, preimage_univ,
        univ_inter] at hcov
      have hset : tnorm (labelFrame p Q (B w₀) δp).F.t₀ (labelFrame p Q (B w₀) δp).F.q ⁻¹'
          (⋃ i, Eg Q i)ᶜ ∩ SQ Q = SQ Q \ ⋃ i, G Q i := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_iUnion, mem_diff, hG]
        tauto
      rw [hset] at hcov
      set c := ENNReal.ofReal (labelFrame p Q (B w₀) δp).F.q * ν w₀ (p.assigned Q)
      calc ((ν w₀).prod volume) (SQ Q \ ⋃ i, G Q i)
          = c * (c⁻¹ * ((ν w₀).prod volume) (SQ Q \ ⋃ i, G Q i)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hct, one_mul]
        _ ≤ c * (ENNReal.ofReal ((K ^ A)⁻¹) * (c⁻¹ * ((ν w₀).prod volume) (SQ Q))) := by
            gcongr
        _ = ENNReal.ofReal ((K ^ A)⁻¹) * ((ν w₀).prod volume) (SQ Q) := by
            rw [← mul_assoc, mul_comm c, mul_assoc, ← mul_assoc c, ENNReal.mul_inv_cancel hc0 hct,
              one_mul]
    -- the pieces partition the retained set
    have hsum : (∑ Q, ((ν w₀).prod volume) (SQ Q)) ≤ ((ν w₀).prod volume) S1 := by
      have hdisj : Pairwise (fun Q Q' => Disjoint (SQ Q) (SQ Q')) := by
        intro Q Q' hne
        refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
        have h1 := hx.2
        have h2 := hx'.2
        simp only [mem_ofPred_eq] at h1 h2
        rw [h1] at h2
        exact Option.some.inj h2
      have hU := measure_iUnion (μ := (ν w₀).prod volume) hdisj hSQm
      rw [tsum_fintype] at hU
      rw [← hU]
      exact measure_mono (iUnion_subset fun Q => inter_subset_left)
    calc ((ν w₀).prod volume) (S1 \ S1')
        ≤ ((ν w₀).prod volume) (⋃ Q, (if heavy Q then SQ Q \ ⋃ i, G Q i else SQ Q)) :=
          measure_mono hcover
      _ ≤ ∑ Q, ((ν w₀).prod volume) (if heavy Q then SQ Q \ ⋃ i, G Q i else SQ Q) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ Q, ((if p.lev Q = q ∧ p.lev b₀ ≤ p.lev Q ∧
              forestAncestor p.lev p.par Q (p.lev b₀) = b₀
            then ENNReal.ofReal τQ * ((ν w₀).prod volume) (p.packet Q) else 0) +
            ENNReal.ofReal ((K ^ A)⁻¹) * ((ν w₀).prod volume) (SQ Q)) := by
          refine Finset.sum_le_sum fun Q _ => ?_
          by_cases hh' : heavy Q
          · rw [if_pos hh']
            exact (hheavy Q hh').trans le_add_self
          · rw [if_neg hh']
            exact (hlight Q hh').trans le_self_add
      _ = ENNReal.ofReal τQ * ∑ Q ∈ Finset.univ.filter (fun Q => p.lev Q = q ∧
              p.lev b₀ ≤ p.lev Q ∧ forestAncestor p.lev p.par Q (p.lev b₀) = b₀),
              ((ν w₀).prod volume) (p.packet Q) +
            ENNReal.ofReal ((K ^ A)⁻¹) * ∑ Q, ((ν w₀).prod volume) (SQ Q) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.sum_filter]
      _ ≤ ENNReal.ofReal τQ * ((ν w₀).prod volume) (p.packet b₀) +
            ENNReal.ofReal ((K ^ A)⁻¹) * ((ν w₀).prod volume) S1 := by
          gcongr
          exact desc_packets_le hp b₀ q
  · -- the signal on one group
    intro Q i x y hx hy
    by_cases hQ : heavy Q
    · obtain ⟨hlevQ, -, -, -⟩ := hrel Q hQ.1
      have hsig := (hprop Q hQ).2 i _ hx _ hy
      have hq0 := labelFrame_q_pos hp Q (B w₀) δp
      have hD := labelFrame_det hp Q (B w₀) δp
      have hsc : (labelFrame p Q (B w₀) δp).sc ≠ 0 := by
        rw [labelFrame_sc]; exact (div_pos hB (hδ _)).ne'
      have e1 := value_normTest_framePoint (labelFrame p Q (B w₀) δp) hq0 hD hsc δp (p.test b₀) x
      have e2 := value_normTest_framePoint (labelFrame p Q (B w₀) δp) hq0 hD hsc δp (p.test b₀) y
      rw [framePoint] at e1 e2
      rw [e1, e2, hlevQ] at hsig
      exact hsig
    · have : n Q = 0 := hzero Q hQ
      exact absurd i.2 (by omega)

end

end

end Submission.Obl.k4_finite_affine_parent_sources
