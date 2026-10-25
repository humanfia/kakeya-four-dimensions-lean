-- `sampleCleanPos` is adapted from this LOT tree, o209 (accepted), file
-- Submission/Obl/k4_fixed_menu_density_pruning/Sample.lean (`sampleClean`): the same
-- per-sample cleaning, for the positive-narrowness path of o234 instead of o209's
-- zero-narrowness path. The proof never uses the narrowness conjunct of the path.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCore
import Submission.Obl.k4_fixed_menu_density_pruning.SampleClean
import Submission.Obl.k4_fixed_menu_density_pruning.TwoStagePruning
import Submission.Obl.k4_fixed_menu_density_pruning.PacketFacts
import Submission.Obl.k4_fixed_menu_density_pruning.DensityCut
import Submission.Obl.k4_fixed_menu_density_pruning.Reindex

set_option linter.unusedVariables false

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_fixed_menu_density_pruning (gcBody upperTail menuDepth
  measure_trim_to_interior level_interior_disjoint incidence_mem_old_packet
  mass_ne_top_of_time_block menuDepth_bounds finite_density_cut measurable_obs
  two_stage_pruning ofReal_half_div retained_map_le card_filter_comp_le sum_reindex_finset)

/-- **The per-sample cleaning** of o209, for the positive-narrowness path. -/
theorem sampleCleanPos (ℓ : ℝ) (Nk L : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (B : Fin W → ℝ) (f : ℝ → ℝ)
    (g : Fin W → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (d₁ κ₁ ρ gain δ₀ τ ε σ : ℝ) (m : ℕ) (s : ℕ → ℝ) (Mp Dp Mg Dg : ℕ)
    (r : ℕ → ℝ) (T : ℕ → ℕ) (nw : ℕ → ℝ) (κ : ℝ) (C : ℕ) (lev : Fin C → ℕ)
    (par : Fin C → Fin C) (γ : Fin C → Fin W) (j : Fin C → ℕ)
    (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
    (F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C))
    (i : ℕ) (h : ℝ) (n : ℕ) (old : Fin n → Fin C) (R' : Fin n → MvPolynomial (Fin 4) ℝ)
    (A' : Fin n → Set (ℕ × (Fin 6 → ℝ))) (V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hNk : 2 ≤ Nk) (hL : 0 < L) (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ < 1) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1 / 4) (hgain : 0 < gain) (hgain1 : gain ≤ 1 / 8)
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ ≤ ρ * gain) (hτ : 0 < τ) (hε : 0 < ε)
    (hω : ∀ w, 0 ≤ ω w) (hω1 : (∑ w, ω w) = 1)
    (hdata : ∀ w, IsProbabilityMeasure (ν w) ∧ 0 < B w ∧ MeasurableSet (E w) ∧
      E w ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (hlaw : ∀ w q, 0 ≤ q → q ≤ L → Measurable (g w q) ∧
      (((ν w).prod volume).restrict (E w)).map (obs (B w) (δ Nk q)) =
        (volume.prod Measure.count).withDensity (g w q))
    (hp : PositivePath ℓ Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hgc : gcBody Nk L W ω ν B d₁ ρ gain m r T C lev γ j A F Mg Dg ε i h n old R' A' V)
    (htailc : upperTail Nk W ω ν E B f g τ (menuDepth L (s i) h δ₀) ≤
      ENNReal.ofReal (Nk ^ (-ε) / 48))
    (htailo : upperTail Nk W ω ν E B f g τ (menuDepth L (s i) 0 δ₀) ≤
      ENNReal.ofReal (Nk ^ (-ε) / 48))
    (htailL : upperTail Nk W ω ν E B f g τ L ≤ ENNReal.ofReal (Nk ^ (-ε) / 48)) :
    CleanCover Nk L W ω ν B f d₁ ρ gain δ₀ m s r T κ C lev γ j Q A F Mg Dg τ ε := by
  classical
  haveI : ∀ w, IsProbabilityMeasure (ν w) := fun w => (hdata w).1
  let μ : Fin W → Measure Incidence := fun w => ((ν w).prod volume).restrict (E w)
  rcases hp with ⟨hκ, hκN, hC, hrLast, hlevels, hlist, hAdisj, hcharts⟩
  have facts (b : Fin C) : MeasurableSet (F b) ∧
      (∀ p ∈ F b, p ∈ E (γ b) ∧ p.1 ∈ A b ∧
        p.2 ∈ Icc ((j b : ℝ) / (2 : ℝ) ^ T (lev b))
          (((j b : ℝ) + 1) / (2 : ℝ) ^ T (lev b))) ∧
      ENNReal.ofReal (Nk ^ (-f (r (lev b))) * |Matrix.det (Q b)| /
        ((2 : ℝ) ^ T (lev b) * κ)) ≤ ((ν (γ b)).prod volume) (F b) ∧
      (0 < lev b → lev (par b) + 1 = lev b ∧ γ (par b) = γ b ∧ F b ⊆ F (par b)) := by
    rcases hcharts b with ⟨hl, hj, hdet, hc, hQ, hq, hd, hcoeff,
      hAm, hFm, hfmt, htest, hinc, hsat, hprior, hdetlo, hdetup, hli, hparent⟩
    refine ⟨hFm, (fun p hp => ⟨(hinc p hp).1, (hinc p hp).2.1,
      (hinc p hp).2.2.1⟩), hsat, ?_⟩
    intro hb
    exact ⟨(hparent hb).1, (hparent hb).2.1, (hparent hb).2.2.2.1⟩
  have hFE (b : Fin C) : F b ⊆ E (γ b) := fun p hp => ((facts b).2.1 p hp).1
  rcases hgc with ⟨hi, hhgain, hhmax, hhmenu, hroom, hn, hcand, hA'disj, hcount, hVdisj, hmass⟩
  have hlev (a : Fin n) : lev (old a) = i := (hcand a).1
  have hVm (a : Fin n) : MeasurableSet (V a) := (hcand a).2.2.2.2.2.2.2.2.1
  have hVA (a : Fin n) (p : Incidence) (hp : p ∈ V a) :=
    (hcand a).2.2.2.2.2.2.2.2.2.1 hp
  have hVE (a : Fin n) : V a ⊆ E (γ (old a)) := by
    intro p hp
    obtain ⟨b, hb, hγ, hpF⟩ := (hVA a p hp).1
    simpa only [hγ] using hFE b hpF
  let It (b : Fin C) : Set Incidence :=
    {p | p.2 ∈ Ioo ((j b : ℝ) / (2 : ℝ) ^ T i)
      (((j b : ℝ) + 1) / (2 : ℝ) ^ T i)}
  have hIt (b : Fin C) : MeasurableSet (It b) :=
    measurableSet_Ioo.preimage measurable_snd
  let F₀ : Fin C → Set Incidence := fun b => if lev b = i then F b ∩ It b else ∅
  let V₀ : Fin n → Set Incidence := fun a => V a ∩ It (old a)
  have hF₀m (b : Fin C) : MeasurableSet (F₀ b) := by
    dsimp only [F₀]
    split_ifs
    · exact (facts b).1.inter (hIt b)
    · exact MeasurableSet.empty
  have hV₀m (a : Fin n) : MeasurableSet (V₀ a) := (hVm a).inter (hIt _)
  have hF₀sub (b : Fin C) : F₀ b ⊆ F b := by
    dsimp only [F₀]
    split_ifs
    · exact inter_subset_left
    · exact empty_subset _
  have hV₀E (a : Fin n) : V₀ a ⊆ E (γ (old a)) := inter_subset_left.trans (hVE a)
  have hF₀mass (b : Fin C) (hb : lev b = i) :
      μ (γ b) (F₀ b) = ((ν (γ b)).prod volume) (F b) := by
    rw [show μ (γ b) (F₀ b) = ((ν (γ b)).prod volume) (F₀ b) from
      Measure.restrict_eq_self _ ((hF₀sub b).trans (hFE b))]
    simp only [F₀, ite_eq_left hb]
    apply measure_trim_to_interior
    intro p hp
    simpa only [hb] using ((facts b).2.1 p hp).2.2
  have hV₀mass (a : Fin n) :
      μ (γ (old a)) (V₀ a) = ((ν (γ (old a))).prod volume) (V a) := by
    rw [show μ (γ (old a)) (V₀ a) = ((ν (γ (old a))).prod volume) (V₀ a) from
      Measure.restrict_eq_self _ (hV₀E a)]
    exact measure_trim_to_interior _ _ _ _ (fun p hp => (hVA a p hp).2.2.1)
  have hF₀d := level_interior_disjoint lev γ j T A F i
    (fun b p hp => ((facts b).2.1 p hp).2.1) hAdisj
  have hV₀sub (a : Fin n) : V₀ a ⊆ F₀ (old a) := by
    intro p hp
    simp only [F₀, ite_eq_left (hlev a), mem_inter_iff]
    refine ⟨?_, hp.2⟩
    obtain ⟨b, hb, hγ, hpF⟩ := (hVA a p hp.1).1
    apply incidence_mem_old_packet lev par γ j T A F
      (fun b hb => ((facts b).2.2.2 hb).1)
      (fun b hb => ((facts b).2.2.2 hb).2.1)
      (fun b hb => ((facts b).2.2.2 hb).2.2)
      (fun b p hp => ⟨((facts b).2.1 p hp).2.1, ((facts b).2.1 p hp).2.2⟩)
      hAdisj (by rw [hlev a, hb]; omega) hγ hpF
      ((hcand a).2.2.2.2.2.1 ((hVA a p hp.1).2.1))
    rw [hlev a]
    exact hp.2
  have hfinF (b : Fin C) : μ (γ b) (F₀ b) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (b := ((ν (γ b)).prod volume) (F b))
    · exact mass_ne_top_of_time_block _ (fun p hp => ((facts b).2.1 p hp).2.2)
    · exact (Measure.restrict_le_self (F₀ b)).trans (measure_mono (hF₀sub b))
  have hfinV (a : Fin n) : μ (γ (old a)) (V₀ a) ≠ ⊤ := by
    rw [hV₀mass]
    exact mass_ne_top_of_time_block _ (fun p hp => (hVA a p hp).2.2.1)
  let q : Fin 3 → ℝ := ![menuDepth L (s i) h δ₀, menuDepth L (s i) 0 δ₀, L]
  have hq (a : Fin 3) : 0 ≤ q a ∧ q a ≤ L := by
    fin_cases a
    · exact menuDepth_bounds hL.le
    · exact menuDepth_bounds hL.le
    · exact ⟨hL.le, le_rfl⟩
  obtain ⟨Good, hGood, hGoodloss, hGoodcap⟩ := finite_density_cut
    μ (fun w => ENNReal.ofReal (ω w)) (volume.prod Measure.count)
    (fun a w => obs (B w) (δ Nk (q a))) (fun a w => g w (q a))
    (fun a => ENNReal.ofReal (Nk ^ (-f (q a) + τ)))
    (fun a w => measurable_obs _ _) (fun a w => (hlaw w (q a) (hq a).1 (hq a).2).1)
    (fun a w => (hlaw w (q a) (hq a).1 (hq a).2).2)
  have herr : ∑ w, ENNReal.ofReal (ω w) * μ w (Good w)ᶜ ≤
      ENNReal.ofReal (Nk ^ (-ε) / 12) := by
    apply hGoodloss.trans
    change (∑ a : Fin 3, upperTail Nk W ω ν E B f g τ (q a)) ≤ _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [q, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero]
    calc
      _ ≤ ENNReal.ofReal (Nk ^ (-ε) / 48) +
          (ENNReal.ofReal (Nk ^ (-ε) / 48) + ENNReal.ofReal (Nk ^ (-ε) / 48)) :=
        add_le_add htailc (add_le_add htailo htailL)
      _ = ENNReal.ofReal (Nk ^ (-ε) / 16) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        have hpow : 0 ≤ Nk ^ (-ε) := by positivity
        linarith)
  obtain ⟨S, V', hV'm, hV'sub, hV'empty, hhalf, hmass'⟩ := two_stage_pruning
    μ (fun w => ENNReal.ofReal (ω w)) γ F₀ old V₀ Good hF₀m hGood hV₀m hF₀d
    (fun a a' hne hγ => (hVdisj a a' hne hγ).mono inter_subset_left inter_subset_left)
    hV₀sub hfinF hfinV (by positivity : 0 ≤ Nk ^ (-ε))
    (hmass.trans_eq (Finset.sum_congr rfl (fun a _ => by rw [hV₀mass]))) herr
  let e : Fin S.card ↪o Fin n := S.orderEmbOfFin rfl
  let U : Fin C → Set Incidence := fun b => F₀ b ∩ Good (γ b)
  have hV'E (a : Fin n) : V' a ⊆ E (γ (old a)) :=
    (hV'sub a).trans (inter_subset_left.trans (hV₀E a))
  have hV'mass (a : Fin n) :
      μ (γ (old a)) (V' a) = ((ν (γ (old a))).prod volume) (V' a) :=
    Measure.restrict_eq_self _ (hV'E a)
  have hUmass (b : Fin C) : μ (γ b) (U b) = ((ν (γ b)).prod volume) (U b) :=
    Measure.restrict_eq_self _ (inter_subset_left.trans ((hF₀sub b).trans (hFE b)))
  refine ⟨i, h, S.card, old ∘ e, R' ∘ e, A' ∘ e, V' ∘ e, U,
    hi, hhgain, hhmax, hhmenu, hroom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast (show S.card ≤ n by simpa using S.card_le_univ)) hn
  · intro a
    dsimp only [Function.comp_apply]
    have ha := hcand (e a)
    have he : e a ∈ S := S.orderEmbOfFin_mem rfl a
    refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2.1,
      ha.2.2.2.2.2.2.1, ha.2.2.2.2.2.2.2.1, hV'm _, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      have hp' := hV'sub (e a) hp
      have hOrig := hVA (e a) p hp'.1.1
      exact ⟨⟨hV₀sub (e a) hp'.1, hp'.2⟩, hOrig.2⟩
    · rw [ofReal_half_div]
      calc
        _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * μ (γ (old (e a))) (V₀ (e a)) := by
          rw [hV₀mass]
          simpa only [mul_assoc] using
            mul_le_mul' (le_rfl : ENNReal.ofReal (1 / 2 : ℝ) ≤ _)
              ha.2.2.2.2.2.2.2.2.2.2
        _ ≤ _ := by rw [← hV'mass (e a)]; exact (hhalf (e a) he).1
    · rw [mul_assoc (2 : ℝ), ofReal_half_div]
      calc
        _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * μ (γ (old (e a))) (F₀ (old (e a))) := by
          rw [hF₀mass _ (hlev _), ← hlev (e a)]
          exact mul_le_mul' le_rfl (facts (old (e a))).2.2.1
        _ ≤ _ := by rw [← hUmass (old (e a))]; exact (hhalf (e a) he).2
    · exact retained_map_le _ (hGood _) (fun p hp => ⟨hV'E _ hp, (hV'sub _ hp).2⟩)
        _ (measurable_obs _ _) _ _ (hGoodcap 0 _)
    · exact retained_map_le _ (hGood _) (fun p hp => ⟨hV'E _ hp, (hV'sub _ hp).2⟩)
        _ (measurable_obs _ _) _ _ (hGoodcap 2 _)
  · intro b
    refine ⟨(hF₀m b).inter (hGood _), inter_subset_left.trans (hF₀sub b), ?_⟩
    exact retained_map_le _ (hGood _) (fun p hp => ⟨hFE b (hF₀sub b hp.1), hp.2⟩)
      _ (measurable_obs _ _) _ _ (hGoodcap 1 _)
  · intro a a' hne hold
    exact hA'disj _ _ (fun h => hne (e.injective h)) hold
  · intro b
    exact le_trans (by exact_mod_cast card_filter_comp_le e e.injective old b) (hcount b)
  · intro a a' hne hγ
    exact (hVdisj _ _ (fun h => hne (e.injective h)) hγ).mono
      ((hV'sub _).trans (inter_subset_left.trans inter_subset_left))
      ((hV'sub _).trans (inter_subset_left.trans inter_subset_left))
  · dsimp only [Function.comp_apply]
    rw [sum_reindex_finset S (fun a : Fin n => ENNReal.ofReal (ω (γ (old a))) *
      ((ν (γ (old a))).prod volume) (V' a))
      (fun a ha => by rw [hV'empty a ha, measure_empty, mul_zero])]
    simpa only [hV'mass] using hmass'

end Submission.Obl.k4_finite_positive_mixed_cover_realization
