/- Adapted from this LOT tree, obligation o212, session x0762, commit ecff5a0a89fd,
   Submission/Obl/k4_critical_intercept_concentration/SourcePairs.lean.
   Existing source attributions below are preserved. -/
import Submission.Obl.k4_critical_switching_state_preparation.ParentFrame
import Submission.Obl.k4_critical_switching_state_preparation.AffineEntries
import Submission.Obl.k4_critical_switching_state_preparation.NormalizedPredictors
import Submission.Obl.k4_critical_switching_state_preparation.UpperCount
import Submission.Obl.k4_critical_switching_state_preparation.PairCodes

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Finset Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

def midpointValue (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (p : α × ℝ) : ℝ :=
  affineResidualIntercept L (cfg.b k p.1) +
    cfg.midpoint k s i * affineResidualSlope L (cfg.b k p.1)

def sourcePair (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (L : Fin 4 → ℝ) (a δ : ℝ) : (α × ℝ) → ℤ × (Fin 3 → ℤ) :=
  pairCode a δ (cfg.midpointValue k s i L) (cfg.framedPoint k s i)

def sourcePredictorSlope (k : ℕ) (s M : ℝ) : ℝ :=
  12 * cfg.K k ^ 2 * cfg.timeLength k s * (8 * cfg.K k ^ 4 + M)

/-- A single actual descendant pays for all source pairs it supplies. The
source witnesses retain the same midpoint intercept, original fitted subsets,
and exact contact-frame positions throughout this estimate. -/
theorem AssignmentLevel.source_child_pair_count {cfg : Data α} (h : cfg.Valid)
    {k : ℕ} {s t : ℝ} (parent : cfg.AssignmentLevel k s)
    (child : cfg.AssignmentLevel k t) (ip : Fin (cfg.n k s)) (i : Fin (cfg.n k t))
    (ht : 0 ≤ t) (hI : I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip))
    (L : Fin 4 → ℝ) (M E K δ : ℝ) (hM : 0 ≤ M)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ M)
    (hK : 4 * cfg.K k ^ 4 ≤ K) (hδ : 0 < δ)
    (hrel : cfg.timeLength k t / cfg.timeLength k s ≤ 1)
    (hδrel : δ ≤ (cfg.timeLength k t / cfg.timeLength k s) ^ 2)
    (hsmall : cfg.timeLength k s * E ≤ cfg.K k * cfg.N k ^ (-t))
    (hmesh : 3 * cfg.sourcePredictorSlope k s M * δ ≤ K * cfg.N k ^ (-t))
    (F : Finset (ℤ × (Fin 3 → ℤ)))
    (witness : (ℤ × (Fin 3 → ℤ)) → α × ℝ)
    (hsource : ∀ u ∈ F,
      (witness u).1 ∈ cfg.B k s ip ∧
      (witness u).2 ∈ I (cfg.T k s) (cfg.j k s ip) ∧
      (witness u).1 ∈ cfg.B k t i ∧
      (witness u).2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
      |affineResidualSlope L (cfg.b k (witness u).1)| ≤ E)
    (hcode : ∀ u ∈ F,
      cfg.sourcePair k s ip L (cfg.N k ^ (-t)) δ (witness u) = u) :
    (F.card : ℝ) * δ ^ 3 ≤
      4194304 * K ^ 4 * (cfg.timeLength k t / cfg.timeLength k s) ^ 4 := by
  classical
  have hK₀ := h.subpower.1 k
  have hKpow : 1 ≤ cfg.K k ^ 4 := one_le_pow₀ hK₀
  have hKlow : cfg.K k ≤ cfg.K k ^ 4 := by
    simpa using pow_le_pow_right₀ hK₀ (show 1 ≤ 4 by norm_num)
  have hKK : cfg.K k ≤ K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hH := cfg.timeLength_pos k s
  have hHc := cfg.timeLength_pos k t
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have ha : 0 < cfg.N k ^ (-t) := Real.rpow_pos_of_pos hN _
  by_cases hF : F.Nonempty
  · obtain ⟨u₀, hu₀⟩ := hF
    obtain ⟨hp₀, ht₀, hi₀, hti₀, hslope₀⟩ := hsource u₀ hu₀
    obtain ⟨A, hAeq, hA, hfit⟩ := child.active_affine_entry h ht i
      (witness u₀).1 hi₀ (witness u₀).2 hti₀
    let H := cfg.timeLength k s
    let r := cfg.timeLength k t / H
    let t₀ := cfg.blockOrigin k s ip 0
    let z₀ := cfg.blockOrigin k s ip 1
    let y₀ := cfg.blockOrigin k s ip 2
    let v₀ := cfg.c k s ip 1
    let c' := horizontalBoxCoefficients H t₀ z₀ y₀ v₀ (cfg.c k t i)
    let m' := (cfg.midpoint k t i - t₀) / H
    let predictor := normalizedPredictor H t₀ z₀ y₀ v₀ (A - L)
    have hbox := parent.normalized_true_box h child ip i hrel
      (parent.fitted_subset ip hp₀) ht₀ (child.fitted_subset i hi₀) hti₀
    change |c' 1| ≤ 4 * cfg.K k ^ 4 ∧ |c' 0 + m' * c' 1| ≤ 4 * cfg.K k ^ 4 ∧
      |c' 3 + c' 0 + m' * c' 1| ≤ (4 * cfg.K k ^ 4) * r ∧
      |c' 4 - m'| ≤ (4 * cfg.K k ^ 4) * r ∧
      ∀ q ∈ horizontalTrueBox (cfg.c k t i) (cfg.midpoint k t i)
          (cfg.timeLength k t) (cfg.K k ^ 2),
        cfg.parentFrame k s ip q ∈ horizontalTrueBox c' m' r (4 * cfg.K k ^ 4) at hbox
    have hm' : |m'| ≤ 1 := by
      have hm := cfg.parentFrame_time_mem k s ip
        (nativeHorizontalLine (cfg.b k (witness u₀).1) (cfg.midpoint k t i))
        (hI (cfg.midpoint_mem_I k t i))
      change m' ∈ Icc (0 : ℝ) 1 at hm
      simpa only [abs_of_nonneg hm.1] using hm.2
    have horigin := parent.blockOrigin_bounds h ip
    have hframeK : 1 ≤ 3 * cfg.K k ^ 2 := by nlinarith
    have hphys : ∀ e : Fin 3, |(A - L) e.succ| ≤ 8 * cfg.K k ^ 4 + M := by
      intro e
      exact (abs_sub _ _).trans (add_le_add (hA e) (hL e))
    have hpred : ∀ e : Fin 3, |predictor e.succ| ≤ cfg.sourcePredictorSlope k s M := by
      have hh := normalizedPredictor_slope_bound H t₀ z₀ y₀ v₀
        (3 * cfg.K k ^ 2) (8 * cfg.K k ^ 4 + M) (A - L)
        hH.le (cfg.timeLength_le_one k s) hframeK (by positivity)
        horigin.1 (horigin.2.1.trans (by nlinarith [hK₀]))
        (horigin.2.2.trans (by nlinarith [hK₀])) hphys
      intro e
      convert hh e using 1 <;> dsimp [sourcePredictorSlope, H] <;> ring
    have hpoint (u) (hu : u ∈ F) :
        cfg.framedPoint k s ip (witness u) ∈ contactGridCell δ u.2 ∧
        cfg.framedPoint k s ip (witness u) ∈ horizontalTrueBox c' m' r K := by
      obtain ⟨hp, hpt, hi, hit, hslope⟩ := hsource u hu
      constructor
      · have heq := congrArg Prod.snd (hcode u hu)
        exact fun e => congrFun heq e
      · have hh := hbox.2.2.2.2 _
          (child.native_point_in_true_box h i (witness u).1 (child.fitted_subset i hi) hit)
        exact ⟨hh.1, hh.2.1.trans (mul_le_mul_of_nonneg_right hK (div_nonneg hHc.le hH.le)),
          hh.2.2.trans (mul_le_mul_of_nonneg_right hK (sq_nonneg r))⟩
    have hprediction (u) (hu : u ∈ F) :
        |cfg.midpointValue k s ip L (witness u) -
          affineBaseEval predictor (cfg.framedPoint k s ip (witness u))| ≤
          2 * K * cfg.N k ^ (-t) := by
      obtain ⟨hp, hpt, hi, hit, hslope⟩ := hsource u hu
      have hgap : |cfg.midpoint k s ip - (witness u).2| ≤ H := by
        have hg := mem_I_time_gap _ _ hpt
        change |(witness u).2 - cfg.midpoint k s ip| ≤ H / 2 at hg
        rw [abs_sub_comm] at hg
        exact hg.trans (by linarith)
      have hh := midpoint_intercept_prediction_normalized A L (cfg.b k (witness u).1)
        H t₀ z₀ y₀ v₀ (cfg.midpoint k s ip) (witness u).2 (cfg.N k ^ (-t))
        (cfg.K k) E hH (hfit _ hi _ hit) hslope hgap hsmall
      exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : 2 * cfg.K k ≤ 2 * K) ha.le)
    exact true_box_intercept_pair_count F
      (fun u => cfg.framedPoint k s ip (witness u))
      (fun u => cfg.midpointValue k s ip L (witness u)) predictor c' m' r K δ
      (cfg.N k ^ (-t)) (cfg.sourcePredictorSlope k s M)
      (div_pos hHc hH) hrel hK1 hδ hδrel ha (by dsimp [sourcePredictorSlope]; positivity)
      hm' (hbox.1.trans hK) (hbox.2.1.trans hK)
      (hbox.2.2.1.trans (mul_le_mul_of_nonneg_right hK (div_nonneg hHc.le hH.le)))
      (hbox.2.2.2.1.trans (mul_le_mul_of_nonneg_right hK (div_nonneg hHc.le hH.le)))
      hpred hmesh hpoint (fun u hu => congrArg Prod.fst (hcode u hu)) hprediction
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity

/-- The occupied-pair table is the image of actual original incidences.
The number of pairs uses the full original assignment weights, even when
its source is an arbitrary later restriction. -/
theorem AssignmentLevel.exists_source_pair_table {cfg : Data α} (h : cfg.Valid)
    {k : ℕ} {s t : ℝ} (parent : cfg.AssignmentLevel k s)
    (child : cfg.AssignmentLevel k t) (ip : Fin (cfg.n k s)) (ht : 0 ≤ t)
    (L : Fin 4 → ℝ) (M E K δ V : ℝ) (hM : 0 ≤ M)
    (hL : ∀ e : Fin 3, |L e.succ| ≤ M)
    (hK : 4 * cfg.K k ^ 4 ≤ K) (hδ : 0 < δ)
    (hrel : cfg.timeLength k t / cfg.timeLength k s ≤ 1)
    (hδrel : δ ≤ (cfg.timeLength k t / cfg.timeLength k s) ^ 2)
    (hsmall : cfg.timeLength k s * E ≤ cfg.K k * cfg.N k ^ (-t))
    (hmesh : 3 * cfg.sourcePredictorSlope k s M * δ ≤ K * cfg.N k ^ (-t))
    (source : Set (α × ℝ))
    (hsource : ∀ p ∈ source, p.1 ∈ cfg.B k s ip ∧
      p.2 ∈ I (cfg.T k s) (cfg.j k s ip) ∧ |affineResidualSlope L (cfg.b k p.1)| ≤ E)
    (hcover : ∀ p ∈ source, ∃ i : Fin (cfg.n k t),
      p.1 ∈ cfg.B k t i ∧ p.2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
      cfg.A k t i ⊆ cfg.A k s ip ∧ I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip))
    (hvalues : ∀ p ∈ source, |cfg.midpointValue k s ip L p| ≤ V) :
    ∃ F : Finset (ℤ × (Fin 3 → ℤ)),
      (∀ u, u ∈ F ↔ ∃ p ∈ source,
        cfg.sourcePair k s ip L (cfg.N k ^ (-t)) δ p = u) ∧
      (F.card : ℝ) * δ ^ 3 ≤ 4194304 * K ^ 4 * cfg.K k ^ 4 *
        (cfg.N k ^ (-s) / cfg.N k ^ (-t)) ^ cfg.d := by
  classical
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hH := cfg.timeLength_pos k s
  have hHc := cfg.timeLength_pos k t
  have hδcube : 0 < δ ^ 3 := pow_pos hδ _
  obtain ⟨F, hF⟩ := exists_actual_pair_table source (cfg.midpointValue k s ip L)
    (cfg.framedPoint k s ip) (cfg.N k ^ (-t)) δ V (8 * cfg.K k ^ 4)
    (Real.rpow_pos_of_pos hN _) hδ hvalues
    (fun p hp => (parent.framedPoint_bounds h ip
      (parent.fitted_subset ip (hsource p hp).1) (hsource p hp).2.1).2.2)
  change ∀ u, u ∈ F ↔ ∃ p ∈ source,
    cfg.sourcePair k s ip L (cfg.N k ^ (-t)) δ p = u at hF
  let D : Finset (Fin (cfg.n k t)) := Finset.univ.filter (fun i =>
    cfg.A k t i ⊆ cfg.A k s ip ∧ I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip))
  let G (i : Fin (cfg.n k t)) := F.filter (fun u => ∃ p ∈ source,
    p.1 ∈ cfg.B k t i ∧ p.2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
      cfg.sourcePair k s ip L (cfg.N k ^ (-t)) δ p = u)
  have hD (i) (hi : i ∈ D) : cfg.A k t i ⊆ cfg.A k s ip ∧
      I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip) :=
    (Finset.mem_filter.mp hi).2
  have hcount := parent.true_descendant_count h child ip D
    (fun i hi => (hD i hi).1) (fun i hi => (hD i hi).2)
  have hratio : (2 : ℝ) ^ cfg.T k t / (2 : ℝ) ^ cfg.T k s =
      cfg.timeLength k s / cfg.timeLength k t := by
    simp [timeLength, div_eq_mul_inv, mul_comm]
  rw [hratio] at hcount
  have hcount' : (D.card : ℝ) ≤ (cfg.K k ^ 2) ^ 2 *
      (cfg.timeLength k s / cfg.timeLength k t) ^ 4 *
      (cfg.N k ^ (-s) / cfg.N k ^ (-t)) ^ cfg.d := by
    convert hcount using 1 <;> ring
  have htotal : F ⊆ D.biUnion G := by
    intro u hu
    obtain ⟨p, hp, hpu⟩ := (hF u).mp hu
    obtain ⟨i, hi, hit, hAi, hIi⟩ := hcover p hp
    refine Finset.mem_biUnion.mpr ⟨i, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAi, hIi⟩
    · exact Finset.mem_filter.mpr ⟨hu, p, hp, hi, hit, hpu⟩
  have hlocal (i : Fin (cfg.n k t)) (hi : i ∈ D) :
      ((G i).card : ℝ) ≤ (4194304 * K ^ 4) *
        (cfg.timeLength k t / cfg.timeLength k s) ^ 4 / δ ^ 3 := by
    by_cases hGi : (G i).Nonempty
    · obtain ⟨u₀, hu₀⟩ := hGi
      have hex (u) (hu : u ∈ G i) : ∃ p ∈ source,
          p.1 ∈ cfg.B k t i ∧ p.2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
            cfg.sourcePair k s ip L (cfg.N k ^ (-t)) δ p = u :=
        (Finset.mem_filter.mp hu).2
      let p₀ := Classical.choose (hex u₀ hu₀)
      let witness (u : ℤ × (Fin 3 → ℤ)) : α × ℝ :=
        if hu : u ∈ G i then Classical.choose (hex u hu) else p₀
      have hwitness (u) (hu : u ∈ G i) : witness u ∈ source ∧
          (witness u).1 ∈ cfg.B k t i ∧ (witness u).2 ∈ I (cfg.T k t) (cfg.j k t i) ∧
          cfg.sourcePair k s ip L (cfg.N k ^ (-t)) δ (witness u) = u := by
        simp only [witness, dif_pos hu]
        exact Classical.choose_spec (hex u hu)
      have hbound := parent.source_child_pair_count h child ip i ht (hD i hi).2
        L M E K δ hM hL hK hδ hrel hδrel hsmall hmesh (G i) witness
        (by
          intro u hu
          have hw := hwitness u hu
          have hs := hsource _ hw.1
          exact ⟨hs.1, hs.2.1, hw.2.1, hw.2.2.1, hs.2.2⟩)
        (fun u hu => (hwitness u hu).2.2.2)
      exact (le_div_iff₀ hδcube).mpr hbound
    · rw [Finset.not_nonempty_iff_eq_empty.mp hGi]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  refine ⟨F, hF, ?_⟩
  have hbudget := occupied_pair_budget_cancel D G F
    (K := cfg.K k ^ 2) (C := 4194304 * K ^ 4)
    (q := cfg.timeLength k t) (qp := cfg.timeLength k s)
    (D := (cfg.N k ^ (-s) / cfg.N k ^ (-t)) ^ cfg.d)
    (ω := δ) (by positivity) (by positivity) hHc hH (by positivity)
    hδ hcount' htotal hlocal
  convert hbudget using 1 <;> ring


end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
