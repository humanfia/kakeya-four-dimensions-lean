-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.StripSaturation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/StripSaturation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/StripSaturation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/StripSaturation.lean.
-- Existing source attributions are preserved below.

import Submission.Lib.K4VelocityStrips.StripFamily

/-!
Saturate an arbitrary family by finitely many sets which were heavy under
the original law. Every remaining set then has small absolute original
mass. No conditional probability or finite indexing assumption is used.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips

/-- A finite union of originally heavy sets leaves at most `θ` of the
original mass in ANY member of the family. The family may be uncountable. -/
theorem finite_original_heavy_cover {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (F : I → Set X)
    (hF : ∀ i, MeasurableSet (F i)) {θ : ℝ} (hθ : 0 < θ) :
    ∃ s : Finset I, (∀ i ∈ s, θ ≤ μ.real (F i)) ∧
      ∀ i, μ.real (F i \ ⋃ j ∈ s, F j) ≤ θ := by
  classical
  let unionSet (s : Finset I) := ⋃ i ∈ s, F i
  let masses : Set ℝ := {v | ∃ s : Finset I,
    (∀ i ∈ s, θ ≤ μ.real (F i)) ∧ v = μ.real (unionSet s)}
  have hne : masses.Nonempty := ⟨0, ∅, by simp, by simp [unionSet]⟩
  have hbound : BddAbove masses := by
    refine ⟨μ.real univ, ?_⟩
    rintro v ⟨s, _, rfl⟩
    exact measureReal_mono (subset_univ _)
  obtain ⟨v, ⟨s, hs, rfl⟩, hnear⟩ := exists_lt_of_lt_csSup hne
    (show sSup masses - θ < sSup masses by linarith)
  refine ⟨s, hs, ?_⟩
  intro i
  by_cases hi : θ ≤ μ.real (F i)
  · have hins : μ.real (unionSet (insert i s)) ≤ sSup masses :=
      le_csSup hbound ⟨insert i s, by simpa using And.intro hi hs, rfl⟩
    have hU : MeasurableSet (unionSet s) := by
      exact Finset.measurableSet_biUnion s (fun j _ => hF j)
    have hadd : μ.real (unionSet (insert i s)) =
        μ.real (unionSet s) + μ.real (F i \ unionSet s) := by
      have heq : unionSet (insert i s) = unionSet s ∪ (F i \ unionSet s) := by
        have hinsert : unionSet (insert i s) = F i ∪ unionSet s := by simp [unionSet]
        rw [hinsert]
        ext x
        by_cases hx : x ∈ unionSet s <;> simp [hx]
      rw [heq, measureReal_union disjoint_sdiff_right (hF i |>.diff hU)
        (measure_ne_top μ _) (measure_ne_top μ _)]
    change μ.real (F i \ unionSet s) ≤ θ
    linarith
  · exact (measureReal_mono sdiff_subset).trans (le_of_not_ge hi)

/-- A uniformly short saturation family, with each prediction heavy under
the ORIGINAL law. Its cardinal bound is the total original mass divided
by the absolute threshold; in particular it is constant for probability
laws at a fixed threshold. -/
theorem bounded_original_heavy_cover {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (F : I → Set X)
    (hF : ∀ i, MeasurableSet (F i)) {θ : ℝ} (hθ : 0 < θ) :
    ∃ s : Finset I, (s.card : ℝ) ≤ μ.real univ / θ ∧
      (∀ i ∈ s, θ < μ.real (F i)) ∧
      ∀ i, μ.real (F i \ ⋃ j ∈ s, F j) ≤ θ := by
  classical
  let unionSet (s : Finset I) := ⋃ i ∈ s, F i
  let P (n : ℕ) := ∃ s : Finset I, s.card = n ∧
    (∀ i ∈ s, θ < μ.real (F i)) ∧ (n : ℝ) * θ ≤ μ.real (unionSet s)
  let bound : ℕ := ⌈μ.real univ / θ⌉₊
  have hP0 : P 0 := ⟨∅, by simp, by simp, by simp [unionSet]⟩
  have hbound (n : ℕ) (hn : P n) : n ≤ bound := by
    obtain ⟨s, _, _, hmass⟩ := hn
    have hraw : (n : ℝ) ≤ μ.real univ / θ := (le_div_iff₀ hθ).mpr
      (hmass.trans (measureReal_mono (subset_univ _)))
    exact_mod_cast hraw.trans (Nat.le_ceil (μ.real univ / θ))
  let n := Nat.findGreatest P bound
  have hPn : P n := Nat.findGreatest_spec (Nat.zero_le bound) hP0
  obtain ⟨s, hcard, hs, hmass⟩ := hPn
  refine ⟨s, ?_, hs, ?_⟩
  · rw [hcard]
    exact (le_div_iff₀ hθ).mpr (hmass.trans (measureReal_mono (subset_univ _)))
  · intro i
    by_contra hbad
    have hbad' : θ < μ.real (F i \ unionSet s) := lt_of_not_ge hbad
    have hi : i ∉ s := by
      intro hi
      have hsub : F i ⊆ unionSet s := fun x hx => mem_iUnion₂.mpr ⟨i, hi, hx⟩
      rw [sdiff_eq_empty.mpr hsub] at hbad'
      simp only [measureReal_empty] at hbad'
      linarith
    have hU : MeasurableSet (unionSet s) := Finset.measurableSet_biUnion s (fun j _ => hF j)
    have hadd : μ.real (unionSet (insert i s)) =
        μ.real (unionSet s) + μ.real (F i \ unionSet s) := by
      have heq : unionSet (insert i s) = unionSet s ∪ (F i \ unionSet s) := by
        have hinsert : unionSet (insert i s) = F i ∪ unionSet s := by simp [unionSet]
        rw [hinsert]
        ext x
        by_cases hx : x ∈ unionSet s <;> simp [hx]
      rw [heq, measureReal_union disjoint_sdiff_right ((hF i).diff hU)
        (measure_ne_top μ _) (measure_ne_top μ _)]
    have hnew : P (n + 1) := by
      refine ⟨insert i s, by rw [Finset.card_insert_of_notMem hi, hcard], ?_, ?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hbad'.trans_le (measureReal_mono sdiff_subset)
        · exact hs j hj
      · rw [hadd]
        push_cast
        linarith
    have hmax : n + 1 ≤ n := Nat.le_findGreatest (hbound (n + 1) hnew) hnew
    omega

/-- One finite net of originally heavy strips leaves small original mass
in every thin strip. Its cardinal bound is independent of the entire
continuum of strip parameters. Both choices of normal sign are included. -/
theorem exists_saturating_original_strip_net
    (μ : Measure StripSpace) [IsProbabilityMeasure μ]
    {θ ε r ρ T : ℝ} (hθ : 0 < θ) (hε : 0 ≤ ε)
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hsmall : 4 * r ≤ ρ)
    (hcap : ∀ x : StripSpace,
      μ (Metric.closedBall x (32 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ θ ^ 2) :
    ∃ s : Finset (StripSpace × ℝ), (s.card : ℝ) ≤ 2 / θ ^ 2 ∧
      (∀ p ∈ s, ‖p.1‖ = 1 ∧ θ ≤ μ.real (boundedStrip p.1 p.2 r T)) ∧
      ∀ n b, ‖n‖ = 1 →
        μ.real (boundedStrip n b r T \
          ⋃ p ∈ s, boundedStrip p.1 p.2 (r + (1 + T) * ρ) T) ≤ θ := by
  classical
  let I := {p : StripSpace × ℝ // ‖p.1‖ = 1}
  let strip (i : I) := boundedStrip i.1.1 i.1.2 r T
  obtain ⟨s, hs, hres⟩ := finite_original_heavy_cover μ strip
    (fun i => measurableSet_boundedStrip _ _ _ _) hθ
  let normal (i : s) := i.1.1.1
  let offset (i : s) := i.1.1.2
  obtain ⟨t, ht, _, hcover⟩ := exists_short_heavy_strip_net μ normal offset
    (fun i => i.1.2) hθ hε hT hρ hsmall (fun i => hs i.1 i.2) hcap heps
  let out := t.image (fun i => (normal i, offset i))
  refine ⟨out, ?_, ?_, ?_⟩
  · exact (by exact_mod_cast Finset.card_image_le : (out.card : ℝ) ≤ t.card).trans ht
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨i.1.2, hs i.1 i.2⟩
  · intro n b hn
    have hsub : (⋃ i ∈ s, strip i) ⊆
        ⋃ p ∈ out, boundedStrip p.1 p.2 (r + (1 + T) * ρ) T := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      obtain ⟨j, hj, hnear⟩ := hcover ⟨i, hi⟩
      refine mem_iUnion₂.mpr ⟨(normal j, offset j), Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
      exact ⟨hxi.1, affineStrip_mem_of_close_parameters_mod_sign hT
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hxi.1)
        (hnear.imp le_of_lt le_of_lt) hxi.2⟩
    exact (measureReal_mono (by
      intro x hx
      exact ⟨hx.1, fun h => hx.2 (hsub h)⟩)).trans (hres ⟨(n, b), hn⟩)

/-- A single finite net covers EVERY strip which was heavy under the
original law, pointwise after enlargement. This stronger coverage permits
later binwise-dominated laws; no full measure domination is assumed. -/
theorem exists_universal_original_heavy_strip_net
    (μ : Measure StripSpace) [IsProbabilityMeasure μ]
    {θ ε r ρ T : ℝ} (hθ : 0 < θ) (hε : 0 ≤ ε)
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hsmall : 8 * r ≤ ρ)
    (hcap : ∀ x : StripSpace,
      μ (Metric.closedBall x (64 * (1 + T) * r / ρ)) ≤ ENNReal.ofReal ε)
    (heps : 2 * ε ≤ θ ^ 2) :
    ∃ s : Finset (StripSpace × ℝ), (s.card : ℝ) ≤ 2 / θ ^ 2 ∧
      (∀ p ∈ s, ‖p.1‖ = 1 ∧ θ ≤ μ.real (boundedStrip p.1 p.2 r T)) ∧
      ∀ n b, ‖n‖ = 1 → θ ≤ μ.real (boundedStrip n b r T) →
        ∃ p ∈ s, boundedStrip n b r T ⊆
          boundedStrip p.1 p.2 (r + (1 + T) * ρ) T := by
  classical
  let H : Set (StripSpace × ℝ) :=
    {p | ‖p.1‖ = 1 ∧ θ ≤ μ.real (boundedStrip p.1 p.2 r T)}
  have hbounded : H ⊆ Metric.closedBall 0 (max 1 (T + |r|)) := by
    intro p hp
    have hpos : 0 < μ.real (boundedStrip p.1 p.2 r T) := hθ.trans_le hp.2
    have hne : (boundedStrip p.1 p.2 r T).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h] at hpos
      simpa using hpos
    obtain ⟨x, hx⟩ := hne
    have hxnorm : ‖x‖ ≤ T := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
    have hb : |p.2| ≤ T + |r| := by
      calc
        _ = |inner ℝ x p.1 - (inner ℝ x p.1 - p.2)| := by ring_nf
        _ ≤ |inner ℝ x p.1| + |inner ℝ x p.1 - p.2| := abs_sub _ _
        _ ≤ ‖x‖ * ‖p.1‖ + r := add_le_add (abs_real_inner_le_norm _ _) hx.2
        _ ≤ T + |r| := by rw [hp.1, mul_one]; linarith [le_abs_self r]
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, hp.1]
    exact max_le_max le_rfl hb
  have htb : TotallyBounded H := (isCompact_closedBall
    (0 : StripSpace × ℝ) (max 1 (T + |r|))).totallyBounded.subset hbounded
  obtain ⟨rawSet, hrawH, hrawfin, hrawcover⟩ :=
    Metric.finite_approx_of_totallyBounded htb (ρ / 4) (by positivity)
  let raw := hrawfin.toFinset
  let normal (i : raw) := i.1.1
  let offset (i : raw) := i.1.2
  have hraw (i : raw) : (i : StripSpace × ℝ) ∈ H := hrawH
    (by simpa only [raw, Set.Finite.mem_toFinset] using i.2)
  obtain ⟨net, hnet, _, hcover⟩ := exists_short_heavy_strip_net μ normal offset
    (fun i => (hraw i).1) hθ hε hT (show 0 < ρ / 2 by positivity)
    (show 4 * r ≤ ρ / 2 by linarith) (fun i => (hraw i).2) (fun x => by
      convert hcap x using 2 <;> field_simp <;> ring) heps
  let out := net.image (fun i => (normal i, offset i))
  refine ⟨out, ?_, ?_, ?_⟩
  · exact (by exact_mod_cast Finset.card_image_le : (out.card : ℝ) ≤ net.card).trans hnet
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hraw i
  · intro n b hn hmass
    obtain ⟨q, hq, hdist⟩ := mem_iUnion₂.mp (hrawcover (show (n, b) ∈ H from ⟨hn, hmass⟩))
    have hqin : q ∈ raw := by simpa only [raw, Set.Finite.mem_toFinset] using hq
    obtain ⟨j, hj, hclose⟩ := hcover ⟨q, hqin⟩
    refine ⟨(normal j, offset j), Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
    have hfirst : ‖n - q.1‖ + |b - q.2| ≤ ρ / 2 := by
      rw [Metric.mem_ball, Prod.dist_eq] at hdist
      have h1 := (le_max_left (dist n q.1) (dist b q.2)).trans_lt hdist
      have h2 := (le_max_right (dist n q.1) (dist b q.2)).trans_lt hdist
      rw [dist_eq_norm] at h1
      rw [Real.dist_eq] at h2
      linarith
    intro x hx
    have hxnorm : ‖x‖ ≤ T := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1
    refine ⟨hx.1, ?_⟩
    have hmid := affineStrip_mem_of_close_parameters hT hxnorm hfirst hx.2
    have hlast := affineStrip_mem_of_close_parameters_mod_sign hT hxnorm
      (hclose.imp le_of_lt le_of_lt) hmid
    convert hlast using 1 <;> ring

/-- A pointwise universal heavy-strip cover transfers to any later law
using only the stated strip-mass implication. After deletion, every thin
strip has small ABSOLUTE mass under that same later law. -/
theorem strip_cap_outside_universal_cover
    (μ ν : Measure StripSpace) [IsFiniteMeasure ν]
    (U : Set StripSpace) {r rOld T θ θOld : ℝ} (hθ : 0 ≤ θ) (hr : r ≤ rOld)
    (hdetect : ∀ n b, ‖n‖ = 1 → θ < ν.real (boundedStrip n b r T) →
      θOld ≤ μ.real (boundedStrip n b rOld T))
    (hcover : ∀ n b, ‖n‖ = 1 → θOld ≤ μ.real (boundedStrip n b rOld T) →
      boundedStrip n b rOld T ⊆ U) :
    ∀ n b, ‖n‖ = 1 → ν.real (boundedStrip n b r T \ U) ≤ θ := by
  intro n b hn
  by_cases hsmall : ν.real (boundedStrip n b r T) ≤ θ
  · exact (measureReal_mono sdiff_subset).trans hsmall
  · have hU := hcover n b hn (hdetect n b hn (lt_of_not_ge hsmall))
    have hsub : boundedStrip n b r T ⊆ U := by
      intro x hx
      exact hU ⟨hx.1, hx.2.trans hr⟩
    rw [sdiff_eq_empty.mpr hsub]
    simpa using hθ

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
