-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.TSCoarse.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSSelect
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TSGeometry
import Submission.WZ.Obl.wz_multiscale_c2_extraction.Coarse.TopScale

/-!
# Coarse families as exact frozen families

The covers of one level of a separated family, contracted about the origin and
re-extended, form the tubes of a coarse family. This file proves the geometric
inputs: nested covers, the tree property of separated levels, and bounded
conflict degrees.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open Set Metric MeasureTheory
open scoped ENNReal Pointwise Classical
open WangZahlLot.Obl.wz_separated_cover_refinement (Tube Dilate dilate_param)

theorem mem_Dilate_of_param {r : ℝ} {z w p : Space} {t : ℝ}
    (ht : t ∈ Icc (-(9 / 2) : ℝ) (11 / 2)) (hp : ‖p - (z + t • w)‖ < 10 * r) :
    p ∈ Dilate r z w := by
  apply mem_thickening_iff.mpr
  refine ⟨z + t • w, ?_, ?_⟩
  · rw [segment_eq_image']
    refine ⟨(t + 9 / 2) / 10, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    module
  · rwa [dist_eq_norm]

/-- Fine tubes sharing a coarse tube lie in the dilate of the cover of either. -/
theorem subset_dilate_of_same_coarse {δ ρ ρ'' : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hρρ : ρ ≤ ρ'') {x v x' v' z w z'' w'' : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h1 : Tube δ x v ⊆ Tube ρ z w) (h2 : Tube δ x' v' ⊆ Tube ρ z w)
    (h3 : Tube δ x v ⊆ Tube ρ'' z'' w'') : Tube δ x' v' ⊆ Dilate ρ'' z'' w'' := by
  intro q hq
  obtain ⟨t, ht, hqt⟩ := exists_param_of_mem_Tube hq
  obtain ⟨s, hs, hts⟩ := axis_mem_of_subset hδ h2 ht
  obtain ⟨s', hs', hss'⟩ := axis_close_of_subset hδ hv hw h1 hs
  obtain ⟨s'', hs'', hs's''⟩ := axis_mem_of_subset hδ h3 hs'
  apply mem_Dilate_of_param (t := s'') ⟨by linarith [hs''.1], by linarith [hs''.2]⟩
  have he : q - (z'' + s'' • w'') = (q - (x' + t • v')) + ((x' + t • v') - (z + s • w)) +
      ((z + s • w) - (x + s' • v)) + ((x + s' • v) - (z'' + s'' • w'')) := by abel
  rw [he]
  calc ‖(q - (x' + t • v')) + ((x' + t • v') - (z + s • w)) +
        ((z + s • w) - (x + s' • v)) + ((x + s' • v) - (z'' + s'' • w''))‖ ≤
        ‖q - (x' + t • v')‖ + ‖(x' + t • v') - (z + s • w)‖ +
          ‖(z + s • w) - (x + s' • v)‖ + ‖(x + s' • v) - (z'' + s'' • w'')‖ :=
        (norm_add_le _ _).trans (by
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _))
    _ < δ + ρ + 3 * ρ + ρ'' := by
        have := hss'
        linarith
    _ ≤ 10 * ρ'' := by linarith

/-- Pointwise closeness of a coarse axis to a cover axis at a coarser level. -/
theorem coarse_axis_close {δ ρ ρ'' : ℝ} (hδ : 0 < δ) {x v z w z'' w'' : Space}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h1 : Tube δ x v ⊆ Tube ρ z w) (h3 : Tube δ x v ⊆ Tube ρ'' z'' w'') :
    ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
      ‖(z + t • w) - (z'' + s • w'')‖ ≤ ρ'' + 3 * ρ := by
  intro t ht
  obtain ⟨s', hs', h⟩ := axis_close_of_subset hδ hv hw h1 ht
  obtain ⟨s, hs, h'⟩ := axis_mem_of_subset hδ h3 hs'
  refine ⟨s, hs, ?_⟩
  have he : (z + t • w) - (z'' + s • w'') =
      ((z + t • w) - (x + s' • v)) + ((x + s' • v) - (z'' + s • w'')) := by abel
  rw [he]
  calc _ ≤ ‖(z + t • w) - (x + s' • v)‖ + ‖(x + s' • v) - (z'' + s • w'')‖ := norm_add_le _ _
    _ ≤ 3 * ρ + ρ'' := by linarith
    _ = ρ'' + 3 * ρ := by ring

/-- Axes of covers containing a fine tube of the unit ball stay in the ball of radius 2. -/
theorem cover_axis_norm_le {δ ρ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : ρ ≤ 1 / 3)
    {x v z w : Space} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hball : Tube δ x v ⊆ ball 0 1) (h1 : Tube δ x v ⊆ Tube ρ z w) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖z + t • w‖ ≤ 1 + 3 * ρ := by
  intro t ht
  obtain ⟨s, hs, h⟩ := axis_close_of_subset hδ hv hw h1 ht
  have hn := axis_norm_le hδ hδ1 hball hs
  calc ‖z + t • w‖ ≤ ‖(z + t • w) - (x + s • v)‖ + ‖x + s • v‖ := by
        have := norm_add_le ((z + t • w) - (x + s • v)) (x + s • v)
        simpa using this
    _ ≤ 3 * ρ + (1 - δ) := add_le_add h hn
    _ ≤ 1 + 3 * ρ := by linarith

/-- A normalized axis point is close to a point of the original line. -/
theorem norm_base_sub {e : ℝ} (z w : Space) (σ : ℝ) :
    ‖((1 - 2 * e) • z - e • w + σ • w) - (z + (σ - e) • w)‖ = |2 * e| * ‖z‖ := by
  have he : ((1 - 2 * e) • z - e • w + σ • w) - (z + (σ - e) • w) = (-(2 * e)) • z := by
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg]

/-- From closeness of normalized axes to containment of an original tube in a
container around another original axis. -/
theorem tube_subset_bigContainer_of_close {e ρ0 D : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1 / 4)
    (hρ0 : 0 < ρ0) {zA wA zB wB : Space} (hA : ‖zA‖ ≤ 2)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖zB + t • wB‖ ≤ 2)
    (hclose : ∀ τ ∈ Icc (0 : ℝ) 1, ∃ σ : ℝ, |σ| ≤ 25 ∧
      ‖((1 - 2 * e) • zB - e • wB + τ • wB) - ((1 - 2 * e) • zA - e • wA + σ • wA)‖ ≤ D)
    (hD : D + 8 * e + ρ0 < 1000000000 * ρ0) :
    Tube ρ0 zB wB ⊆ bigContainer ρ0 zA wA := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := exists_param_of_mem_Tube hp
  set τ := (1 - 2 * e) * t + e
  have hτ : τ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [τ]; nlinarith [ht.1]
    · dsimp [τ]; nlinarith [ht.2]
  obtain ⟨σ, hσ, hd⟩ := hclose τ hτ
  have hBτ : (1 - 2 * e) • zB - e • wB + τ • wB = (1 - 2 * e) • (zB + t • wB) := by
    dsimp [τ]; module
  apply mem_bigContainer (t := σ - e)
  · rw [abs_le] at hσ ⊢
    constructor <;> linarith [hσ.1, hσ.2]
  · have hsplit : p - (zA + (σ - e) • wA) = (p - (zB + t • wB)) +
        ((zB + t • wB) - ((1 - 2 * e) • zB - e • wB + τ • wB)) +
        (((1 - 2 * e) • zB - e • wB + τ • wB) - ((1 - 2 * e) • zA - e • wA + σ • wA)) +
        (((1 - 2 * e) • zA - e • wA + σ • wA) - (zA + (σ - e) • wA)) := by abel
    rw [hsplit]
    have h2 : ‖(zB + t • wB) - ((1 - 2 * e) • zB - e • wB + τ • wB)‖ ≤ 4 * e := by
      rw [hBτ]
      have he' : (zB + t • wB) - (1 - 2 * e) • (zB + t • wB) = (2 * e) • (zB + t • wB) := by
        module
      rw [he', norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      nlinarith [hB t ht, norm_nonneg (zB + t • wB)]
    have h4 : ‖((1 - 2 * e) • zA - e • wA + σ • wA) - (zA + (σ - e) • wA)‖ ≤ 4 * e := by
      rw [norm_base_sub, abs_of_nonneg (by linarith)]
      nlinarith [norm_nonneg zA]
    calc _ ≤ ‖p - (zB + t • wB)‖ +
          ‖(zB + t • wB) - ((1 - 2 * e) • zB - e • wB + τ • wB)‖ +
          ‖((1 - 2 * e) • zB - e • wB + τ • wB) - ((1 - 2 * e) • zA - e • wA + σ • wA)‖ +
          ‖((1 - 2 * e) • zA - e • wA + σ • wA) - (zA + (σ - e) • wA)‖ :=
          (norm_add_le _ _).trans (by
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _))
      _ < ρ0 + 4 * e + D + 4 * e := by linarith
      _ < 1000000000 * ρ0 := by linarith

/-- Heavy overlap of normalized tubes, in either direction, puts the second
original tube in the container of the first. -/
theorem overlap_container {r e ρ0 : ℝ} (hr : 0 < r) (hr1 : r ≤ 1 / 10000000) (he : 0 ≤ e)
    (he1 : e ≤ 1 / 4) (hρ0 : 0 < ρ0) (hrρ : r ≤ 100 * ρ0) (heρ : e ≤ 100 * ρ0)
    {zA wA zB wB : Space} (hwA : ‖wA‖ = 1) (hwB : ‖wB‖ = 1) (hA : ‖zA‖ ≤ 2)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖zB + t • wB‖ ≤ 2)
    (hov : (1 / 2 : ℝ≥0∞) * volume (ntube r e zA wA) <
        volume (ntube r e zA wA ∩ ntube r e zB wB) ∨
      (1 / 2 : ℝ≥0∞) * volume (ntube r e zB wB) <
        volume (ntube r e zB wB ∩ ntube r e zA wA)) :
    Tube ρ0 zB wB ⊆ bigContainer ρ0 zA wA := by
  have hR : r ≤ 1 / 10000 := by linarith
  apply tube_subset_bigContainer_of_close he he1 hρ0 hA hB (D := 1000000 * r)
  · rcases hov with hov | hov
    · have hc := overlap_axis_close hr hR hwA hwB hov
      intro τ hτ
      obtain ⟨σ, hσ, hd⟩ := hc τ hτ
      refine ⟨σ, ?_, ?_⟩
      · rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
      · linarith
    · have hc := overlap_axis_close hr hR hwB hwA hov
      intro τ hτ
      obtain ⟨σ0, hσ0, hd0⟩ := hc 0 ⟨le_rfl, zero_le_one⟩
      obtain ⟨σ1, hσ1, hd1⟩ := hc 1 ⟨zero_le_one, le_rfl⟩
      simp only [zero_smul, add_zero, one_smul] at hd0 hd1
      have hD : 10000 * r ≤ 1 / 100 := by linarith
      have hpos : (0 : ℝ) < 10000 * r := by positivity
      obtain ⟨σ, hσ, hd⟩ := lines_close_of_common_segment hD
        (p0 := (1 - 2 * e) • zA - e • wA) (v := wA)
        (z := (1 - 2 * e) • zA - e • wA) (w := wA)
        (z' := (1 - 2 * e) • zB - e • wB) (w' := wB) hwA hwA hwB
        (a := 0) (b := 1) (a' := σ0) (b' := σ1) (by simp)
        (by rw [abs_le]; constructor <;> linarith [hσ0.1, hσ0.2])
        (by simpa using hpos) (by simpa using hpos)
        hd0 hd1 hτ
      exact ⟨σ, hσ, by linarith⟩
  · linarith

/-- Two normalized dilates containing both ends of a unit segment put the second
original tube in the container of the first. -/
theorem dilate_conflict_container {R e ρ0 : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 1000)
    (he : 0 ≤ e) (he1 : e ≤ 1 / 4) (hρ0 : 0 < ρ0) (hRρ : R ≤ 100 * ρ0)
    (heρ : e ≤ 100 * ρ0) {zA wA zB wB p0 v : Space} (hv : ‖v‖ = 1) (hwA : ‖wA‖ = 1)
    (hwB : ‖wB‖ = 1) (hA : ‖zA‖ ≤ 2) (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖zB + t • wB‖ ≤ 2)
    (h0A : p0 ∈ Dilate R ((1 - 2 * e) • zA - e • wA) wA)
    (h1A : p0 + v ∈ Dilate R ((1 - 2 * e) • zA - e • wA) wA)
    (h0B : p0 ∈ Dilate R ((1 - 2 * e) • zB - e • wB) wB)
    (h1B : p0 + v ∈ Dilate R ((1 - 2 * e) • zB - e • wB) wB) :
    Tube ρ0 zB wB ⊆ bigContainer ρ0 zA wA := by
  obtain ⟨a, ha, hda⟩ := dilate_param h0A
  obtain ⟨b, -, hdb⟩ := dilate_param h1A
  obtain ⟨a', ha', hda'⟩ := dilate_param h0B
  obtain ⟨b', -, hdb'⟩ := dilate_param h1B
  have hD : 10 * R ≤ 1 / 100 := by linarith
  apply tube_subset_bigContainer_of_close he he1 hρ0 hA hB (D := 100 * (10 * R))
  · intro τ hτ
    exact lines_close_of_common_segment hD hv hwA hwB
      (by linarith) (by linarith) hda hdb hda' hdb' hτ
  · linarith

/-! ### Conflict relations and their degrees -/

/-- Element conflicts: heavy overlap of normalized coarse tubes in either direction. -/
def elemConflict {k : ℕ} (r e : ℝ) (z w : Fin k → Space) (j j' : Fin k) : Prop :=
  j ≠ j' ∧ ((1 / 2 : ℝ≥0∞) * volume (ntube r e (z j) (w j)) <
      volume (ntube r e (z j) (w j) ∩ ntube r e (z j') (w j')) ∨
    (1 / 2 : ℝ≥0∞) * volume (ntube r e (z j') (w j')) <
      volume (ntube r e (z j') (w j') ∩ ntube r e (z j) (w j)))

theorem elemConflict_symm {k : ℕ} {r e : ℝ} {z w : Fin k → Space} {j j' : Fin k}
    (h : elemConflict r e z w j j') : elemConflict r e z w j' j :=
  ⟨Ne.symm h.1, h.2.symm⟩

/-- Cover conflicts: heavy overlap of normalized covers, or a coarse tube in both
of their dilates. -/
def coverConflict {k k'' : ℕ} (r e R : ℝ) (z w : Fin k → Space) (z'' w'' : Fin k'' → Space)
    (m m' : Fin k'') : Prop :=
  m ≠ m' ∧ ((1 / 2 : ℝ≥0∞) * volume (ntube R e (z'' m) (w'' m)) <
      volume (ntube R e (z'' m) (w'' m) ∩ ntube R e (z'' m') (w'' m')) ∨
    (1 / 2 : ℝ≥0∞) * volume (ntube R e (z'' m') (w'' m')) <
      volume (ntube R e (z'' m') (w'' m') ∩ ntube R e (z'' m) (w'' m)) ∨
    ∃ j, ntube r e (z j) (w j) ⊆ Dilate R ((1 - 2 * e) • z'' m - e • w'' m) (w'' m) ∧
      ntube r e (z j) (w j) ⊆ Dilate R ((1 - 2 * e) • z'' m' - e • w'' m') (w'' m'))

theorem coverConflict_symm {k k'' : ℕ} {r e R : ℝ} {z w : Fin k → Space}
    {z'' w'' : Fin k'' → Space} {m m' : Fin k''}
    (h : coverConflict r e R z w z'' w'' m m') : coverConflict r e R z w z'' w'' m' m := by
  obtain ⟨hne, h1 | h2 | ⟨j, hj, hj'⟩⟩ := h
  · exact ⟨Ne.symm hne, Or.inr (Or.inl h1)⟩
  · exact ⟨Ne.symm hne, Or.inl h2⟩
  · exact ⟨Ne.symm hne, Or.inr (Or.inr ⟨j, hj', hj⟩)⟩

/-- Element conflicts have bounded degree. -/
theorem elemConflict_card_le {k : ℕ} {ρ e : ℝ} (hρ : 0 < ρ) (h8ρ : 8 * ρ ≤ 1 / 10000000)
    (he : 0 ≤ e) (he1 : e ≤ 1 / 4) (heρ : e ≤ 100 * ρ) (z w : Fin k → Space)
    (hw : ∀ j, ‖w j‖ = 1) (hz : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, ‖z j + t • w j‖ ≤ 2)
    (hsep : ∀ j j', j ≠ j' → volume (Tube ρ (z j) (w j) ∩ Tube ρ (z j') (w j')) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube ρ (z j) (w j))) (j : Fin k) :
    (Finset.univ.filter (elemConflict (8 * ρ) e z w j)).card ≤ bigBound := by
  classical
  apply card_le_of_subset_bigContainer hρ (by linarith) z w hw hsep (z j) (w j) (hw j)
  intro j' hj'
  have hc := (Finset.mem_filter.mp hj').2
  have hzj : ‖z j‖ ≤ 2 := by simpa using hz j 0 ⟨le_rfl, zero_le_one⟩
  exact overlap_container (by positivity) h8ρ he he1 hρ (by linarith) heρ (hw j) (hw j')
    hzj (hz j') hc.2

/-- Cover conflicts have bounded degree. -/
theorem coverConflict_card_le {k k'' : ℕ} {ρ ρ'' e : ℝ} (hρ : 0 < ρ) (hρρ : ρ ≤ ρ'')
    (hρ'' : ρ'' ≤ 1 / 1000000000) (he : 0 ≤ e) (heρ : e ≤ 16 * ρ)
    (z w : Fin k → Space) (z'' w'' : Fin k'' → Space)
    (hw : ∀ j, ‖w j‖ = 1) (hw'' : ∀ m, ‖w'' m‖ = 1)
    (hz'' : ∀ m, ∀ t ∈ Icc (0 : ℝ) 1, ‖z'' m + t • w'' m‖ ≤ 2)
    (hsep'' : ∀ m m', m ≠ m' → volume (Tube ρ'' (z'' m) (w'' m) ∩ Tube ρ'' (z'' m') (w'' m')) ≤
      (1 / 2 : ℝ≥0∞) * volume (Tube ρ'' (z'' m) (w'' m))) (m : Fin k'') :
    (Finset.univ.filter
      (coverConflict (8 * ρ) e (ρ'' + 27 * ρ) z w z'' w'' m)).card ≤ bigBound := by
  classical
  have hρ''0 : 0 < ρ'' := lt_of_lt_of_le hρ hρρ
  apply card_le_of_subset_bigContainer hρ''0 (by linarith) z'' w'' hw'' hsep'' (z'' m) (w'' m)
    (hw'' m)
  intro m' hm'
  have hc := (Finset.mem_filter.mp hm').2
  have hzm : ‖z'' m‖ ≤ 2 := by simpa using hz'' m 0 ⟨le_rfl, zero_le_one⟩
  have hR : 0 < ρ'' + 27 * ρ := by positivity
  obtain ⟨-, h1 | h2 | ⟨j, hj, hj'⟩⟩ := hc
  · exact overlap_container hR (by linarith) he (by linarith) hρ''0 (by linarith) (by linarith)
      (hw'' m) (hw'' m') hzm (hz'' m') (Or.inl h1)
  · exact overlap_container hR (by linarith) he (by linarith) hρ''0 (by linarith) (by linarith)
      (hw'' m) (hw'' m') hzm (hz'' m') (Or.inr h2)
  · have h8 : 0 < 8 * ρ := by positivity
    have hp0 := axis_mem_Tube h8 ((1 - 2 * e) • z j - e • w j) (w j) (t := 0)
      ⟨le_rfl, zero_le_one⟩
    have hp1 := axis_mem_Tube h8 ((1 - 2 * e) • z j - e • w j) (w j) (t := 1)
      ⟨zero_le_one, le_rfl⟩
    simp only [zero_smul, add_zero, one_smul] at hp0 hp1
    exact dilate_conflict_container hR (by linarith) he (by linarith) hρ''0 (by linarith)
      (by linarith) (hw j) (hw'' m) (hw'' m') hzm (hz'' m')
      (hj hp0) (hj hp1) (hj' hp0) (hj' hp1)

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
