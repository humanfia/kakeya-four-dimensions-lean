-- Adapted from this LOT tree, o107/x0734, Submission/Obl/k4_finite_narrowness_path_improvement/TangentWindowSchedule.lean; namespace renamed.
import Mathlib
import Submission.Obl.k4_finite_positive_mixed_cover_realization.Grid

/-! The geometric schedule for the original-law entropy window.
Any monotone downward rounding to a sufficiently fine original grid
gives a fixed-band parent, intermediate level, and deeper endpoint. -/

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- All levels concern the same original grid. The model interval of
length `u` ends before the intermediate graph level. -/
structure TangentWindows (m : ℕ) (s : ℕ → ℝ) (D u mesh : ℝ) where
  count : ℕ
  count_pos : 0 < count
  count_lower : (1/(32*D))/u ≤ (count : ℝ)
  level : ℕ → ℕ
  middle : ℕ → ℕ
  monotone : Monotone level
  level_lt : ∀ i, level i < m
  parent_band : ∀ i, 1/8 ≤ s (level i) ∧ s (level i) ≤ 1/4
  between : ∀ i, i < count → level i ≤ middle i ∧ middle i ≤ level (i+1)
  middle_lt : ∀ i, i < count → middle i < m
  model_room : ∀ i, i < count → s (level i)+u ≤ s (middle i)
  first_gap : ∀ i, i < count → |s (middle i)-s (level i)-D*u/2| ≤ mesh
  second_gap : ∀ i, i < count → |s (level (i+1))-s (middle i)-D*u/2| ≤ mesh
  full_gap : ∀ i, i < count → |s (level (i+1))-s (level i)-D*u| ≤ mesh

/-- Every model level up to the parent depth plus `u` precedes the
intermediate graph level of the same original window. -/
theorem TangentWindows.model_level_le_middle
    {m : ℕ} {s : ℕ → ℝ} {D u mesh : ℝ} (q : TangentWindows m s D u mesh)
    (hstrict : ∀ i j, i < j → j < m → s i < s j)
    {i j : ℕ} (hi : i < q.count) (hj : j < m)
    (hsj : s j ≤ s (q.level i)+u) : j ≤ q.middle i := by
  by_contra hn
  have hmid : q.middle i < j := lt_of_not_ge hn
  exact (not_lt_of_ge (hsj.trans (q.model_room i hi))) (hstrict _ _ hmid hj)

/-- Round equally spaced target levels in `[5/32,7/32]` down to the
original grid. The window count is at least `1/(32*D*u)`. No original
measure, chart count, coefficient budget, or sample enters this choice. -/
theorem exists_tangent_windows
    (m : ℕ) (s : ℕ → ℝ) (round : ℝ → ℕ) (hround_mono : Monotone round)
    (D u mesh : ℝ) (hD : 4 ≤ D) (hu : 0 < u) (hsmall : D*u ≤ 1/64)
    (hmesh : mesh ≤ u)
    (hround : ∀ x : ℝ, 5/32 ≤ x → x ≤ 7/32 →
      round x < m ∧ s (round x) ≤ x ∧ x ≤ s (round x)+mesh) :
    Nonempty (TangentWindows m s D u mesh) := by
  classical
  let w := D*u
  let a := 1/(16*w)
  let J := ⌊a⌋₊
  have hD0 : 0 < D := by linarith
  have hw : 0 < w := mul_pos hD0 hu
  have ha : 0 < a := by dsimp [a]; positivity
  have ha4 : 4 ≤ a := by
    apply (le_div_iff₀ (show 0 < 16*w by positivity)).mpr
    dsimp only [w]
    nlinarith [hsmall]
  have hJle : (J : ℝ) ≤ a := Nat.floor_le ha.le
  have hJlt : a < (J : ℝ)+1 := Nat.lt_floor_add_one a
  have hJhalf : a/2 ≤ (J : ℝ) := by linarith
  have hJ0 : 0 < J := by
    have : (0 : ℝ) < J := by linarith
    exact_mod_cast this
  have hJw : (J : ℝ)*w ≤ 1/16 := by
    have h := (le_div_iff₀ (show 0 < 16*w by positivity)).mp hJle
    nlinarith
  have hu1 : u ≤ 1/64 := by nlinarith [hsmall]
  let target : ℕ → ℝ := fun i => 5/32+(min i J : ℕ)*w
  let level : ℕ → ℕ := fun i => round (target i)
  let middle : ℕ → ℕ := fun i => round (target i+w/2)
  have htarget (i : ℕ) : 5/32 ≤ target i ∧ target i ≤ 7/32 := by
    have hmin0 : (0 : ℝ) ≤ (min i J : ℕ) := Nat.cast_nonneg _
    have hminJ : ((min i J : ℕ) : ℝ) ≤ J := by exact_mod_cast min_le_right i J
    have hmul := mul_le_mul_of_nonneg_right hminJ hw.le
    dsimp only [target]
    constructor <;> nlinarith
  have hr (i : ℕ) := hround (target i) (htarget i).1 (htarget i).2
  have hstep (i : ℕ) (hi : i < J) : target (i+1) = target i+w := by
    simp only [target,min_eq_left (Nat.succ_le_of_lt hi),min_eq_left hi.le,
      Nat.cast_add,Nat.cast_one,Nat.cast_succ]
    ring
  have hm_target (i : ℕ) (hi : i < J) : 5/32 ≤ target i+w/2 ∧ target i+w/2 ≤ 7/32 := by
    have hnext := (htarget (i+1)).2
    rw [hstep i hi] at hnext
    constructor <;> linarith [(htarget i).1]
  have hm (i : ℕ) (hi : i < J) :=
    hround (target i+w/2) (hm_target i hi).1 (hm_target i hi).2
  have hfirst (i : ℕ) (hi : i < J) :
      |s (middle i)-s (level i)-w/2| ≤ mesh := by
    have h0 := hr i
    have h1 := hm i hi
    rw [abs_le]
    constructor <;> linarith [h0.2.1,h0.2.2,h1.2.1,h1.2.2]
  have hsecond (i : ℕ) (hi : i < J) :
      |s (level (i+1))-s (middle i)-w/2| ≤ mesh := by
    have h0 := hm i hi
    have h1 := hr (i+1)
    rw [hstep i hi] at h1
    dsimp only [level,middle]
    rw [hstep i hi,abs_le]
    constructor <;> linarith [h0.2.1,h0.2.2,h1.2.1,h1.2.2]
  refine ⟨{ count := J, count_pos := hJ0, count_lower := ?_, level := level, middle := middle, monotone := ?_, level_lt := fun i => (hr i).1, parent_band := ?_, between := ?_, middle_lt := fun i hi => (hm i hi).1, model_room := ?_, first_gap := hfirst, second_gap := hsecond, full_gap := ?_ }⟩
  · have heq : (1/(32*D))/u = a/2 := by
      dsimp [a,w]
      field_simp
      ring
    exact heq.symm ▸ hJhalf
  · intro i j hij
    apply hround_mono
    have hmin : ((min i J : ℕ) : ℝ) ≤ (min j J : ℕ) := by
      exact_mod_cast min_le_min hij (le_refl J)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hmin hw.le)
  · intro i
    have h := hr i
    constructor
    · linarith [(htarget i).1,h.2.2]
    · exact h.2.1.trans ((htarget i).2.trans (by norm_num))
  · intro i hi
    constructor
    · exact hround_mono (by linarith : target i ≤ target i+w/2)
    · apply hround_mono
      rw [hstep i hi]
      linarith
  · intro i hi
    have h := (abs_le.mp (hfirst i hi)).1
    dsimp only [w] at h
    nlinarith
  · intro i hi
    have h0 := hr i
    have h1 := hr (i+1)
    rw [hstep i hi] at h1
    change |s (round (target (i+1)))-s (round (target i))-w| ≤ mesh
    rw [hstep i hi,abs_le]
    constructor <;> linarith [h0.2.1,h0.2.2,h1.2.1,h1.2.2]

/-- The accepted original fine-grid predecessor supplies the entire
schedule. Its mesh estimate is imported, while taking the maximum
available predecessor makes the rounding monotone. -/
theorem exists_tangent_windows_of_grid
    {m : ℕ} {s : ℕ → ℝ} {gain ρ D u : ℝ}
    (hs : Submission.Obl.k4_finite_positive_mixed_cover_realization.FineGrid m s gain ρ)
    (hD : 4 ≤ D) (hu : 0 < u) (hsmall : D*u ≤ 1/64)
    (hmesh0 : 0 ≤ ρ*gain) (hmesh : ρ*gain ≤ u) :
    Nonempty (TangentWindows m s D u (ρ*gain)) := by
  classical
  have hstrict : StrictMonoOn s (Set.Iio m) := by
    apply strictMonoOn_of_lt_add_one Set.ordConnected_Iio
    intro i _ hi hnext
    exact hs.1.2.2.1 i hnext
  let cells (x : ℝ) := (Finset.range m).filter (fun i => s i ≤ x)
  let round (x : ℝ) := (cells x).sup id
  have hmono : Monotone round := by
    intro x y hxy
    apply Finset.sup_mono
    intro i hi
    obtain ⟨hi,hsi⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi,hsi.trans hxy⟩
  apply exists_tangent_windows m s round hmono D u (ρ*gain) hD hu hsmall hmesh
  intro x hx0 hx1
  have hu1 : u ≤ 1/64 := by nlinarith
  obtain ⟨j,hj,hjx,hxj⟩ := hs.predecessor hmesh0
    (show s 0 ≤ x by linarith [hs.2.1]) (hx1.trans (by norm_num))
  have hjmem : j ∈ cells x := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hjx⟩
  obtain ⟨k,hk,heq⟩ := Finset.exists_mem_eq_sup (cells x) ⟨j,hjmem⟩ id
  have heq' : round x = k := heq
  have hmem : round x ∈ cells x := heq'.symm ▸ hk
  obtain ⟨hindex,hsx⟩ := Finset.mem_filter.mp hmem
  have hg : round x < m := Finset.mem_range.mp hindex
  refine ⟨hg,hsx,?_⟩
  have hjr : j ≤ round x := Finset.le_sup (f := id) hjmem
  exact hxj.trans (add_le_add (hstrict.monotoneOn hj hg hjr) le_rfl)

end

end Submission.Obl.k4_finite_affine_parent_sources
