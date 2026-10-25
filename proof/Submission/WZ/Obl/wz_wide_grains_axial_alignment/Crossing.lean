-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_wide_grains_axial_alignment.Crossing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Crossing geometry for the frozen prisms

A convex set that meets the frontier of a frozen box `P a b c z e` only on its two long ends, and
reaches both long ends inside the box (the crossing clause of `G`/`H`), stays strictly inside the
lateral walls at every height of the box. Consequently it meets a laterally widened box only
inside the original one, and it crosses the widened box too.
-/

open LeanEval.Analysis.WangZahlKakeya Set Metric

namespace WangZahlLot.Obl.wz_wide_grains_axial_alignment

/-- The frozen box `P a b c z e` (with `ι` the coordinates). -/
def box (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) : Set Space :=
  {p | |(e (p - z)) 0| ≤ a / 2 ∧ |(e (p - z)) 1| ≤ b / 2 ∧ |(e (p - z)) 2| ≤ c / 2}

theorem continuous_coord (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (k : Fin 3) :
    Continuous fun p : Space => (e (p - z)) k :=
  (PiLp.continuous_apply 2 (fun _ => ℝ) k).comp (e.continuous.comp (continuous_sub_right z))

theorem isClosed_box (a b c : ℝ) (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) :
    IsClosed (box a b c z e) := by
  exact (isClosed_le (continuous_coord z e 0).abs continuous_const).inter
    ((isClosed_le (continuous_coord z e 1).abs continuous_const).inter
      (isClosed_le (continuous_coord z e 2).abs continuous_const))

/-- Coordinates along an affine combination. -/
theorem coord_lineMap (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (p p' : Space) (t : ℝ) (k : Fin 3) :
    (e (p + t • (p' - p) - z)) k = (e (p - z)) k + t * ((e (p' - z)) k - (e (p - z)) k) := by
  have h : p + t • (p' - p) - z = (p - z) + t • ((p' - z) - (p - z)) := by
    simp only [sub_sub_sub_cancel_right]; abel
  rw [h, map_add, map_smul, map_sub]
  simp

/-- Moving along `e.symm (single k 1)` shifts the `k`-th coordinate. -/
theorem coord_shift (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) (p : Space) (s : ℝ) (k j : Fin 3) :
    (e (p + s • e.symm (EuclideanSpace.single k 1) - z)) j =
      (e (p - z)) j + if j = k then s else 0 := by
  have h : p + s • e.symm (EuclideanSpace.single k 1) - z =
      (p - z) + s • e.symm (EuclideanSpace.single k 1) := by abel
  rw [h, map_add, map_smul, LinearIsometryEquiv.apply_symm_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk]

/-- A point of the box whose `k`-th coordinate (k = 0 or 1, i.e. any coordinate) sits on the
boundary value is not interior. -/
theorem not_mem_interior_box {a b c : ℝ} {z : Space} {e : Space ≃ₗᵢ[ℝ] Space} {r : Space}
    {k : Fin 3} {w : ℝ}
    (hk : ∀ p ∈ box a b c z e, |(e (p - z)) k| ≤ w / 2) (hr : |(e (r - z)) k| = w / 2) :
    r ∉ interior (box a b c z e) := by
  intro hint
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hint
  obtain ⟨ε, hε, hball⟩ := hint
  set σ : ℝ := if 0 ≤ (e (r - z)) k then 1 else -1 with hσ
  set r' := r + (ε / 2 * σ) • e.symm (EuclideanSpace.single k 1) with hr'
  have hσabs : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
  have hdist : dist r' r < ε := by
    rw [hr', dist_eq_norm, add_sub_cancel_left, norm_smul, LinearIsometryEquiv.norm_map,
      PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_mul, hσabs, mul_one,
      abs_of_pos (by positivity)]
    linarith
  have hmem := hk r' (hball (mem_ball.mpr hdist))
  rw [hr', coord_shift] at hmem
  simp only [ite_true] at hmem
  have : |(e (r - z)) k + ε / 2 * σ| = |(e (r - z)) k| + ε / 2 := by
    rw [hσ]
    split_ifs with h0
    · rw [mul_one, abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    · have h0' : (e (r - z)) k < 0 := lt_of_not_ge h0
      rw [abs_of_neg h0', abs_of_neg (by linarith)]; ring
  rw [this, hr] at hmem
  linarith

/-- **Crossing keeps the tube inside the lateral walls.** If a convex set `K` meets the
frontier of the box only on its two long ends, and reaches both long ends inside the box,
then every point of `K` at an interior height lies strictly inside the two lateral bounds. -/
theorem lateral_lt_of_crossing {a b c : ℝ} {z : Space} {e : Space ≃ₗᵢ[ℝ] Space} {K : Set Space}
    (hK : Convex ℝ K)
    (hfront : ∀ p ∈ K ∩ frontier (box a b c z e), |(e (p - z)) 2| = c / 2)
    (hfaces : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ), ∃ p ∈ K ∩ box a b c z e, (e (p - z)) 2 = t)
    {p : Space} (hp : p ∈ K) (hp2 : |(e (p - z)) 2| < c / 2) :
    |(e (p - z)) 0| < a / 2 ∧ |(e (p - z)) 1| < b / 2 := by
  have hc : 0 < c := by linarith [abs_nonneg ((e (p - z)) 2)]
  obtain ⟨p₁, ⟨hp₁K, hp₁U⟩, hp₁2⟩ := hfaces (-c / 2) (by simp)
  obtain ⟨p₂, ⟨hp₂K, hp₂U⟩, hp₂2⟩ := hfaces (c / 2) (by simp)
  set s := (e (p - z)) 2 with hs
  have hs' := abs_lt.mp hp2
  set l : ℝ := (s + c / 2) / c with hl
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hc.le
  have hl1 : l ≤ 1 := (div_le_one hc).mpr (by linarith)
  -- the point of the chord `[p₁, p₂]` at height `s`
  set p' := p₁ + l • (p₂ - p₁) with hp'
  have hp'K : p' ∈ K := by
    have := hK hp₁K hp₂K (sub_nonneg.mpr hl1) hl0 (by ring : (1 - l) + l = 1)
    convert this using 1
    rw [hp', smul_sub, sub_smul, one_smul]; abel
  have hq : ∀ k, (e (p' - z)) k = (e (p₁ - z)) k + l * ((e (p₂ - z)) k - (e (p₁ - z)) k) :=
    fun k => coord_lineMap z e p₁ p₂ l k
  have hp'2 : (e (p' - z)) 2 = s := by
    rw [hq, hp₁2, hp₂2, hl]; field_simp; ring
  have hcomb : ∀ k (w : ℝ), |(e (p₁ - z)) k| ≤ w / 2 → |(e (p₂ - z)) k| ≤ w / 2 →
      |(e (p' - z)) k| ≤ w / 2 := by
    intro k w h1 h2
    rw [hq]
    have : (e (p₁ - z)) k + l * ((e (p₂ - z)) k - (e (p₁ - z)) k) =
        (1 - l) * (e (p₁ - z)) k + l * (e (p₂ - z)) k := by ring
    rw [this]
    calc |(1 - l) * (e (p₁ - z)) k + l * (e (p₂ - z)) k|
        ≤ |(1 - l) * (e (p₁ - z)) k| + |l * (e (p₂ - z)) k| := abs_add_le _ _
      _ = (1 - l) * |(e (p₁ - z)) k| + l * |(e (p₂ - z)) k| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hl1), abs_of_nonneg hl0]
      _ ≤ (1 - l) * (w / 2) + l * (w / 2) := by gcongr
      _ = w / 2 := by ring
  have hp'0 := hcomb 0 a hp₁U.1 hp₂U.1
  have hp'1 := hcomb 1 b hp₁U.2.1 hp₂U.2.1
  by_contra hcon
  -- the segment from `p'` to `p` leaves the lateral walls: find the exit point
  set γ : ℝ → Space := fun t => p' + t • (p - p') with hγ
  set g : ℝ → ℝ := fun t =>
    max (|(e (γ t - z)) 0| - a / 2) (|(e (γ t - z)) 1| - b / 2) with hg
  have hγq : ∀ t k, (e (γ t - z)) k = (e (p' - z)) k + t * ((e (p - z)) k - (e (p' - z)) k) :=
    fun t k => coord_lineMap z e p' p t k
  have hgc : Continuous g := by
    have hc' : ∀ k, Continuous fun t => (e (γ t - z)) k := by
      intro k; simp_rw [hγq]; fun_prop
    exact ((hc' 0).abs.sub continuous_const).max ((hc' 1).abs.sub continuous_const)
  have hg0 : g 0 ≤ 0 := by
    simp only [hg, hγ, zero_smul, add_zero]
    exact max_le (by linarith) (by linarith)
  have hg1 : 0 ≤ g 1 := by
    simp only [hg, hγ, one_smul, add_sub_cancel]
    rcases not_and_or.mp hcon with h | h
    · exact le_max_of_le_left (by linarith [not_lt.mp h])
    · exact le_max_of_le_right (by linarith [not_lt.mp h])
  obtain ⟨t, ⟨ht0, ht1⟩, hgt⟩ :=
    intermediate_value_Icc zero_le_one hgc.continuousOn ⟨hg0, hg1⟩
  have hγK : γ t ∈ K := by
    have := hK hp'K hp (sub_nonneg.mpr ht1) ht0 (by ring : (1 - t) + t = 1)
    convert this using 1
    simp only [hγ, smul_sub, sub_smul, one_smul]; abel
  have hγ2 : (e (γ t - z)) 2 = s := by rw [hγq, hp'2]; ring
  have hle : g t ≤ 0 := hgt.le
  have hγ0 : |(e (γ t - z)) 0| ≤ a / 2 := by
    have := le_max_left (|(e (γ t - z)) 0| - a / 2) (|(e (γ t - z)) 1| - b / 2)
    simp only [hg] at hle; linarith
  have hγ1 : |(e (γ t - z)) 1| ≤ b / 2 := by
    have := le_max_right (|(e (γ t - z)) 0| - a / 2) (|(e (γ t - z)) 1| - b / 2)
    simp only [hg] at hle; linarith
  have hγU : γ t ∈ box a b c z e := ⟨hγ0, hγ1, by rw [hγ2]; exact hp2.le⟩
  have hγfr : γ t ∈ frontier (box a b c z e) := by
    rw [(isClosed_box a b c z e).frontier_eq]
    refine ⟨hγU, ?_⟩
    simp only [hg] at hgt
    rcases max_eq_iff.mp hgt with ⟨h, -⟩ | ⟨h, -⟩
    · exact not_mem_interior_box (k := 0) (w := a) (fun q hq => hq.1) (by linarith)
    · exact not_mem_interior_box (k := 1) (w := b) (fun q hq => hq.2.1) (by linarith)
  have := hfront (γ t) ⟨hγK, hγfr⟩
  rw [hγ2] at this
  linarith


/-- The strict box lies in the interior of the box. -/
theorem strict_subset_interior_box {a b c : ℝ} {z : Space} {e : Space ≃ₗᵢ[ℝ] Space} {p : Space}
    (h0 : |(e (p - z)) 0| < a / 2) (h1 : |(e (p - z)) 1| < b / 2) (h2 : |(e (p - z)) 2| < c / 2) :
    p ∈ interior (box a b c z e) := by
  have hopen : IsOpen {p : Space | |(e (p - z)) 0| < a / 2 ∧ |(e (p - z)) 1| < b / 2 ∧
      |(e (p - z)) 2| < c / 2} :=
    (isOpen_lt (continuous_coord z e 0).abs continuous_const).inter
      ((isOpen_lt (continuous_coord z e 1).abs continuous_const).inter
        (isOpen_lt (continuous_coord z e 2).abs continuous_const))
  refine interior_maximal ?_ hopen ⟨h0, h1, h2⟩
  intro q hq
  exact ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩

/-- The crossing conclusion up to the long ends, for an open convex crossing set. -/
theorem lateral_lt_of_crossing' {a b c : ℝ} {z : Space} {e : Space ≃ₗᵢ[ℝ] Space} {K : Set Space}
    (hK : Convex ℝ K) (hKo : IsOpen K) (hc : 0 < c)
    (hfront : ∀ p ∈ K ∩ frontier (box a b c z e), |(e (p - z)) 2| = c / 2)
    (hfaces : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ), ∃ p ∈ K ∩ box a b c z e, (e (p - z)) 2 = t)
    {p : Space} (hp : p ∈ K) (hp2 : |(e (p - z)) 2| ≤ c / 2) :
    |(e (p - z)) 0| < a / 2 ∧ |(e (p - z)) 1| < b / 2 := by
  rcases hp2.lt_or_eq with hlt | heq
  · exact lateral_lt_of_crossing hK hfront hfaces hp hlt
  · -- push `p` slightly towards the middle along the long axis
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hKo p hp
    set t : ℝ := min (ε / 2) (c / 2) with ht
    have ht0 : 0 < t := lt_min (by positivity) (by positivity)
    have htc : t ≤ c / 2 := min_le_right _ _
    have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    set σ : ℝ := if 0 ≤ (e (p - z)) 2 then 1 else -1 with hσ
    have hσabs : |σ| = 1 := by rw [hσ]; split_ifs <;> simp
    set p' := p + (-(t * σ)) • e.symm (EuclideanSpace.single 2 1) with hp'
    have hp'K : p' ∈ K := by
      apply hball
      rw [mem_ball, hp', dist_eq_norm, add_sub_cancel_left, norm_smul,
        LinearIsometryEquiv.norm_map, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
        abs_neg, abs_mul, hσabs, mul_one, abs_of_pos ht0]
      exact htε
    have hq : ∀ j, (e (p' - z)) j = (e (p - z)) j + if j = 2 then -(t * σ) else 0 :=
      fun j => coord_shift z e p _ 2 j
    have h2 : |(e (p' - z)) 2| < c / 2 := by
      rw [hq]; simp only [ite_true]
      rw [hσ]
      split_ifs with h0
      · rw [abs_of_nonneg h0] at heq
        rw [mul_one, heq, abs_of_nonneg (by linarith)]; linarith
      · have h0' : (e (p - z)) 2 < 0 := lt_of_not_ge h0
        rw [abs_of_neg h0'] at heq
        rw [abs_of_nonpos (by linarith)]; linarith
    have := lateral_lt_of_crossing hK hfront hfaces hp'K h2
    rw [hq, hq] at this
    simpa using this

/-- **Widening.** If an open convex set crosses `box a b c z e`, it meets the wider box
`box a b' c z e` (`b ≤ b'`) only inside the original one, and it crosses the wider box. -/
theorem crossing_widen {a b b' c : ℝ} {z : Space} {e : Space ≃ₗᵢ[ℝ] Space} {K : Set Space}
    (hK : Convex ℝ K) (hKo : IsOpen K) (hc : 0 < c) (hbb : b ≤ b')
    (hfront : ∀ p ∈ K ∩ frontier (box a b c z e), |(e (p - z)) 2| = c / 2)
    (hfaces : ∀ t ∈ ({-c / 2, c / 2} : Set ℝ), ∃ p ∈ K ∩ box a b c z e, (e (p - z)) 2 = t) :
    K ∩ box a b' c z e ⊆ box a b c z e ∧
      (∀ p ∈ K ∩ frontier (box a b' c z e), |(e (p - z)) 2| = c / 2) ∧
      (∀ t ∈ ({-c / 2, c / 2} : Set ℝ), ∃ p ∈ K ∩ box a b' c z e, (e (p - z)) 2 = t) := by
  have hsub : box a b c z e ⊆ box a b' c z e := by
    intro p hp
    exact ⟨hp.1, hp.2.1.trans (by linarith), hp.2.2⟩
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun t ht => ?_⟩
  · have := lateral_lt_of_crossing' hK hKo hc hfront hfaces hp.1 hp.2.2.2
    exact ⟨this.1.le, this.2.le, hp.2.2.2⟩
  · have hpU : p ∈ box a b' c z e := (isClosed_box a b' c z e).frontier_subset hp.2
    by_contra hne
    have hlt : |(e (p - z)) 2| < c / 2 := lt_of_le_of_ne hpU.2.2 hne
    have := lateral_lt_of_crossing' hK hKo hc hfront hfaces hp.1 hlt.le
    have hint := strict_subset_interior_box (b := b') this.1 (lt_of_lt_of_le this.2 (by linarith)) hlt
    exact hp.2.2 hint
  · obtain ⟨p, hp, hpt⟩ := hfaces t ht
    exact ⟨p, ⟨hp.1, hsub hp.2⟩, hpt⟩

end WangZahlLot.Obl.wz_wide_grains_axial_alignment
