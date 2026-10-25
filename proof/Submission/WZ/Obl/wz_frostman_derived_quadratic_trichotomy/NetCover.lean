-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.NetCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.Overlap

/-!
# One scale of an exact cover for a canonical family

Canonical (left-aligned) δ-tubes whose lines are close in (foot, direction) lie in the ρ-tube
around one of them (`Canonical.lean`). Canonical segments whose directions are close but whose
feet are far apart are far apart (`segment_dist_ge`). Together with `Overlap.lean` this gives one
scale of an exact `S`-cover: a grid in (foot, direction) space, one residue class of cells by
pigeonhole, one representative per cell.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- The component of `y` orthogonal to `v`. -/
noncomputable def perp (v y : Sp) : Sp := y - (inner ℝ y v) • v

lemma norm_perp_le {v : Sp} (hv : ‖v‖ = 1) (y : Sp) : ‖perp v y‖ ≤ ‖y‖ := by
  have h1 : inner ℝ (perp v y) v = 0 := by
    unfold perp
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hv]; ring
  have h2 : y = perp v y + (inner ℝ y v) • v := by unfold perp; abel
  have h3 : ‖y‖ ^ 2 = ‖perp v y‖ ^ 2 + (inner ℝ y v) ^ 2 := by
    conv_lhs => rw [h2]
    rw [norm_add_sq_real, real_inner_smul_right, h1, norm_smul, Real.norm_eq_abs, hv]
    rw [mul_one, sq_abs]; ring
  have h4 : ‖perp v y‖ ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [sq_nonneg (inner ℝ y v)]
  nlinarith [norm_nonneg (perp v y), norm_nonneg y]

lemma perp_add (v y y' : Sp) : perp v (y + y') = perp v y + perp v y' := by
  unfold perp; rw [inner_add_left, add_smul]; abel

lemma perp_sub (v y y' : Sp) : perp v (y - y') = perp v y - perp v y' := by
  unfold perp; rw [inner_sub_left, sub_smul]; abel

lemma perp_smul (v y : Sp) (t : ℝ) : perp v (t • y) = t • perp v y := by
  unfold perp; rw [real_inner_smul_left, smul_sub, smul_smul]

lemma perp_self {v : Sp} (hv : ‖v‖ = 1) : perp v v = 0 := by
  unfold perp; rw [real_inner_self_eq_norm_sq, hv]; simp

lemma perp_of_inner_zero {v p : Sp} (hp : inner ℝ p v = 0) : perp v p = p := by
  unfold perp; rw [hp, zero_smul, sub_zero]

/-- Canonical segments with `e`-close directions and far feet are far apart:
every point of one is at distance at least `‖p - p'‖ - 2 e` from every point of the other. -/
theorem segment_dist_ge {δ e : ℝ} {x v x' v' : Sp} (hδ : 0 < δ) (hv : ‖v‖ = 1)
    (hv' : ‖v'‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1)
    (hT' : Metric.thickening δ (segment ℝ x' (x' + v')) ⊆ Metric.ball (0 : Sp) 1)
    (he : ‖v - v'‖ ≤ e) :
    ∀ a ∈ segment ℝ (leftStart δ x v) (leftStart δ x v + v),
      ∀ a' ∈ segment ℝ (leftStart δ x' v') (leftStart δ x' v' + v'),
        ‖foot x v - foot x' v'‖ - 2 * e ≤ dist a a' := by
  intro a ha a' ha'
  obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_add_iff.1 ha
  obtain ⟨t', ht0', ht1', rfl⟩ := mem_segment_add_iff.1 ha'
  obtain ⟨-, -, hh1', -, -⟩ := chord_bounds hδ hv' hT'
  have hhalf' := half_le_halfChord hδ hv' hT'
  have hp' := norm_foot_le_one hδ hv' hT'
  set p := foot x v
  set p' := foot x' v'
  set h' := halfChord δ x' v'
  have hpv : inner ℝ p v = 0 := inner_foot hv
  have hp'v' : inner ℝ p' v' = 0 := inner_foot hv'
  -- the points, through the feet
  have ea : leftStart δ x v + t • v = p + (t - halfChord δ x v) • v := leftStart_param δ x v t
  have ea' : leftStart δ x' v' + t' • v' = p' + (t' - h') • v' := leftStart_param δ x' v' t'
  -- the orthogonal part of the difference
  have hperp : perp v ((leftStart δ x v + t • v) - (leftStart δ x' v' + t' • v'))
      = (p - perp v p') - (t' - h') • perp v (v' - v) := by
    rw [ea, ea', perp_sub, perp_add, perp_add, perp_smul, perp_smul, perp_self hv,
      perp_of_inner_zero hpv, perp_sub, perp_self hv]
    module
  -- `‖p' - perp v p'‖ = |⟪p', v⟫| ≤ ‖p'‖ e ≤ e`
  have hpp : ‖p' - perp v p'‖ ≤ e := by
    have : p' - perp v p' = (inner ℝ p' v) • v := by unfold perp; abel
    rw [this, norm_smul, hv, mul_one, Real.norm_eq_abs]
    have hi : inner ℝ p' v = inner ℝ p' (v - v') := by
      rw [inner_sub_right, hp'v', sub_zero]
    rw [hi]
    calc |inner ℝ p' (v - v')| ≤ ‖p'‖ * ‖v - v'‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * e := by
          apply mul_le_mul hp' he (norm_nonneg _) zero_le_one
      _ = e := one_mul e
  have hpv' : ‖perp v (v' - v)‖ ≤ e := by
    calc ‖perp v (v' - v)‖ ≤ ‖v' - v‖ := norm_perp_le hv _
      _ = ‖v - v'‖ := norm_sub_rev _ _
      _ ≤ e := he
  have hcoef : |t' - h'| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hlow : ‖p - p'‖ - 2 * e ≤
      ‖(p - perp v p') - (t' - h') • perp v (v' - v)‖ := by
    have e1 : p - p' = ((p - perp v p') - (t' - h') • perp v (v' - v))
        + ((t' - h') • perp v (v' - v) - (p' - perp v p')) := by abel
    have e2 : ‖(t' - h') • perp v (v' - v) - (p' - perp v p')‖ ≤ 2 * e := by
      calc ‖(t' - h') • perp v (v' - v) - (p' - perp v p')‖
          ≤ ‖(t' - h') • perp v (v' - v)‖ + ‖p' - perp v p'‖ := norm_sub_le _ _
        _ = |t' - h'| * ‖perp v (v' - v)‖ + ‖p' - perp v p'‖ := by
            rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * e + e := by
            gcongr
        _ = 2 * e := by ring
    have := norm_add_le ((p - perp v p') - (t' - h') • perp v (v' - v))
      ((t' - h') • perp v (v' - v) - (p' - perp v p'))
    rw [← e1] at this
    linarith
  calc ‖p - p'‖ - 2 * e ≤ ‖(p - perp v p') - (t' - h') • perp v (v' - v)‖ := hlow
    _ = ‖perp v ((leftStart δ x v + t • v) - (leftStart δ x' v' + t' • v'))‖ := by rw [hperp]
    _ ≤ ‖(leftStart δ x v + t • v) - (leftStart δ x' v' + t' • v')‖ := norm_perp_le hv _
    _ = dist (leftStart δ x v + t • v) (leftStart δ x' v' + t' • v') := (dist_eq_norm _ _).symm

/-! ### A grid in (foot, direction) space -/

/-- The cell of a point at grid size `s`. -/
noncomputable def cellIdx (s : ℝ) (y : Sp) : Fin 3 → ℤ := fun c => ⌊y c / s⌋

lemma abs_sub_lt_of_floor_eq {s a b : ℝ} (hs : 0 < s) (h : ⌊a / s⌋ = ⌊b / s⌋) :
    |a - b| < s := by
  have := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hs, div_lt_one hs] at this
  exact this

lemma norm_sub_lt_of_cellIdx_eq {s : ℝ} (hs : 0 < s) {y y' : Sp}
    (h : cellIdx s y = cellIdx s y') : ‖y - y'‖ < 2 * s := by
  have hc : ∀ c, |y c - y' c| < s := fun c => abs_sub_lt_of_floor_eq hs (congrFun h c)
  have hsq : ‖y - y'‖ ^ 2 < (2 * s) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ c, ‖(y - y') c‖ ^ 2 < ∑ _c : Fin 3, s ^ 2 := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro c _
          rw [PiLp.sub_apply, Real.norm_eq_abs]
          have := hc c
          nlinarith [abs_nonneg (y c - y' c)]
      _ = 3 * s ^ 2 := by simp
      _ ≤ (2 * s) ^ 2 := by nlinarith
  nlinarith [norm_nonneg (y - y')]

lemma norm_sub_ge_of_cellIdx_ne {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 1 ≤ M) {y y' : Sp}
    (hmod : ∀ c, cellIdx s y c % (M : ℤ) = cellIdx s y' c % (M : ℤ))
    (hne : cellIdx s y ≠ cellIdx s y') : ((M : ℝ) - 1) * s ≤ ‖y - y'‖ := by
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hne
  have hdvd' : (M : ℤ) ∣ cellIdx s y' c - cellIdx s y c := Int.ModEq.dvd (hmod c)
  have hdvd : (M : ℤ) ∣ cellIdx s y c - cellIdx s y' c := by
    have := dvd_neg.mpr hdvd'
    rwa [neg_sub] at this
  have hge : (M : ℤ) ≤ |cellIdx s y c - cellIdx s y' c| :=
    Int.le_of_dvd (abs_pos.2 (sub_ne_zero.2 hc)) ((dvd_abs _ _).2 hdvd)
  have hreal : (M : ℝ) ≤ |((cellIdx s y c - cellIdx s y' c : ℤ) : ℝ)| := by
    have : ((M : ℤ) : ℝ) ≤ ((|cellIdx s y c - cellIdx s y' c| : ℤ) : ℝ) := by exact_mod_cast hge
    simpa [Int.cast_abs] using this
  have h1 := Int.floor_le (y c / s)
  have h2 := Int.lt_floor_add_one (y c / s)
  have h3 := Int.floor_le (y' c / s)
  have h4 := Int.lt_floor_add_one (y' c / s)
  have hk : ((M : ℝ) - 1) ≤ |y c / s - y' c / s| := by
    simp only [cellIdx, Int.cast_sub] at hreal
    rcases le_abs.mp hreal with h | h
    · rw [le_abs]; left; linarith
    · rw [le_abs]; right; linarith
  have hscale : |y c - y' c| = s * |y c / s - y' c / s| := by
    rw [← abs_of_pos hs, ← abs_mul, abs_of_pos hs]
    congr 1
    field_simp
  calc ((M : ℝ) - 1) * s ≤ |y c / s - y' c / s| * s := by
        exact mul_le_mul_of_nonneg_right hk hs.le
    _ = |y c - y' c| := by rw [hscale]; ring
    _ = ‖(y - y') c‖ := by rw [PiLp.sub_apply, Real.norm_eq_abs]
    _ ≤ ‖y - y'‖ := PiLp.norm_apply_le _ _

/-- The cell of a tube: the cell of its foot and the cell of its direction. -/
noncomputable def lineCell (s : ℝ) (x v : Sp) : (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (cellIdx s (foot x v), cellIdx s v)

/-- Canonical tubes in the same cell: the first lies in the ρ-tube of the second. -/
theorem subset_of_same_cell {δ ρ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hρs : δ + 10 * s ≤ ρ)
    {x v x' v' : Sp} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1)
    (hT' : Metric.thickening δ (segment ℝ x' (x' + v')) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : x = leftStart δ x v) (hcan' : x' = leftStart δ x' v')
    (hcell : lineCell s x v = lineCell s x' v') :
    Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.thickening ρ (segment ℝ x' (x' + v')) := by
  have hp : ‖foot x v - foot x' v'‖ < 2 * s :=
    norm_sub_lt_of_cellIdx_eq hs (congrArg Prod.fst hcell)
  have hvv : ‖v - v'‖ < 2 * s := norm_sub_lt_of_cellIdx_eq hs (congrArg Prod.snd hcell)
  have hL := norm_leftStart_sub_le hδ hv hv' hT hT'
  have hx : x - x' = leftStart δ x v - leftStart δ x' v' := by
    conv_lhs => rw [hcan, hcan']
  have hxx : ‖x - x'‖ ≤ 8 * s := by rw [hx]; linarith
  have hend : ‖(x + v) - (x' + v')‖ ≤ 10 * s := by
    have e : (x + v) - (x' + v') = (x - x') + (v - v') := by abel
    rw [e]
    calc ‖(x - x') + (v - v')‖ ≤ ‖x - x'‖ + ‖v - v'‖ := norm_add_le _ _
      _ ≤ 8 * s + 2 * s := by linarith
      _ = 10 * s := by ring
  have hsub := thickening_segment_subset_of_close (δ := δ) (le_trans hxx (by linarith)) hend
  exact hsub.trans (Metric.thickening_mono hρs _)

/-- Same cell, any thickness: the `τ`-thickening of one canonical segment lies in the
`(τ + 10 s)`-thickening of the other. -/
theorem thick_subset_of_same_cell {δ τ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    {x v x' v' : Sp} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1)
    (hT' : Metric.thickening δ (segment ℝ x' (x' + v')) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : x = leftStart δ x v) (hcan' : x' = leftStart δ x' v')
    (hcell : lineCell s x v = lineCell s x' v') :
    Metric.thickening τ (segment ℝ x (x + v)) ⊆
      Metric.thickening (τ + 10 * s) (segment ℝ x' (x' + v')) := by
  have hp : ‖foot x v - foot x' v'‖ < 2 * s :=
    norm_sub_lt_of_cellIdx_eq hs (congrArg Prod.fst hcell)
  have hvv : ‖v - v'‖ < 2 * s := norm_sub_lt_of_cellIdx_eq hs (congrArg Prod.snd hcell)
  have hL := norm_leftStart_sub_le hδ hv hv' hT hT'
  have hx : x - x' = leftStart δ x v - leftStart δ x' v' := by
    conv_lhs => rw [hcan, hcan']
  have hxx : ‖x - x'‖ ≤ 8 * s := by rw [hx]; linarith
  have hend : ‖(x + v) - (x' + v')‖ ≤ 10 * s := by
    have e : (x + v) - (x' + v') = (x - x') + (v - v') := by abel
    rw [e]
    calc ‖(x - x') + (v - v')‖ ≤ ‖x - x'‖ + ‖v - v'‖ := norm_add_le _ _
      _ ≤ 8 * s + 2 * s := by linarith
      _ = 10 * s := by ring
  exact thickening_segment_subset_of_close (δ := τ) (le_trans hxx (by linarith)) hend

/-- Two canonical tubes in distinct cells of one residue class mod `M` give separated net
tubes, when the grid size is `ρ/20` and `M ≥ 200000`. -/
theorem separated_of_same_class {δ ρ : ℝ} (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 10000)
    {M : ℕ} (hM : 200000 ≤ M) {x v x' v' : Sp} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (hT : Metric.thickening δ (segment ℝ x (x + v)) ⊆ Metric.ball (0 : Sp) 1)
    (hT' : Metric.thickening δ (segment ℝ x' (x' + v')) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : x = leftStart δ x v) (hcan' : x' = leftStart δ x' v') (hanti : 1 ≤ ‖v + v'‖)
    (hclass1 : ∀ c, (lineCell (ρ / 20) x v).1 c % (M : ℤ) = (lineCell (ρ / 20) x' v').1 c % (M : ℤ))
    (hclass2 : ∀ c, (lineCell (ρ / 20) x v).2 c % (M : ℤ) = (lineCell (ρ / 20) x' v').2 c % (M : ℤ))
    (hne : lineCell (ρ / 20) x v ≠ lineCell (ρ / 20) x' v') :
    8000 * ρ ≤ min ‖v - v'‖ ‖v + v'‖ ∨
      ∀ a ∈ segment ℝ x (x + v), ∀ a' ∈ segment ℝ x' (x' + v'), 2 * ρ ≤ dist a a' := by
  have hs : 0 < ρ / 20 := by positivity
  have hM1 : (1 : ℕ) ≤ M := le_trans (by norm_num) hM
  have hMr : (200000 : ℝ) ≤ M := by exact_mod_cast hM
  by_cases hdir : cellIdx (ρ / 20) v = cellIdx (ρ / 20) v'
  · -- same direction cell: the feet are far apart
    right
    have hfoot : cellIdx (ρ / 20) (foot x v) ≠ cellIdx (ρ / 20) (foot x' v') := by
      intro h
      apply hne
      unfold lineCell
      rw [h, hdir]
    have hpfar := norm_sub_ge_of_cellIdx_ne hs hM1 hclass1 hfoot
    have hvv : ‖v - v'‖ ≤ 2 * (ρ / 20) := (norm_sub_lt_of_cellIdx_eq hs hdir).le
    intro a ha a' ha'
    rw [hcan] at ha
    rw [hcan'] at ha'
    have := segment_dist_ge hδ hv hv' hT hT' hvv a ha a' ha'
    have hbig : 2 * ρ ≤ ((M : ℝ) - 1) * (ρ / 20) - 2 * (2 * (ρ / 20)) := by nlinarith
    linarith
  · -- distinct direction cells: transverse
    left
    have hvfar := norm_sub_ge_of_cellIdx_ne hs hM1 hclass2 hdir
    apply le_min
    · nlinarith
    · linarith

/-- One scale of an exact cover for a canonical family. Inside any nonempty index set `U`, a
subset `S` with `|U| ≤ 200000⁶ |S|` and a separated net of unit ρ-tubes exist such that every
tube of `S` lies in some net tube and every net tube contains a tube of `S`. -/
theorem one_scale_cover {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : 2 * δ ≤ ρ) (hρ : ρ ≤ 1 / 10000)
    {n : ℕ} (x v : Fin n → Sp) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (U : Finset (Fin n)) (hU : U.Nonempty) :
    ∃ S ⊆ U, (U.card : ℝ) ≤ (200000 : ℝ) ^ 6 * S.card ∧
      ∃ q : ℕ, ∃ z w : Fin q → Sp, (∀ j, ‖w j‖ = 1) ∧ NetSeparated ρ z w ∧
        (∀ j, ∃ i ∈ S, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j))) ∧
        (∀ i ∈ S, ∃ j, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
          Metric.thickening ρ (segment ℝ (z j) (z j + w j))) := by
  classical
  have hρ0 : 0 < ρ := by linarith
  set s : ℝ := ρ / 20 with hsdef
  have hs : 0 < s := by positivity
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = 200000 := ⟨200000, rfl⟩
  -- the residue class of a tube
  let key : Fin n → (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun i =>
    (fun c => (lineCell s (x i) (v i)).1 c % (M : ℤ), fun c => (lineCell s (x i) (v i)).2 c % (M : ℤ))
  obtain ⟨box, hboxdef⟩ : ∃ box : Finset (Fin 3 → ℤ),
      box = Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) M := ⟨_, rfl⟩
  obtain ⟨t, htdef⟩ : ∃ t : Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)), t = box ×ˢ box := ⟨_, rfl⟩
  have hmaps : ∀ i ∈ U, key i ∈ t := by
    intro i _
    have hM0 : (0 : ℤ) < M := by rw [hMdef]; norm_num
    have hmem : ∀ k : ℤ, k % (M : ℤ) ∈ Finset.Ico (0 : ℤ) M := by
      intro k
      rw [Finset.mem_Ico]
      exact ⟨Int.emod_nonneg _ hM0.ne', Int.emod_lt_of_pos _ hM0⟩
    rw [htdef, hboxdef, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
    exact ⟨fun c => hmem _, fun c => hmem _⟩
  have htcard : (t.card : ℝ) = (200000 : ℝ) ^ 6 := by
    rw [htdef, hboxdef, Finset.card_product, Fintype.card_piFinset, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Int.card_Ico, sub_zero, hMdef]
    norm_num
  have ht : t.Nonempty := by
    obtain ⟨i, hi⟩ := hU
    exact ⟨key i, hmaps i hi⟩
  have htpos : (0 : ℝ) < t.card := by rw [htcard]; positivity
  obtain ⟨y, -, hy⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps ht
    (b := (U.card : ℝ) / t.card) (by
      rw [nsmul_eq_mul, ← mul_div_assoc, mul_div_cancel_left₀ _ htpos.ne'])
  set S := U.filter (fun i => key i = y) with hSdef
  have hSU : S ⊆ U := Finset.filter_subset _ _
  have hScard : (U.card : ℝ) ≤ (200000 : ℝ) ^ 6 * S.card := by
    rw [← htcard]
    have := hy
    rw [div_le_iff₀ htpos] at this
    linarith
  refine ⟨S, hSU, hScard, ?_⟩
  -- the occupied cells and one representative per cell
  set C := S.image (fun i => lineCell s (x i) (v i)) with hCdef
  have hrep : ∀ κ ∈ C, ∃ i ∈ S, lineCell s (x i) (v i) = κ := fun κ hκ => by
    simpa [hCdef] using hκ
  let rep : C → Fin n := fun κ => (hrep κ.1 κ.2).choose
  have hrepS : ∀ κ : C, rep κ ∈ S := fun κ => (hrep κ.1 κ.2).choose_spec.1
  have hrepcell : ∀ κ : C, lineCell s (x (rep κ)) (v (rep κ)) = κ.1 :=
    fun κ => (hrep κ.1 κ.2).choose_spec.2
  let e : C ≃ Fin C.card := C.equivFin
  refine ⟨C.card, fun j => x (rep (e.symm j)), fun j => v (rep (e.symm j)),
    fun j => hv _, ?_, ?_, ?_⟩
  · -- separation
    intro j j' hjj'
    have hne : lineCell s (x (rep (e.symm j))) (v (rep (e.symm j))) ≠
        lineCell s (x (rep (e.symm j'))) (v (rep (e.symm j'))) := by
      rw [hrepcell, hrepcell]
      intro h
      exact hjj' (e.symm.injective (Subtype.ext h))
    have hk1 := (Finset.mem_filter.1 (hrepS (e.symm j))).2
    have hk2 := (Finset.mem_filter.1 (hrepS (e.symm j'))).2
    have hkey : key (rep (e.symm j)) = key (rep (e.symm j')) := hk1.trans hk2.symm
    have hc1 : ∀ c, (lineCell s (x (rep (e.symm j))) (v (rep (e.symm j)))).1 c % (M : ℤ) =
        (lineCell s (x (rep (e.symm j'))) (v (rep (e.symm j')))).1 c % (M : ℤ) :=
      fun c => congrFun (congrArg Prod.fst hkey) c
    have hc2 : ∀ c, (lineCell s (x (rep (e.symm j))) (v (rep (e.symm j)))).2 c % (M : ℤ) =
        (lineCell s (x (rep (e.symm j'))) (v (rep (e.symm j')))).2 c % (M : ℤ) :=
      fun c => congrFun (congrArg Prod.snd hkey) c
    exact separated_of_same_class hδ hρ0 hρ (le_of_eq hMdef.symm) (hv _) (hv _) (hT _) (hT _)
      (hcan _) (hcan _) (hanti _ _) hc1 hc2 hne
  · -- every net tube contains its representative
    intro j
    refine ⟨rep (e.symm j), hrepS _, ?_⟩
    exact Metric.thickening_mono (by linarith) _
  · -- every tube of `S` lies in the net tube of its cell
    intro i hi
    have hiC : lineCell s (x i) (v i) ∈ C := Finset.mem_image_of_mem _ hi
    refine ⟨e ⟨_, hiC⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    apply subset_of_same_cell hδ hs (by rw [hsdef]; linarith) (hv i) (hv _) (hT i) (hT _)
      (hcan i) (hcan _)
    rw [hrepcell]

/-! ### All radii at once -/

/-- A separated net restricted to the tubes it actually uses. -/
theorem restrict_net {δ ρ : ℝ} {n : ℕ} (x v : Fin n → Sp) (S : Finset (Fin n))
    {q : ℕ} (z w : Fin q → Sp) (hw : ∀ j, ‖w j‖ = 1) (hsep : NetSeparated ρ z w)
    (hcov : ∀ i ∈ S, ∃ j, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z j) (z j + w j))) :
    ∃ q' : ℕ, ∃ z' w' : Fin q' → Sp, (∀ j, ‖w' j‖ = 1) ∧ NetSeparated ρ z' w' ∧
      (∀ j, ∃ i ∈ S, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        Metric.thickening ρ (segment ℝ (z' j) (z' j + w' j))) ∧
      (∀ i ∈ S, ∃ j, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        Metric.thickening ρ (segment ℝ (z' j) (z' j + w' j))) := by
  classical
  set used := Finset.univ.filter (fun j : Fin q => ∃ i ∈ S,
    Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.thickening ρ (segment ℝ (z j) (z j + w j))) with hused
  let e : used ≃ Fin used.card := used.equivFin
  refine ⟨used.card, fun j => z (e.symm j).1, fun j => w (e.symm j).1, fun j => hw _, ?_, ?_, ?_⟩
  · intro j j' hjj'
    apply hsep
    intro h
    exact hjj' (e.symm.injective (Subtype.ext h))
  · intro j
    exact (Finset.mem_filter.1 (e.symm j).2).2
  · intro i hi
    obtain ⟨j, hj⟩ := hcov i hi
    have hju : j ∈ used := Finset.mem_filter.2 ⟨Finset.mem_univ _, i, hi, hj⟩
    refine ⟨e ⟨j, hju⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hj

/-- Exact covers at finitely many radii at once: inside any nonempty index set `U` of a
canonical family without antipodal directions there is a subset `S` with
`|U| ≤ (200000⁶)^N |S|` covered, at every radius `ρs k`, by a separated net of unit tubes. -/
theorem multi_scale_cover {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Sp)
    (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖) :
    ∀ (N : ℕ) (ρs : Fin N → ℝ), (∀ k, 2 * δ ≤ ρs k ∧ ρs k ≤ 1 / 10000) →
      ∀ U : Finset (Fin n), U.Nonempty →
      ∃ S ⊆ U, (U.card : ℝ) ≤ ((200000 : ℝ) ^ 6) ^ N * S.card ∧
        ∀ k, ∃ q : ℕ, ∃ z w : Fin q → Sp, (∀ j, ‖w j‖ = 1) ∧ NetSeparated (ρs k) z w ∧
          (∀ i ∈ S, ∃ j, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
            Metric.thickening (ρs k) (segment ℝ (z j) (z j + w j))) := by
  intro N
  induction N with
  | zero =>
    intro ρs hρs U hU
    exact ⟨U, subset_rfl, by simp, fun k => k.elim0⟩
  | succ N ih =>
    intro ρs hρs U hU
    obtain ⟨S', hS'U, hS'card, hS'cov⟩ := ih (fun k => ρs (Fin.castSucc k))
      (fun k => hρs _) U hU
    have hS'ne : S'.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [h, Finset.card_empty, Nat.cast_zero, mul_zero] at hS'card
      have : (0 : ℝ) < U.card := by exact_mod_cast Finset.card_pos.2 hU
      linarith
    obtain ⟨S, hSS', hScard, q, z, w, hw, hsep, -, hcov⟩ :=
      one_scale_cover hδ (hρs (Fin.last N)).1 (hρs (Fin.last N)).2 x v hv hT hcan hanti S' hS'ne
    refine ⟨S, hSS'.trans hS'U, ?_, ?_⟩
    · calc (U.card : ℝ) ≤ ((200000 : ℝ) ^ 6) ^ N * S'.card := hS'card
        _ ≤ ((200000 : ℝ) ^ 6) ^ N * ((200000 : ℝ) ^ 6 * S.card) := by gcongr
        _ = ((200000 : ℝ) ^ 6) ^ (N + 1) * S.card := by ring
    · intro k
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · exact ⟨q, z, w, hw, hsep, hcov⟩
      · obtain ⟨q', z', w', hw', hsep', hcov'⟩ := hS'cov k'
        exact ⟨q', z', w', hw', hsep', fun i hi => hcov' i (hSS' hi)⟩

/-- Exact covers at every radius, in the form of the frozen `S`: for the subset `S` of
`multi_scale_cover`, at every radius the net tubes pairwise overlap in at most half their
volume, every tube of `S` lies in exactly one of them, and every net tube contains a tube of
`S`. -/
theorem multi_scale_exact_cover {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (x v : Fin n → Sp)
    (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : Sp) 1)
    (hcan : ∀ i, x i = leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (N : ℕ) (ρs : Fin N → ℝ) (hρs : ∀ k, 2 * δ ≤ ρs k ∧ ρs k ≤ 1 / 10000)
    (U : Finset (Fin n)) (hU : U.Nonempty) :
    ∃ S ⊆ U, (U.card : ℝ) ≤ ((200000 : ℝ) ^ 6) ^ N * S.card ∧
      ∀ k, ∃ q : ℕ, ∃ z w : Fin q → Sp, (∀ j, ‖w j‖ = 1) ∧
        (∀ j j', j ≠ j' → MeasureTheory.volume
            (Metric.thickening (ρs k) (segment ℝ (z j) (z j + w j)) ∩
              Metric.thickening (ρs k) (segment ℝ (z j') (z j' + w j'))) ≤
            (1 / 2 : ENNReal) *
              MeasureTheory.volume (Metric.thickening (ρs k) (segment ℝ (z j) (z j + w j)))) ∧
        (∀ i ∈ S, ∃! j, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
            Metric.thickening (ρs k) (segment ℝ (z j) (z j + w j))) ∧
        (∀ j, ∃ i ∈ S, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
            Metric.thickening (ρs k) (segment ℝ (z j) (z j + w j))) := by
  obtain ⟨S, hSU, hScard, hcov⟩ := multi_scale_cover hδ x v hv hT hcan hanti N ρs hρs U hU
  refine ⟨S, hSU, hScard, fun k => ?_⟩
  obtain ⟨q, z, w, hw, hsep, hcovk⟩ := hcov k
  obtain ⟨q', z', w', hw', hsep', hused, hcov'⟩ := restrict_net x v S z w hw hsep hcovk
  have hρ0 : 0 < ρs k := by linarith [(hρs k).1]
  refine ⟨q', z', w', hw', fun j j' hjj' => ?_, fun i hi => ?_, hused⟩
  · rcases hsep' j j' hjj' with htr | hfar
    · exact half_overlap_of_transverse hρ0 (by linarith [(hρs k).2]) (hw' j) (hw' j') htr
    · exact half_overlap_of_far hfar
  · obtain ⟨j₀, hj₀⟩ := hcov' i hi
    refine ⟨j₀, hj₀, fun j hj => ?_⟩
    by_contra hne
    rcases hsep' j j₀ hne with htr | hfar
    · have h1 := direction_near_of_subset hδ (hv i) (hw' j) hj
      have h2 := direction_near_of_subset hδ (hv i) (hw' j₀) hj₀
      have := min_dir_triangle (v := v i) (w := w' j) (w' := w' j₀)
      linarith
    · obtain ⟨⟨θ1, h01, h11, hd1⟩, -⟩ := endpoints_near_of_subset hδ hj
      obtain ⟨⟨θ2, h02, h12, hd2⟩, -⟩ := endpoints_near_of_subset hδ hj₀
      have := hfar (z' j + θ1 • w' j) (mem_segment_add_iff.2 ⟨θ1, h01, h11, rfl⟩)
        (z' j₀ + θ2 • w' j₀) (mem_segment_add_iff.2 ⟨θ2, h02, h12, rfl⟩)
      have := dist_triangle_left (z' j + θ1 • w' j) (z' j₀ + θ2 • w' j₀) (x i)
      linarith

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
