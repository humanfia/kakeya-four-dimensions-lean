/- Adapted from this LOT tree o255, session x0901, branch x0901 at 7ca74bdb,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/RowField.lean.
   Earlier provenance comments in the source are retained. -/
import Submission.Obl.k4_narrow_projected_row_parents.RowApply
import Submission.Obl.k4_narrow_projected_row_parents.RowOptions
import Submission.Obl.k4_narrow_projected_row_parents.WitnessBins

/-!
# The row field of deep labels

A *listed parent* is a true parent `Q` at depth `r` with a retained set `W` of
its incidences and short lists, per zoomed horizontal cell and velocity bin,
of the bins of width `E₁` of the zoomed transverse velocity (the output of the
comparison of true and projected labels in the narrow case).

Deep labels at a depth `r' > r` inside `Q` carry rows
`T = ((c₃' - c₃) / g_r, (c₄' - c₄) / g_r)` predicting the zoomed transverse
velocity to `K g_{r'} / g_r`.  After pruning (deep label, cell) states that
are light relative to their full assignments, every retained state has
witness velocity bins of palette mass at least `δ / K`, and the rows at a
cell occupy few bins: a listed parent becomes row-ready.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_general_parent_projected_layers Submission.Obl.k4_general_parent_projected_layers.PreparedModel Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- A parent with short transverse-velocity lists. -/
structure ParentLists (p : Parameters) (a : PreparedModel α) (k : ℕ) (r ξ E₁ M : ℝ) where
  /-- the parent label -/
  Q : Fin (a.n k r)
  /-- retained incidences -/
  W : Set (α × ℝ)
  measurable_W : MeasurableSet W
  W_sub : W ⊆ a.B k r Q ×ˢ a.block k r Q
  measurable_A : MeasurableSet (a.A k r Q)
  B_sub_A : a.B k r Q ⊆ a.A k r Q
  prior_ne : a.nu k (a.A k r Q) ≠ 0
  mass : ENNReal.ofReal (a.q k r / M) * a.nu k (a.A k r Q) ≤ a.rho k W
  pos_bound : ∀ z ∈ W, |(parentZoom p a k r Q).coeff (a.b k z.1) 0| ≤ M
  vel_bound : ∀ z ∈ W, |a.b k z.1 3| ≤ M
  yv_bound : ∀ z ∈ W, |(parentZoom p a k r Q).coeff (a.b k z.1) 4| ≤ M
  /-- the lists -/
  L : (Fin 2 → ℤ) → ℤ → Finset ℤ
  L_card : ∀ c w, ((L c w).card : ℝ) ≤ M
  L_mem : ∀ z ∈ W, ⌊(parentZoom p a k r Q).coeff (a.b k z.1) 4 / E₁⌋ ∈
    L (hcell (parentZoom p a k r Q) ξ (a.b k z.1) z.2) ⌊a.b k z.1 3 / ξ⌋
  joint_cap : ∀ (c : Fin 2 → ℤ) (v₀ : ℤ),
    a.rho k {z | z ∈ W ∧ hcell (parentZoom p a k r Q) ξ (a.b k z.1) z.2 = c ∧
        ⌊a.b k z.1 3 / ξ⌋ = v₀} ≤
      ENNReal.ofReal (M * ξ ^ 2) * a.pi k (Ico ((v₀ : ℝ) * ξ) (((v₀ : ℝ) + 1) * ξ)) *
        (ENNReal.ofReal (a.q k r) * a.nu k (a.A k r Q))

/-- The row of a deep label `n` at depth `r'` relative to the parent `Q` at depth `r`. -/
def deepRow (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ) (Q : Fin (a.n k r))
    (r' : ℝ) (n : Fin (a.n k r')) : Fin 2 → ℝ :=
  ![(a.c k r' n 3 - a.c k r Q 3) / narrow p k r, (a.c k r' n 4 - a.c k r Q 4) / narrow p k r]

/-- A deep row predicts the zoomed transverse velocity of the deep label's lines. -/
theorem deepRow_predict (p : Parameters) (hp : p.Valid) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) (r' : ℝ) (n : Fin (a.n k r')) (b : Fin 6 → ℝ) {e : ℝ}
    (hslope : |b 4 - a.c k r' n 3 - a.c k r' n 4 * b 3| ≤ e) :
    |deepRow p a k r Q r' n 0 + b 3 * deepRow p a k r Q r' n 1 -
        (parentZoom p a k r Q).coeff b 4| ≤ e / narrow p k r := by
  have hg := narrow_pos p hp k r
  have hq := q_pos a k r
  rw [Zoom.coeff_four]
  simp only [deepRow, parentZoom, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  have hid : (a.c k r' n 3 - a.c k r Q 3) / narrow p k r +
      b 3 * ((a.c k r' n 4 - a.c k r Q 4) / narrow p k r) -
      a.q k r * (b 4 - a.c k r Q 3 - a.c k r Q 4 * b 3) / (a.q k r * narrow p k r) =
      -(b 4 - a.c k r' n 3 - a.c k r' n 4 * b 3) / narrow p k r := by
    field_simp
    ring
  rw [hid, abs_div, abs_neg, abs_of_pos hg]
  exact div_le_div_of_nonneg_right hslope hg.le

theorem floor_sub_le_one {x x₀ ξ : ℝ} (hξ : 0 < ξ) (h : |x - x₀| ≤ ξ) :
    |⌊x / ξ⌋ - ⌊x₀ / ξ⌋| ≤ 1 := by
  have h1 : |x / ξ - x₀ / ξ| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hξ, div_le_one hξ]; exact h
  rw [abs_le] at h1 ⊢
  have a1 := Int.floor_le (x / ξ)
  have a2 := Int.lt_floor_add_one (x / ξ)
  have a3 := Int.floor_le (x₀ / ξ)
  have a4 := Int.lt_floor_add_one (x₀ / ξ)
  constructor
  · have : ((⌊x₀ / ξ⌋ : ℤ) : ℝ) - ⌊x / ξ⌋ < 2 := by linarith
    have : ⌊x₀ / ξ⌋ - ⌊x / ξ⌋ < 2 := by exact_mod_cast this
    omega
  · have : ((⌊x / ξ⌋ : ℤ) : ℝ) - ⌊x₀ / ξ⌋ < 2 := by linarith
    have : ⌊x / ξ⌋ - ⌊x₀ / ξ⌋ < 2 := by exact_mod_cast this
    omega

/-- The zoomed corner of a deep label: its block start and its major centre there. -/
def deepCorner (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ) (Q : Fin (a.n k r))
    (r' : ℝ) (n : Fin (a.n k r')) : Fin 2 → ℝ :=
  ![(blockStart (a.T k r') (a.j k r' n) - (parentZoom p a k r Q).t₀) / (parentZoom p a k r Q).q,
    (a.c k r' n 0 + blockStart (a.T k r') (a.j k r' n) * a.c k r' n 1 -
      (parentZoom p a k r Q).z₀) / (parentZoom p a k r Q).q]

/-- **Geometry of a small deep label.** If the deep block and the deep major
width are at most one zoomed cell, every incidence of the deep label lies in a
cell adjacent to the cell of its corner. -/
theorem hcell_near_corner (p : Parameters) (a : PreparedModel α) (k : ℕ) (r : ℝ)
    (Q : Fin (a.n k r)) (r' : ℝ) (n : Fin (a.n k r')) {ξ K : ℝ} (hξ : 0 < ξ)
    (hsmall : 2 * K * a.q k r' ≤ ξ * a.q k r) (hsmall' : a.q k r' ≤ ξ * a.q k r)
    (hc1 : |a.c k r' n 1| ≤ K) {l : α} {t : ℝ} (ht : t ∈ a.block k r' n)
    (hplank : |(a.x k l t) 1 - a.c k r' n 0 - t * a.c k r' n 1| ≤ K * a.q k r') :
    ∀ i, |hcell (parentZoom p a k r Q) ξ (a.b k l) t i -
      ⌊deepCorner p a k r Q r' n i / ξ⌋| ≤ 1 := by
  have hq := q_pos a k r
  have hq' := q_pos a k r'
  have hK : 0 ≤ K := le_trans (abs_nonneg _) hc1
  have hZq : (parentZoom p a k r Q).q = a.q k r := rfl
  simp only [block] at ht
  rw [interval_eq] at ht
  obtain ⟨ht1, ht2⟩ := ht
  set t₁ := blockStart (a.T k r') (a.j k r' n)
  have hq'def : (2 : ℝ) ^ (-((a.T k r' : ℕ) : ℤ)) = a.q k r' := rfl
  rw [hq'def] at ht2
  intro i
  fin_cases i
  · -- zoomed time
    simp only [hcell, hpos, deepCorner, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    apply floor_sub_le_one hξ
    rw [hZq, ← sub_div, abs_div, abs_of_pos hq, div_le_iff₀ hq]
    rw [abs_le]; constructor <;> nlinarith
  · -- zoomed major position
    simp only [hcell, hpos, deepCorner, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Zoom.coeff_zero]
    apply floor_sub_le_one hξ
    have hx1 : (a.x k l t) 1 = a.b k l 0 + t * a.b k l 3 := rfl
    rw [hx1] at hplank
    have hid : (a.b k l 0 + (parentZoom p a k r Q).t₀ * a.b k l 3 - (parentZoom p a k r Q).z₀) /
          (parentZoom p a k r Q).q +
        (t - (parentZoom p a k r Q).t₀) / (parentZoom p a k r Q).q * a.b k l 3 -
        (a.c k r' n 0 + t₁ * a.c k r' n 1 - (parentZoom p a k r Q).z₀) /
          (parentZoom p a k r Q).q =
        ((a.b k l 0 + t * a.b k l 3 - a.c k r' n 0 - t * a.c k r' n 1) +
          (t - t₁) * a.c k r' n 1) / (parentZoom p a k r Q).q := by
      field_simp; ring
    rw [hid, hZq, abs_div, abs_of_pos hq, div_le_iff₀ hq]
    have h2 : |(t - t₁) * a.c k r' n 1| ≤ K * a.q k r' := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      calc (t - t₁) * |a.c k r' n 1| ≤ a.q k r' * K :=
            mul_le_mul (by linarith) hc1 (abs_nonneg _) hq'.le
        _ = K * a.q k r' := by ring
    calc |(a.b k l 0 + t * a.b k l 3 - a.c k r' n 0 - t * a.c k r' n 1) +
          (t - t₁) * a.c k r' n 1|
        ≤ |a.b k l 0 + t * a.b k l 3 - a.c k r' n 0 - t * a.c k r' n 1| +
          |(t - t₁) * a.c k r' n 1| := abs_add_le _ _
      _ ≤ K * a.q k r' + K * a.q k r' := add_le_add hplank h2
      _ ≤ ξ * a.q k r := by linarith

theorem volume_interval (T : ℕ) (j : Fin (2 ^ T)) :
    volume (interval T j) = ENNReal.ofReal ((2 : ℝ) ^ (-(T : ℤ))) := by
  rw [interval_eq, Real.volume_Icc]
  congr 1; ring

theorem interval_inter_subsingleton (T : ℕ) {j j' : Fin (2 ^ T)} (h : j ≠ j') :
    (interval T j ∩ interval T j').Subsingleton := by
  intro x hx y hy
  simp only [interval, mem_inter_iff, mem_Icc] at hx hy
  have hpos : (0 : ℝ) < 2 ^ T := by positivity
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne h) with hlt | hlt
  · -- `j < j'`: the only common point is `(j + 1) / 2^T = j' / 2^T`
    have h1 : ((j : ℕ) : ℝ) + 1 ≤ ((j' : ℕ) : ℝ) := by exact_mod_cast hlt
    have hx1 : x ≤ (((j : ℕ) : ℝ) + 1) / 2 ^ T := hx.1.2
    have hx2 : ((j' : ℕ) : ℝ) / 2 ^ T ≤ x := hx.2.1
    have hy1 : y ≤ (((j : ℕ) : ℝ) + 1) / 2 ^ T := hy.1.2
    have hy2 : ((j' : ℕ) : ℝ) / 2 ^ T ≤ y := hy.2.1
    have : (((j : ℕ) : ℝ) + 1) / 2 ^ T ≤ ((j' : ℕ) : ℝ) / 2 ^ T :=
      div_le_div_of_nonneg_right h1 hpos.le
    linarith
  · have h1 : ((j' : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hlt
    have hx1 : x ≤ (((j' : ℕ) : ℝ) + 1) / 2 ^ T := hx.2.2
    have hx2 : ((j : ℕ) : ℝ) / 2 ^ T ≤ x := hx.1.1
    have hy1 : y ≤ (((j' : ℕ) : ℝ) + 1) / 2 ^ T := hy.2.2
    have hy2 : ((j : ℕ) : ℝ) / 2 ^ T ≤ y := hy.1.1
    have : (((j' : ℕ) : ℝ) + 1) / 2 ^ T ≤ ((j : ℕ) : ℝ) / 2 ^ T :=
      div_le_div_of_nonneg_right h1 hpos.le
    linarith

/-- **Deep labels inside a parent have summable full assignments.** -/
theorem sum_inside_prior_le (a : PreparedModel α) (k : ℕ) (r r' : ℝ) (Q : Fin (a.n k r))
    (hAm : ∀ n, MeasurableSet (a.A k r' n))
    (hdisj : ∀ n n', n ≠ n' → a.j k r' n = a.j k r' n' → Disjoint (a.A k r' n) (a.A k r' n'))
    (S : Finset (Fin (a.n k r')))
    (hS : ∀ n ∈ S, a.A k r' n ⊆ a.A k r Q ∧ a.block k r' n ⊆ a.block k r Q) :
    ∑ n ∈ S, ENNReal.ofReal (a.q k r') * a.nu k (a.A k r' n) ≤
      ENNReal.ofReal (a.q k r) * a.nu k (a.A k r Q) := by
  classical
  set J := S.image (a.j k r')
  have hfib : ∀ j' ∈ J, ∑ n ∈ S.filter (fun n => a.j k r' n = j'), a.nu k (a.A k r' n) ≤
      a.nu k (a.A k r Q) := by
    intro j' _
    rw [← measure_biUnion_finset]
    · apply measure_mono
      intro l hl
      simp only [mem_iUnion] at hl
      obtain ⟨n, hn, hln⟩ := hl
      exact (hS n (Finset.mem_filter.mp hn).1).1 hln
    · intro n hn n' hn' hnn'
      exact hdisj n n' hnn' ((Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hn').2.symm)
    · intro n _; exact hAm n
  have hcount : (J.card : ℝ≥0∞) * ENNReal.ofReal (a.q k r') ≤ ENNReal.ofReal (a.q k r) := by
    have hvol : ∑ j' ∈ J, volume (interval (a.T k r') j') ≤ volume (a.block k r Q) := by
      rw [← measure_biUnion_finset₀]
      · apply measure_mono
        intro x hx
        simp only [mem_iUnion] at hx
        obtain ⟨j', hj', hx⟩ := hx
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj'
        exact (hS n hn).2 hx
      · intro j' _ j'' _ hjj
        exact (interval_inter_subsingleton _ hjj).measure_zero volume
      · intro j' _; exact measurableSet_Icc.nullMeasurableSet
    simp only [volume_interval, Finset.sum_const, nsmul_eq_mul, block] at hvol
    exact hvol
  calc ∑ n ∈ S, ENNReal.ofReal (a.q k r') * a.nu k (a.A k r' n)
      = ∑ j' ∈ J, ∑ n ∈ S.filter (fun n => a.j k r' n = j'),
          ENNReal.ofReal (a.q k r') * a.nu k (a.A k r' n) :=
        (Finset.sum_fiberwise_of_maps_to (fun n hn => Finset.mem_image_of_mem _ hn) _).symm
    _ = ∑ j' ∈ J, ENNReal.ofReal (a.q k r') *
          ∑ n ∈ S.filter (fun n => a.j k r' n = j'), a.nu k (a.A k r' n) := by
        simp only [Finset.mul_sum]
    _ ≤ ∑ _j' ∈ J, ENNReal.ofReal (a.q k r') * a.nu k (a.A k r Q) :=
        Finset.sum_le_sum fun j' hj' => mul_le_mul_right (hfib j' hj') _
    _ = (J.card : ℝ≥0∞) * ENNReal.ofReal (a.q k r') * a.nu k (a.A k r Q) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ ENNReal.ofReal (a.q k r) * a.nu k (a.A k r Q) := mul_le_mul_left hcount _

end

end Submission.Obl.k4_narrow_projected_row_parents
