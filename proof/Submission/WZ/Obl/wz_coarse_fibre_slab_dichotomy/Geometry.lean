-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.OrthogonalBox
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorBox

/-!
# Elementary geometry of the doubled coarse tube

For a fine segment inside a coarse `ρ`-tube, its `ρ`-neighbourhood lies in the doubled tube
`W = T (2ρ) (y - w/2) (2w)`; `μ W ≤ 96 ρ²`; and every slab containing the fine segment meets
`W` in volume at least `ρ * min r (ρ/2) / 2`.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy

open MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace

/-- The closed slab `{p | |⟪u,p⟫ - t| ≤ r}`. -/
def slabQ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ) :
    Set LeanEval.Analysis.WangZahlKakeya.Space :=
  {p | |inner ℝ u p - t| ≤ r}

/-- The doubled coarse tube. -/
def doubled (ρ : ℝ) (y w : LeanEval.Analysis.WangZahlKakeya.Space) :
    Set LeanEval.Analysis.WangZahlKakeya.Space :=
  thickening (2 * ρ) (segment ℝ (y - (1 / 2 : ℝ) • w) (y - (1 / 2 : ℝ) • w + (2 : ℝ) • w))

local notation "Sp" => LeanEval.Analysis.WangZahlKakeya.Space

lemma isClosed_slabQ (u : Sp) (t r : ℝ) : IsClosed (slabQ u t r) := by
  apply isClosed_le _ continuous_const
  fun_prop

lemma measurableSet_slabQ (u : Sp) (t r : ℝ) : MeasurableSet (slabQ u t r) :=
  (isClosed_slabQ u t r).measurableSet

/-- A unit vector orthogonal to two given vectors of the three-dimensional space. -/
lemma exists_unit_orth_two (u v : Sp) :
    ∃ e : Sp, ‖e‖ = 1 ∧ inner ℝ e u = 0 ∧ inner ℝ e v = 0 := by
  classical
  let K : Submodule ℝ Sp := Submodule.span ℝ {u, v}
  have hK : Module.finrank ℝ K ≤ 2 := by
    have h := finrank_span_finset_le_card (R := ℝ) ({u, v} : Finset Sp)
    have hc : ((({u, v} : Finset Sp)) : Set Sp) = {u, v} := by
      ext z; simp
    rw [Set.finrank, hc] at h
    exact h.trans Finset.card_le_two
  have hsum := K.finrank_add_finrank_orthogonal
  rw [finrank_euclideanSpace_fin] at hsum
  have hpos : 0 < Module.finrank ℝ Kᗮ := by omega
  have hne : Kᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he0
  refine ⟨‖e‖⁻¹ • e, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  · have hu : u ∈ K := Submodule.subset_span (by simp)
    have := (Submodule.mem_orthogonal' K e).mp he u hu
    rw [real_inner_smul_left, this, mul_zero]
  · have hv : v ∈ K := Submodule.subset_span (by simp)
    have := (Submodule.mem_orthogonal' K e).mp he v hv
    rw [real_inner_smul_left, this, mul_zero]

/-- The segment `[y, y+w]` lies in the doubled segment `[y - w/2, y + 3w/2]`. -/
lemma segment_subset_doubled_segment (y w : Sp) :
    segment ℝ y (y + w) ⊆
      segment ℝ (y - (1 / 2 : ℝ) • w) (y - (1 / 2 : ℝ) • w + (2 : ℝ) • w) := by
  apply (convex_segment _ _).segment_subset
  · refine ⟨3 / 4, 1 / 4, by norm_num, by norm_num, by norm_num, ?_⟩
    module
  · refine ⟨1 / 4, 3 / 4, by norm_num, by norm_num, by norm_num, ?_⟩
    module

/-- The `ρ`-neighbourhood of a fine segment contained (with its `δ`-tube) in a coarse `ρ`-tube
lies in the doubled coarse tube. -/
lemma thickening_subset_doubled {ρ δ : ℝ} (hδ : 0 < δ) {x v y w : Sp}
    (h : thickening δ (segment ℝ x (x + v)) ⊆ thickening ρ (segment ℝ y (y + w))) :
    thickening ρ (segment ℝ x (x + v)) ⊆ doubled ρ y w := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  have hq' : q ∈ thickening ρ (segment ℝ y (y + w)) := h (self_subset_thickening hδ _ hq)
  obtain ⟨q', hq', hqq'⟩ := mem_thickening_iff.mp hq'
  refine mem_thickening_iff.mpr ⟨q', segment_subset_doubled_segment y w hq', ?_⟩
  calc dist p q' ≤ dist p q + dist q q' := dist_triangle _ _ _
    _ < ρ + ρ := add_lt_add hpq hqq'
    _ = 2 * ρ := by ring


open WangZahlLot.Obl.wz_regular_transverse_affine_cells in
/-- The doubled coarse tube has volume at most `96 ρ²`. -/
lemma volume_doubled_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (y : Sp) {w : Sp} (hw : ‖w‖ = 1) :
    volume (doubled ρ y w) ≤ ENNReal.ofReal (96 * ρ ^ 2) := by
  obtain ⟨N, hN, hNw⟩ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.exists_orth_unit hw
  obtain ⟨b, hb1, hb2⟩ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.exists_frame
    hN hw hNw
  have hsub : doubled ρ y w ⊆ orthogonalBox ![2 * ρ, 2 * ρ, 1 + 2 * ρ] (y + (1 / 2 : ℝ) • w) b := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
    obtain ⟨a, c, ha, hc, hac, rfl⟩ := hq
    have hqc : a • (y - (1 / 2 : ℝ) • w) + c • (y - (1 / 2 : ℝ) • w + (2 : ℝ) • w) -
        (y + (1 / 2 : ℝ) • w) = (2 * c - 1) • w := by
      have ha' : a = 1 - c := by linarith
      subst ha'
      module
    have hsplit : p - (y + (1 / 2 : ℝ) • w) =
        (p - (a • (y - (1 / 2 : ℝ) • w) + c • (y - (1 / 2 : ℝ) • w + (2 : ℝ) • w))) +
          (2 * c - 1) • w := by rw [← hqc]; abel
    have hcw : |2 * c - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have key : ∀ i, |inner ℝ (b i) (p - (y + (1 / 2 : ℝ) • w))| ≤
        2 * ρ + |inner ℝ (b i) w| := by
      intro i
      rw [hsplit, inner_add_right, inner_smul_right]
      have h1 : |inner ℝ (b i) (p - (a • (y - (1 / 2 : ℝ) • w) +
          c • (y - (1 / 2 : ℝ) • w + (2 : ℝ) • w)))| < 2 * ρ := by
        calc _ ≤ ‖b i‖ * ‖p - (a • (y - (1 / 2 : ℝ) • w) +
                c • (y - (1 / 2 : ℝ) • w + (2 : ℝ) • w))‖ := abs_real_inner_le_norm _ _
          _ = dist p (a • (y - (1 / 2 : ℝ) • w) + c • (y - (1 / 2 : ℝ) • w + (2 : ℝ) • w)) := by
              rw [b.orthonormal.1 i, one_mul, dist_eq_norm]
          _ < 2 * ρ := hpq
      calc _ ≤ |inner ℝ (b i) (p - (a • (y - (1 / 2 : ℝ) • w) +
              c • (y - (1 / 2 : ℝ) • w + (2 : ℝ) • w)))| +
            |(2 * c - 1) * inner ℝ (b i) w| := abs_add_le _ _
        _ ≤ 2 * ρ + 1 * |inner ℝ (b i) w| := by
            rw [abs_mul]
            exact add_le_add h1.le (mul_le_mul_of_nonneg_right hcw (abs_nonneg _))
        _ = 2 * ρ + |inner ℝ (b i) w| := by ring
    have hw0 : inner ℝ (b 0) w = 0 := by rw [← hb2]; exact b.orthonormal.2 (by decide)
    have hw1 : inner ℝ (b 1) w = 0 := by rw [← hb2]; exact b.orthonormal.2 (by decide)
    have hw2 : inner ℝ (b 2) w = 1 := by
      rw [hb2, real_inner_self_eq_norm_sq, hw]; norm_num
    intro i
    fin_cases i
    · have := key 0
      rw [hw0, abs_zero, add_zero] at this
      simpa using this
    · have := key 1
      rw [hw1, abs_zero, add_zero] at this
      simpa using this
    · have := key 2
      rw [hw2, abs_one] at this
      simp only [Fin.reduceFinMk, Matrix.cons_val]
      linarith
  calc volume (doubled ρ y w)
      ≤ volume (orthogonalBox ![2 * ρ, 2 * ρ, 1 + 2 * ρ] (y + (1 / 2 : ℝ) • w) b) :=
        measure_mono hsub
    _ = ENNReal.ofReal (8 * ∏ i, (![2 * ρ, 2 * ρ, 1 + 2 * ρ] : Fin 3 → ℝ) i) := by
        apply volume_orthogonalBox
        intro i; fin_cases i <;> simp <;> linarith
    _ ≤ ENNReal.ofReal (96 * ρ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
        nlinarith [sq_nonneg ρ]

/-- If `x * y ≤ 0` then `|x + y| ≤ max |x| |y|`. -/
lemma abs_add_le_max_of_mul_nonpos {x y : ℝ} (h : x * y ≤ 0) : |x + y| ≤ max |x| |y| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · have : x * y = 0 := le_antisymm h (mul_nonneg hx hy)
    rcases mul_eq_zero.mp this with h0 | h0 <;> simp [h0]
  · rw [abs_le]; constructor
    · have := neg_abs_le y; have := le_max_right |x| |y|; linarith
    · have := le_abs_self x; have := le_max_left |x| |y|; linarith
  · rw [abs_le]; constructor
    · have := neg_abs_le x; have := le_max_left |x| |y|; linarith
    · have := le_abs_self y; have := le_max_right |x| |y|; linarith
  · have : x * y = 0 := le_antisymm h (mul_nonneg_of_nonpos_of_nonpos hx hy)
    rcases mul_eq_zero.mp this with h0 | h0 <;> simp [h0]

/-- An affine function of `s` has a constant sign on `[0,1/2]` or on `[1/2,1]`. -/
lemma exists_half_sign (g₀ g₁ : ℝ) : ∃ s₀ ε : ℝ, 1 / 4 ≤ s₀ ∧ s₀ ≤ 3 / 4 ∧ (ε = 1 ∨ ε = -1) ∧
    ∀ s, s₀ - 1 / 4 ≤ s → s ≤ s₀ + 1 / 4 → ε * (g₀ + s * g₁) ≤ 0 := by
  rcases le_total (g₀ + g₁ / 2) 0 with hmid | hmid
  · rcases le_total g₀ 0 with h0 | h0
    · refine ⟨1 / 4, 1, by norm_num, by norm_num, Or.inl rfl, fun s hs1 hs2 => ?_⟩
      have : g₀ + s * g₁ = (1 - 2 * s) * g₀ + (2 * s) * (g₀ + g₁ / 2) := by ring
      rw [this, one_mul]
      have h1 : 0 ≤ 1 - 2 * s := by linarith
      have h2 : 0 ≤ 2 * s := by linarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 h0, mul_nonpos_of_nonneg_of_nonpos h2 hmid]
    · refine ⟨3 / 4, 1, by norm_num, by norm_num, Or.inl rfl, fun s hs1 hs2 => ?_⟩
      have hend : g₀ + g₁ ≤ 0 := by linarith
      have : g₀ + s * g₁ = (2 - 2 * s) * (g₀ + g₁ / 2) + (2 * s - 1) * (g₀ + g₁) := by ring
      rw [this, one_mul]
      have h1 : 0 ≤ 2 - 2 * s := by linarith
      have h2 : 0 ≤ 2 * s - 1 := by linarith
      nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 hmid, mul_nonpos_of_nonneg_of_nonpos h2 hend]
  · rcases le_total 0 g₀ with h0 | h0
    · refine ⟨1 / 4, -1, by norm_num, by norm_num, Or.inr rfl, fun s hs1 hs2 => ?_⟩
      have : g₀ + s * g₁ = (1 - 2 * s) * g₀ + (2 * s) * (g₀ + g₁ / 2) := by ring
      rw [this]
      have h1 : 0 ≤ 1 - 2 * s := by linarith
      have h2 : 0 ≤ 2 * s := by linarith
      nlinarith [mul_nonneg h1 h0, mul_nonneg h2 hmid]
    · refine ⟨3 / 4, -1, by norm_num, by norm_num, Or.inr rfl, fun s hs1 hs2 => ?_⟩
      have hend : 0 ≤ g₀ + g₁ := by linarith
      have : g₀ + s * g₁ = (2 - 2 * s) * (g₀ + g₁ / 2) + (2 * s - 1) * (g₀ + g₁) := by ring
      rw [this]
      have h1 : 0 ≤ 2 - 2 * s := by linarith
      have h2 : 0 ≤ 2 * s - 1 := by linarith
      nlinarith [mul_nonneg h1 hmid, mul_nonneg h2 hend]

open WangZahlLot.Obl.wz_regular_transverse_affine_cells in
/-- A slab containing a unit segment meets any set containing the `ρ`-neighbourhood of the segment
in volume at least `ρ * min r (ρ/2) / 2`. -/
lemma volume_inter_slab_ge {ρ r t : ℝ} (hρ : 0 < ρ) (hr : 0 < r) {x v u : Sp} (hv : ‖v‖ = 1)
    (hu : ‖u‖ ≤ 1) {W : Set Sp} (hW : thickening ρ (segment ℝ x (x + v)) ⊆ W)
    (hseg : segment ℝ x (x + v) ⊆ slabQ u t r) :
    ENNReal.ofReal (ρ * min r (ρ / 2) / 2) ≤ volume (W ∩ slabQ u t r) := by
  obtain ⟨e, he, heu, hev⟩ := exists_unit_orth_two u v
  obtain ⟨b, hb1, hb2⟩ := WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor.exists_frame
    hv he (by rw [real_inner_comm]; exact hev)
  set β := inner ℝ u (b 0) with hβ
  have hβ1 : |β| ≤ 1 := by
    calc |β| ≤ ‖u‖ * ‖b 0‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := by rw [b.orthonormal.1 0]; nlinarith [norm_nonneg u]
      _ = 1 := by ring
  obtain ⟨s₀, ε, hs₀l, hs₀u, hε, hsign⟩ :=
    exists_half_sign (β * (inner ℝ u x - t)) (β * inner ℝ u v)
  have hεsq : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  set m := min r (ρ / 2) with hm
  have hm0 : 0 < m := lt_min hr (by linarith)
  have hmr : m ≤ r := min_le_left _ _
  have hmρ : m ≤ ρ / 2 := min_le_right _ _
  set c₀ := x + s₀ • v + (ε * m / 2) • b 0 with hc₀
  have hb02 : inner ℝ (b 0) (b 2) = 0 := b.orthonormal.2 (by decide)
  have hue : inner ℝ u e = 0 := by rw [real_inner_comm]; exact heu
  have hbox : orthogonalBox ![m / 2, 1 / 4, ρ / 2] c₀ b ⊆ W ∩ slabQ u t r := by
    intro p hp
    set a₀ := inner ℝ (b 0) (p - c₀) with ha₀
    set a₁ := inner ℝ (b 1) (p - c₀) with ha₁
    set a₂ := inner ℝ (b 2) (p - c₀) with ha₂
    have h0 : |a₀| ≤ m / 2 := by simpa using hp 0
    have h1 : |a₁| ≤ 1 / 4 := by simpa using hp 1
    have h2 : |a₂| ≤ ρ / 2 := by simpa using hp 2
    have hexp : p - c₀ = a₀ • b 0 + a₁ • b 1 + a₂ • b 2 := by
      have := b.sum_repr' (p - c₀)
      rw [Fin.sum_univ_three] at this
      exact this.symm
    have hp' : p = (x + (s₀ + a₁) • v) + ((ε * m / 2 + a₀) • b 0 + a₂ • e) := by
      have hpc : p = c₀ + (p - c₀) := by abel
      rw [hpc, hexp, hc₀, hb1, hb2]
      module
    have hs0 : 0 ≤ s₀ + a₁ := by have := neg_abs_le a₁; linarith
    have hs1 : s₀ + a₁ ≤ 1 := by have := le_abs_self a₁; linarith
    have hq : x + (s₀ + a₁) • v ∈ segment ℝ x (x + v) :=
      ⟨1 - (s₀ + a₁), s₀ + a₁, by linarith, hs0, by ring, by module⟩
    have hc' : |ε * m / 2 + a₀| ≤ m := by
      calc |ε * m / 2 + a₀| ≤ |ε * m / 2| + |a₀| := abs_add_le _ _
        _ = m / 2 + |a₀| := by rw [abs_div, abs_mul, hεabs, abs_of_pos hm0]; norm_num
        _ ≤ m := by linarith
    refine ⟨hW (mem_thickening_iff.mpr ⟨x + (s₀ + a₁) • v, hq, ?_⟩), ?_⟩
    · rw [dist_eq_norm, hp', add_sub_cancel_left]
      have hnsq : ‖(ε * m / 2 + a₀) • b 0 + a₂ • e‖ ^ 2 = (ε * m / 2 + a₀) ^ 2 + a₂ ^ 2 := by
        rw [← hb2, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hb02,
          norm_smul, norm_smul, b.orthonormal.1 0, b.orthonormal.1 2, Real.norm_eq_abs,
          Real.norm_eq_abs, mul_one, mul_one, sq_abs, sq_abs]
        ring
      have hlt : ‖(ε * m / 2 + a₀) • b 0 + a₂ • e‖ ^ 2 < ρ ^ 2 := by
        rw [hnsq]
        have e1 : (ε * m / 2 + a₀) ^ 2 ≤ m ^ 2 := by
          rw [← sq_abs, ← sq_abs m]; exact pow_le_pow_left₀ (abs_nonneg _)
            (hc'.trans (le_abs_self m)) 2
        have e2 : a₂ ^ 2 ≤ (ρ / 2) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
        have e3 : m ^ 2 ≤ (ρ / 2) ^ 2 := pow_le_pow_left₀ hm0.le hmρ 2
        nlinarith
      exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hρ.le (by norm_num)).mp hlt
    · show |inner ℝ u p - t| ≤ r
      have hγ : |inner ℝ u (x + (s₀ + a₁) • v) - t| ≤ r := hseg hq
      have hsplit : inner ℝ u p - t =
          (inner ℝ u (x + (s₀ + a₁) • v) - t) + (ε * m / 2 + a₀) * β := by
        rw [hp']
        simp only [inner_add_right, inner_smul_right, hue, hβ]
        ring
      rw [hsplit]
      have hsg := hsign (s₀ + a₁) (by have := neg_abs_le a₁; linarith)
        (by have := le_abs_self a₁; linarith)
      have hγexp : inner ℝ u (x + (s₀ + a₁) • v) - t =
          (inner ℝ u x - t) + (s₀ + a₁) * inner ℝ u v := by
        rw [inner_add_right, inner_smul_right]; ring
      have hεc : 0 ≤ ε * (ε * m / 2 + a₀) := by
        have : ε * (ε * m / 2 + a₀) = m / 2 + ε * a₀ := by
          have : ε * (ε * m / 2) = (ε * ε) * m / 2 := by ring
          rw [mul_add, this, hεsq]; ring
        rw [this]
        have : |ε * a₀| ≤ m / 2 := by rw [abs_mul, hεabs, one_mul]; exact h0
        have := neg_abs_le (ε * a₀)
        linarith
      have hprod : (inner ℝ u (x + (s₀ + a₁) • v) - t) * ((ε * m / 2 + a₀) * β) ≤ 0 := by
        have hkey : (inner ℝ u (x + (s₀ + a₁) • v) - t) * ((ε * m / 2 + a₀) * β) =
            (ε * (ε * m / 2 + a₀)) *
              (ε * (β * (inner ℝ u x - t) + (s₀ + a₁) * (β * inner ℝ u v))) := by
          rw [hγexp]
          have : ε * (ε * m / 2 + a₀) * (ε * (β * (inner ℝ u x - t) +
              (s₀ + a₁) * (β * inner ℝ u v))) = (ε * ε) * ((ε * m / 2 + a₀) *
              (β * (inner ℝ u x - t) + (s₀ + a₁) * (β * inner ℝ u v))) := by ring
          rw [this, hεsq]; ring
        rw [hkey]
        exact mul_nonpos_of_nonneg_of_nonpos hεc hsg
      calc _ ≤ max |inner ℝ u (x + (s₀ + a₁) • v) - t| |(ε * m / 2 + a₀) * β| :=
            abs_add_le_max_of_mul_nonpos hprod
        _ ≤ r := by
            apply max_le hγ
            rw [abs_mul]
            calc |ε * m / 2 + a₀| * |β| ≤ m * 1 :=
                  mul_le_mul hc' hβ1 (abs_nonneg _) hm0.le
              _ ≤ r := by linarith
  calc ENNReal.ofReal (ρ * min r (ρ / 2) / 2)
      = volume (orthogonalBox ![m / 2, 1 / 4, ρ / 2] c₀ b) := by
        rw [volume_orthogonalBox]
        · congr 1
          simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
          rw [← hm]; ring
        · intro i; fin_cases i <;> simp <;> linarith
    _ ≤ volume (W ∩ slabQ u t r) := measure_mono hbox

end WangZahlLot.Obl.wz_coarse_fibre_slab_dichotomy
