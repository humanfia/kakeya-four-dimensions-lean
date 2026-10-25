-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Agree.EventGeometry; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Sample
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Agree.Transverse
import Submission.Obl.k4_general_compared_layers_velocity_lists.NativeSourceCaps

/-!
# Geometry of one incidence of a color-0 event

For an incidence `ω = (l, t)` of a color-0 event `e` with parent block `Q`, coarse label `i`
and fine label `j`:

* its time lies in the block of `Q`, its normalized time in `[0, 1]`;
* its normalized major and transverse coordinates are at most `K`, its base coordinates at
  most `K`;
* `Y = Y_Q(t, Z) + w U` exactly;
* `X = G_i(t, Y) + offset(Q, i, j)` up to `2 H a₁` (fine-layer fit and the offset fit on the
  true fiber box);
* its trajectory lies within `2 χ` of the coarse tag line.

Two incidences in one native state are close in `(t, Z, U, X)`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

theorem agree_blockLen_pos (k : ℕ) (r : ℝ) : 0 < p.blockLen k r := by
  unfold blockLen
  positivity

theorem agree_blockLen_le_one (k : ℕ) (r : ℝ) : p.blockLen k r ≤ 1 := by
  unfold blockLen
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem agree_blockLen_eq_zpow (k : ℕ) (r : ℝ) :
    p.blockLen k r = (2 : ℝ) ^ (-(p.T k r : ℤ)) := by
  unfold blockLen
  rw [zpow_neg, zpow_natCast]

theorem agree_blockWidth_pos {k : ℕ} (r : ℝ) (hN : 0 < p.N k) : 0 < p.blockWidth k r := by
  unfold blockWidth
  exact mul_pos (agree_blockLen_pos k r) (Real.rpow_pos_of_pos hN _)

theorem agree_blockWidth_le_one {k : ℕ} {r : ℝ} (hN : 1 ≤ p.N k) (hℓr : 0 ≤ p.ℓ * r) :
    p.blockWidth k r ≤ 1 := by
  unfold blockWidth
  have h1 : p.N k ^ (-p.ℓ * r) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have h2 := agree_blockLen_le_one (p := p) k r
  have h3 := (agree_blockLen_pos (p := p) k r).le
  have h4 : 0 ≤ p.N k ^ (-p.ℓ * r) := Real.rpow_nonneg (by linarith) _
  nlinarith

theorem agree_mem_block_iff {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)} {t : ℝ} :
    t ∈ block (p.T k r) (p.j k r Q) ↔
      p.blockStart k r Q ≤ t ∧ t ≤ p.blockStart k r Q + p.blockLen k r := by
  simp only [block, Submission.Obl.k4_critical_intercept_concentration.Data.I, mem_Icc,
    blockStart, blockLen]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;>
    [rw [add_div, one_div] at h2; rw [add_div, one_div]] <;> exact h2

theorem agree_blockStart_nonneg (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) : 0 ≤ p.blockStart k r Q := by
  unfold blockStart
  positivity

theorem agree_blockStart_add_le_one (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) :
    p.blockStart k r Q + p.blockLen k r ≤ 1 := by
  unfold blockStart blockLen
  have hj : ((p.j k r Q : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ p.T k r := by
    have := (p.j k r Q).isLt
    exact_mod_cast this
  have hpos : (0 : ℝ) < (2 : ℝ) ^ p.T k r := by positivity
  rw [div_eq_mul_inv, ← add_one_mul]
  calc _ ≤ (2 : ℝ) ^ p.T k r * ((2 : ℝ) ^ p.T k r)⁻¹ :=
        mul_le_mul_of_nonneg_right hj (inv_nonneg.mpr hpos.le)
    _ = 1 := mul_inv_cancel₀ hpos.ne'

theorem agree_block_subset_unit (k : ℕ) (r : ℝ) (Q : Fin (p.n k r)) :
    block (p.T k r) (p.j k r Q) ⊆ Icc (0 : ℝ) 1 := by
  intro t ht
  obtain ⟨h1, h2⟩ := (agree_mem_block_iff (p := p)).mp ht
  exact ⟨(agree_blockStart_nonneg k r Q).trans h1, h2.trans (agree_blockStart_add_le_one k r Q)⟩

theorem agree_tauN_mem_unit {k : ℕ} {r : ℝ} {Q : Fin (p.n k r)} {ω : α × ℝ}
    (ht : ω.2 ∈ block (p.T k r) (p.j k r Q)) :
    0 ≤ p.tauN k r Q ω ∧ p.tauN k r Q ω ≤ 1 := by
  obtain ⟨h1, h2⟩ := (agree_mem_block_iff (p := p)).mp ht
  have hq := agree_blockLen_pos (p := p) k r
  unfold tauN
  constructor
  · exact div_nonneg (by linarith) hq.le
  · rw [div_le_one hq]
    linarith

theorem AtDepth.agree_coeff_le {k : ℕ} {r R : ℝ} (hat : p.AtDepth k r R) (Q : Fin (p.n k r))
    (e : Fin 5) : |p.c k r Q e| ≤ p.K k :=
  (hat.2.2.2.2.1 Q).2.2.2.1 e

theorem AtDepth.agree_B_subset_A {k : ℕ} {r R : ℝ} (hat : p.AtDepth k r R) (Q : Fin (p.n k r)) :
    p.B k r Q ⊆ p.A k r Q :=
  (hat.2.2.1 Q).2.2

/-- The major and transverse block bounds in normalized coordinates. -/
theorem AtDepth.agree_normalized_le {k : ℕ} {r R : ℝ} (hat : p.AtDepth k r R) (hN : 0 < p.N k)
    (Q : Fin (p.n k r)) {ω : α × ℝ} (hl : ω.1 ∈ p.B k r Q)
    (ht : ω.2 ∈ block (p.T k r) (p.j k r Q)) :
    |p.zetaN k r Q ω| ≤ p.K k ∧ |p.uN k r Q ω| ≤ p.K k := by
  have hgeo := (hat.2.2.2.2.1 Q).2.2.2.2.2.1 ω.1 (hat.agree_B_subset_A Q hl) ω.2 ht
  have hq := agree_blockLen_pos (p := p) k r
  have hw := agree_blockWidth_pos (p := p) r hN
  have hqz : (2 : ℝ) ^ (-(p.T k r : ℤ)) = p.blockLen k r := (agree_blockLen_eq_zpow k r).symm
  rw [hqz] at hgeo
  obtain ⟨h1, h2, -⟩ := hgeo
  constructor
  · unfold zetaN
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    have : p.x k ω.1 ω.2 1 - p.c k r Q 0 - p.c k r Q 1 * ω.2 =
        p.x k ω.1 ω.2 1 - p.c k r Q 0 - ω.2 * p.c k r Q 1 := by ring
    rw [this]
    exact h1
  · unfold uN tiltY
    rw [abs_div, abs_of_pos hw, div_le_iff₀ hw]
    have : p.x k ω.1 ω.2 2 - (p.c k r Q 2 + p.c k r Q 3 * ω.2 + p.c k r Q 4 * p.x k ω.1 ω.2 1) =
        p.x k ω.1 ω.2 2 - p.c k r Q 2 - ω.2 * p.c k r Q 3 - p.c k r Q 4 * p.x k ω.1 ω.2 1 := by
      ring
    rw [this]
    have hwid : p.blockLen k r * p.N k ^ (-p.ℓ * r) = p.blockWidth k r := rfl
    calc _ ≤ p.K k * p.blockLen k r * p.N k ^ (-p.ℓ * r) := h2
      _ = p.K k * p.blockWidth k r := by rw [mul_assoc, hwid]

/-- The transverse coordinate reconstructs `Y` exactly. -/
theorem agree_x_two_eq_tilt {k : ℕ} {r : ℝ} (hN : 0 < p.N k) (Q : Fin (p.n k r)) (ω : α × ℝ) :
    p.x k ω.1 ω.2 2 =
      p.tiltY k r Q ω.2 (p.x k ω.1 ω.2 1) + p.blockWidth k r * p.uN k r Q ω := by
  have hw := agree_blockWidth_pos (p := p) r hN
  unfold uN
  field_simp
  ring

theorem agree_tauN_mul_add {k : ℕ} {r : ℝ} (Q : Fin (p.n k r)) (ω : α × ℝ) :
    ω.2 = p.blockStart k r Q + p.blockLen k r * p.tauN k r Q ω := by
  have hq := agree_blockLen_pos (p := p) k r
  unfold tauN
  field_simp
  ring

theorem agree_zetaN_mul_add {k : ℕ} {r : ℝ} (Q : Fin (p.n k r)) (ω : α × ℝ) :
    p.x k ω.1 ω.2 1 = p.c k r Q 0 + p.c k r Q 1 * ω.2 + p.blockLen k r * p.zetaN k r Q ω := by
  have hq := agree_blockLen_pos (p := p) k r
  unfold zetaN
  field_simp
  ring

/-- The bin of a real number determines it to within the mesh. -/
theorem agree_abs_sub_lt_of_floor_eq {x y δ : ℝ} (hδ : 0 < δ) (h : ⌊x / δ⌋ = ⌊y / δ⌋) :
    |x - y| < δ := by
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at h1
  exact h1

theorem agree_abs_sub_bin_le {x δ : ℝ} (hδ : 0 < δ) {a : ℤ} (h : ⌊x / δ⌋ = a) :
    |x - (a : ℝ) * δ| ≤ δ := by
  have hlo := (le_div_iff₀ hδ).mp (h ▸ Int.floor_le (x / δ))
  have hhi := (div_lt_iff₀ hδ).mp (h ▸ Int.lt_floor_add_one (x / δ))
  rw [abs_le]
  constructor <;> nlinarith

theorem agree_floor_div_mem_Icc {x δ : ℝ} (hδ : 0 < δ) {K : ℝ} (hx : |x| ≤ K) (M : ℕ)
    (hM : K / δ + 1 ≤ M) : ⌊x / δ⌋ ∈ Finset.Icc (-(M : ℤ)) M := by
  rw [Finset.mem_Icc]
  have h1 : |x / δ| ≤ K / δ := by
    rw [abs_div, abs_of_pos hδ]
    exact div_le_div_of_nonneg_right hx hδ.le
  have h2 := abs_le.mp h1
  constructor
  · have : (-(M : ℝ)) ≤ ((⌊x / δ⌋ : ℤ) : ℝ) := by
      have := Int.lt_floor_add_one (x / δ)
      linarith
    exact_mod_cast this
  · have : ((⌊x / δ⌋ : ℤ) : ℝ) ≤ (M : ℝ) := by
      have := Int.floor_le (x / δ)
      linarith
    exact_mod_cast this

namespace ComparedSample

variable {k : ℕ} {r u v m H : ℝ} (s : p.ComparedSample k r u v m H)

/-- The data of a color-0 event. -/
theorem agree_event_data0 {e : Fin (s.count 0)} {ω : α × ℝ} (hω : ω ∈ s.event 0 e) :
    ω ∈ p.baseGood k ∧ ω.1 ∈ p.B k r (s.parent 0 e) ∧
      ω.2 ∈ block (p.T k r) (p.j k r (s.parent 0 e)) ∧
      ω.1 ∈ (s.layers 0).C (s.coarse 0 e) ∧
      ω.1 ∈ (s.layers (0 : Fin 2).succ).C (s.fine 0 e) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := s.event_data 0 e ω hω
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The coarse tags of an incidence of the coarse layer. -/
theorem agree_coarse_tags {i : Fin (s.layers 0).count} {l : α} (hl : l ∈ (s.layers 0).C i) :
    ⌊p.b k l 3 / p.N k ^ (-m)⌋ = (s.layers 0).tag i 0 ∧
      ⌊p.b k l 0 / p.N k ^ (-m)⌋ = (s.layers 0).tag i 1 :=
  let h := ((s.layer_valid 0).2.2.2.2.2.1 i).2.2.2.1 l hl
  ⟨h.1, h.2.1⟩

/-- The fine-layer fit of an incidence. -/
theorem agree_fine_fit {j : Fin (s.layers (0 : Fin 2).succ).count} {l : α}
    (hl : l ∈ (s.layers (0 : Fin 2).succ).C j) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |p.signal k l t - eval ![t, p.x k l t 2] ((s.layers (0 : Fin 2).succ).G j)| ≤
      H * p.N k ^ (-(r + u)) := by
  have h := (((s.layer_valid (0 : Fin 2).succ).2.2.2.2.2.1 j).2.2.2.1 l hl).2.2 t ht
  have hs : (![r, r + u, r + v] : Fin 3 → ℝ) (0 : Fin 2).succ = r + u := rfl
  rw [hs] at h
  exact h.2

theorem agree_totalDegree_coarse (i : Fin (s.layers 0).count) :
    ((s.layers 0).G i).totalDegree ≤ 2 :=
  ((s.layer_valid 0).2.2.2.2.2.1 i).2.1

/-- Every incidence of a color-0 event is fitted by its coarse predictor plus the offset of
its fine label, to `2 H a₁`. -/
theorem agree_event_fit {R : ℝ} (hat : p.AtDepth k r R) (hN : 0 < p.N k) (hKH : p.K k ≤ H)
    {e : Fin (s.count 0)} {ω : α × ℝ} (hω : ω ∈ s.event 0 e) :
    |p.signal k ω.1 ω.2 -
        eval ![ω.2, p.tiltY k r (s.parent 0 e) ω.2 (p.x k ω.1 ω.2 1) +
          p.blockWidth k r * p.uN k r (s.parent 0 e) ω] ((s.layers 0).G (s.coarse 0 e)) -
        s.offset 0 (s.parent 0 e) (s.coarse 0 e) (s.fine 0 e)| ≤
      2 * H * p.N k ^ (-(r + u)) := by
  obtain ⟨hgood, hB, ht, hC, hF⟩ := s.agree_event_data0 hω
  have hunit : ω.2 ∈ Icc (0 : ℝ) 1 := agree_block_subset_unit k r _ ht
  rw [← agree_x_two_eq_tilt hN]
  have hfit := s.agree_fine_fit hF hunit
  -- the incidence lies on the true fiber box of its coarse tag
  have hbox : (![ω.2, p.x k ω.1 ω.2 1, p.x k ω.1 ω.2 2] : Fin 3 → ℝ) ∈
      p.trueFiberBox k r m H (s.parent 0 e) ((s.layers 0).tag (s.coarse 0 e)) := by
    obtain ⟨htag0, htag1⟩ := s.agree_coarse_tags hC
    have hχ : 0 < p.N k ^ (-m) := Real.rpow_pos_of_pos hN _
    have htube := intercept_velocity_bin_tube hχ htag1 htag0 hunit
    have hgeo := ((hat.2.2.2.2.1 (s.parent 0 e)).2.2.2.2.2.1 ω.1
      (hat.agree_B_subset_A _ hB) ω.2 ht).2.1
    have hH2 : (2 : ℝ) ≤ H := s.loss_one
    refine ⟨ht, ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hx1 : p.x k ω.1 ω.2 1 = p.b k ω.1 0 + ω.2 * p.b k ω.1 3 := rfl
      rw [hx1]
      calc _ ≤ 2 * p.N k ^ (-m) := htube
        _ ≤ H * p.N k ^ (-m) := by nlinarith
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      have hpos : 0 ≤ (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) := by positivity
      calc _ ≤ p.K k * (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r) := hgeo
        _ = p.K k * ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) := by ring
        _ ≤ H * ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) :=
          mul_le_mul_of_nonneg_right hKH hpos
  have hoff := s.offset_fit 0 (s.parent 0 e) (s.coarse 0 e) (s.fine 0 e) (s.fine_mem 0 e) _ hbox
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hoff
  rw [show -r - u = -(r + u) by ring] at hoff
  have hsig : p.signal k ω.1 ω.2 = eval (p.x k ω.1 ω.2) (p.P k) := rfl
  calc _ = |(p.signal k ω.1 ω.2 -
        eval ![ω.2, p.x k ω.1 ω.2 2] ((s.layers (0 : Fin 2).succ).G (s.fine 0 e))) +
        (eval ![ω.2, p.x k ω.1 ω.2 2] ((s.layers (0 : Fin 2).succ).G (s.fine 0 e)) -
          eval ![ω.2, p.x k ω.1 ω.2 2] ((s.layers 0).G (s.coarse 0 e)) -
          s.offset 0 (s.parent 0 e) (s.coarse 0 e) (s.fine 0 e))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ H * p.N k ^ (-(r + u)) + H * p.N k ^ (-(r + u)) := add_le_add hfit hoff
    _ = _ := by ring

end ComparedSample

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
