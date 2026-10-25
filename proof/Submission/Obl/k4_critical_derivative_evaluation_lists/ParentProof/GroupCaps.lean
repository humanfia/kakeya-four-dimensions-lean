/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, GroupCaps.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.GroupDefs
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.JointGrid
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.FrozenGroupBand
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.NativePerTimeSupport

/-! The two geometric inputs of the horizontal coefficient count, for the
original frozen data: the group band cap (from the frozen joint caps) and the
group scalar support count (from whole true boxes, the pure base cap, disjoint
full assignments and their original floors). -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The pointwise good set carries all of the original incidence measure. -/
theorem Valid.eventually_goodSet_full (h : cfg.Valid) {s : ℝ} (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, cfg.μ k (cfg.goodSet k s)ᶜ = 0 := by
  filter_upwards [h.eventually_assignment_level hs hsU] with k lev
  letI : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  obtain ⟨hb, _, _, hdom, _, _, _, _, hprior, _⟩ := h.basic k
  have hprod : ∀ᵐ p ∂(cfg.ν k).prod (volume : Measure ℝ),
      |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact hprior.mono (fun l hl => Filter.Eventually.of_forall (fun _ => hl))
  have hsum : ∀ᵐ p ∂cfg.μ k,
      |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k :=
    (Measure.absolutelyContinuous_of_le_smul hdom).ae_le hprod
  have hhidden : ∀ᵐ p ∂cfg.μ k, ∀ i : Fin (cfg.n k s),
      |cfg.b k p.1 2| ≤ cfg.K k ∧ |cfg.b k p.1 5| ≤ 2 * cfg.K k ∧
        ∀ t ∈ Icc (0 : ℝ) 1, |cfg.b k p.1 2 + t * cfg.b k p.1 5| ≤ cfg.K k :=
    ae_all_iff.mpr (fun i => lev.native_hidden_bounds h i)
  have hdef : ∀ᵐ p ∂cfg.μ k, ∀ i : Fin (cfg.n k s),
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) :=
    ae_all_iff.mpr lev.horizontal_equation
  apply ae_iff.mp
  filter_upwards [lev.covers, hsum, hhidden, hdef] with p hcov hbnd hhid hdefect
  obtain ⟨i, hiB, hiI⟩ := hcov
  have hnat := hhid i
  refine ⟨mem_time_block_unit _ _ hiI, ?_, ?_, ?_, ?_, hnat.1, hnat.2.1,
    hdefect i, i, hiB, hiI⟩ <;>
    linarith [abs_nonneg (cfg.b k p.1 0), abs_nonneg (cfg.b k p.1 1),
      abs_nonneg (cfg.b k p.1 3), abs_nonneg (cfg.b k p.1 4)]

/-- Equal original group codes control the three initial coordinates. -/
theorem groupCode_coordinate_gaps (cfg : Data α) (k : ℕ) (a v : ℝ)
    (ha : 0 < a) (hv : 0 < v) (hva : v ≤ a) (l l' : α)
    (heq : cfg.groupCode k a v l = cfg.groupCode k a v l') :
    |cfg.b k l 0 - cfg.b k l' 0| ≤ a ∧
    |cfg.b k l 1 - cfg.b k l' 1| ≤ a ∧
    |cfg.b k l 3 - cfg.b k l' 3| ≤ a := by
  refine ⟨?_, ?_, ?_⟩
  · exact Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq ha
      (congrArg Prod.fst heq)
  · exact Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq ha
      (congrArg (fun z => z.2.1) heq)
  · exact (Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq hv
      (congrArg (fun z => z.2.2) heq)).trans hva

/-- Sample-wise original group cap, using a sufficiently fine original
mesh and an absorbed numerical constant. -/
theorem group_band_cap_at_sample (h : cfg.Valid) {k : ℕ} {s b ε : ℝ}
    (hs : 0 < s) (hse : s < cfg.e₀)
    (caps : ∀ u : ℝ, 0 ≤ u → u ≤ s →
      cfg.NativeFineJointCap k u (cfg.N k ^ (-b)) (cfg.N k ^ (-(2 * s))))
    (hmesh : 16 * cfg.K k * cfg.N k ^ (-b) ≤ cfg.N k ^ (-s))
    (hfiner : cfg.N k ^ (-b) ≤ cfg.N k ^ (-(4 * s)))
    (hcost : 23040 * cfg.K k ^ 2 ≤ cfg.N k ^ ε)
    (g : ℤ × ℤ × ℤ) (c₀ c₁ r τ₁ τ₂ : ℝ)
    (har : cfg.N k ^ (-s) ≤ r) (hr4 : r ≤ 4) (hc₁ : |c₁| ≤ 4 * cfg.K k)
    (hτ : τ₁ ≤ τ₂) :
    cfg.μ k (cfg.goodSet k s ∩
      {p | cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1 = g ∧
        p.2 ∈ Icc τ₁ τ₂ ∧ |cfg.hidden k p - (c₀ + p.2 * c₁)| ≤ r}) ≤
      ENNReal.ofReal (cfg.N k ^ ε * (τ₂ - τ₁ + cfg.N k ^ (-(4 * s))) *
        cfg.groupWeight k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) g * r ^ cfg.d) := by
  letI : IsProbabilityMeasure (cfg.π k) := (h.basic k).2.2.1
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hNgt : 1 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith
  have hK : 1 ≤ cfg.K k := h.subpower.1 k
  have hK0 : 0 ≤ cfg.K k := by linarith
  let a := cfg.N k ^ (-s)
  let v := cfg.N k ^ (-(2 * s))
  let δ := cfg.N k ^ (-b)
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  have hv : 0 < v := Real.rpow_pos_of_pos hN _
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hva : v ≤ a := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hdefa : cfg.N k ^ (-cfg.e₀) ≤ a := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  let U := cfg.goodSet k s ∩ {p : α × ℝ | cfg.groupCode k a v p.1 = g ∧
    p.2 ∈ Icc τ₁ τ₂ ∧ |cfg.hidden k p - (c₀ + p.2 * c₁)| ≤ r}
  by_cases hU : U.Nonempty
  swap
  · rw [show cfg.goodSet k s ∩ {p : α × ℝ | cfg.groupCode k a v p.1 = g ∧
        p.2 ∈ Icc τ₁ τ₂ ∧ |cfg.hidden k p - (c₀ + p.2 * c₁)| ≤ r} = ∅ from
        Set.not_nonempty_iff_eq_empty.mp hU, measure_empty]
    exact zero_le
  obtain ⟨y₀, hy₀⟩ := hU
  let p : Fin 3 → ℝ := ![cfg.b k y₀.1 0, cfg.b k y₀.1 1, cfg.b k y₀.1 3]
  let R := min r 1
  have hR : 0 < R := lt_min (ha.trans_le har) (by norm_num)
  have hRa : a ≤ R := le_min har ha1
  have hR1 : R ≤ 1 := min_le_right _ _
  have hRr : R ≤ r := min_le_left _ _
  have hrR : r ≤ 4 * R := by
    by_cases hr1 : r ≤ 1
    · rw [show R = r from min_eq_left hr1]
      linarith [hR]
    · rw [show R = 1 from min_eq_right (le_of_lt (lt_of_not_ge hr1))]
      linarith
  let u := -Real.logb (cfg.N k) R
  have hu : 0 ≤ u := by
    have hh := (Real.logb_le_iff_le_rpow hNgt hR).mpr
      (by simpa using hR1 : R ≤ cfg.N k ^ (0 : ℝ))
    dsimp [u]
    linarith
  have hus : u ≤ s := by
    have hh := (Real.le_logb_iff_rpow_le hNgt hR).mpr hRa
    dsimp [u]
    linarith
  have hscale : cfg.N k ^ (-u) = R := by
    dsimp [u]
    simpa only [neg_neg] using Real.rpow_logb hN (ne_of_gt hNgt) hR
  let L : Fin 4 → ℝ := ![c₀, c₁, 0, 0]
  have hG : 1 ≤ 16 * cfg.K k := by linarith
  have hKG : cfg.K k ≤ 16 * cfg.K k := by linarith
  have hp₀ : |p 0| ≤ 16 * cfg.K k :=
    (show |cfg.b k y₀.1 0| ≤ cfg.K k from hy₀.1.2.1).trans hKG
  have hp₂ : |p 2| ≤ 16 * cfg.K k :=
    (show |cfg.b k y₀.1 3| ≤ cfg.K k from hy₀.1.2.2.2.1).trans hKG
  have hL : ∀ e : Fin 3, |L e.succ| ≤ 16 * cfg.K k := by
    intro e
    fin_cases e
    · exact hc₁.trans (by linarith)
    · simpa [L] using (show 0 ≤ 16 * cfg.K k by positivity)
    · simpa [L] using (show 0 ≤ 16 * cfg.K k by positivity)
  have hgaps (y : α × ℝ) (hy : y ∈ U) :
      |cfg.b k y.1 0 - p 0| ≤ a ∧ |cfg.b k y.1 1 - p 1| ≤ a ∧
      |cfg.b k y.1 3 - p 2| ≤ a :=
    cfg.groupCode_coordinate_gaps k a v ha hv hva y.1 y₀.1 (hy.2.1.trans hy₀.2.1.symm)
  have hunit (y : α × ℝ) (hy : y ∈ U) : |y.2| ≤ 1 := by
    rw [abs_of_nonneg hy.1.1.1]
    exact hy.1.1.2
  have hgeometry (y : α × ℝ) (hy : y ∈ U) :=
    native_initial_group_geometry (cfg.b k y.1) p y.2 a (hunit y hy)
      (hgaps y hy).1 (hgaps y hy).2.1 (hgaps y hy).2.2
      (hy.1.2.2.2.2.2.2.2.1.trans hdefa)
  have hh := original_group_band_joint_cap (cfg.μ k) U
    (fun y : α × ℝ => nativeHorizontalPoint (cfg.b k y.1) y.2)
    (cfg.hidden k) (fun y : α × ℝ => ⌊cfg.b k y.1 3 / v⌋) g.2.2
    δ R (τ₂ - τ₁ + δ) a (16 * cfg.K k) τ₁ (cfg.K k) (R ^ cfg.d)
    (cfg.π k {w | ⌊w / v⌋ = g.2.2}) p L hδ hR hG hK0 (Real.rpow_nonneg hR.le _)
    (by linarith) hmesh (by
      have hh : 3 * δ ≤ a := (mul_le_mul_of_nonneg_right (by linarith : 3 ≤ 16 * cfg.K k) hδ.le).trans hmesh
      exact hh.trans hRa) hp₀ hp₂ hL
    (by
      intro y hy
      change y.2 ∈ Icc τ₁ (τ₁ + (τ₂ - τ₁ + δ))
      exact ⟨hy.2.2.1.1, by linarith [hy.2.2.1.2]⟩)
    (fun y hy => (hgeometry y hy).1) (fun y hy => (hgeometry y hy).2) (by
      intro y hy
      have heq : affineBaseValue L (nativeHorizontalPoint (cfg.b k y.1) y.2) = c₀ + y.2 * c₁ := by
        simp [affineBaseValue, L, Fin.sum_univ_succ, nativeHorizontalPoint]
        ring
      rw [heq]
      exact hy.2.2.2.trans (hrR.trans (mul_le_mul_of_nonneg_right (by linarith : 4 ≤ 16 * cfg.K k) hR.le)))
    (by intro y hy; exact congrArg (fun z => z.2.2) hy.2.1) (by
      intro q n
      have hh := caps u hu hus q n g.2.2
      rw [hscale] at hh
      exact hh)
  let πr := (cfg.π k).real {w | ⌊w / v⌋ = g.2.2}
  have hπeq : ENNReal.ofReal πr = cfg.π k {w | ⌊w / v⌋ = g.2.2} :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [← hπeq, ← ENNReal.ofReal_mul (by positivity :
    0 ≤ 1440 * cfg.K k * (16 * cfg.K k) * (τ₂ - τ₁ + δ) * a ^ 2 * R ^ cfg.d)] at hh
  refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hRpow : R ^ cfg.d ≤ r ^ cfg.d := Real.rpow_le_rpow hR.le hRr h.dimension_nonneg
  have hπ0 : 0 ≤ πr := measureReal_nonneg
  calc
    _ = (23040 * cfg.K k ^ 2) * (τ₂ - τ₁ + δ) * a ^ 2 * R ^ cfg.d * πr := by ring
    _ ≤ (cfg.N k ^ ε) * (τ₂ - τ₁ + cfg.N k ^ (-(4 * s))) * a ^ 2 * r ^ cfg.d * πr := by
      gcongr
    _ = _ := by dsimp [groupWeight, πr, a, v]; ring

/-- (B) The group band cap: a fixed initial-position/velocity group, a time
window and an affine hidden band of half-width `r` cost the window length (up
to a fine mesh) times the group reference weight `π(v-bin) a²` times `r^d`. -/
theorem Valid.eventually_group_band_cap (h : cfg.Valid) {s : ℝ} (hs : 0 < s)
    (hse : s < cfg.e₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (g : ℤ × ℤ × ℤ) (c₀ c₁ r τ₁ τ₂ : ℝ),
      cfg.N k ^ (-s) ≤ r → r ≤ 4 → |c₁| ≤ 4 * cfg.K k → τ₁ ≤ τ₂ →
      cfg.μ k (cfg.goodSet k s ∩
          {p | cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1 = g ∧
            p.2 ∈ Icc τ₁ τ₂ ∧ |cfg.hidden k p - (c₀ + p.2 * c₁)| ≤ r}) ≤
        ENNReal.ofReal (cfg.N k ^ ε * (τ₂ - τ₁ + cfg.N k ^ (-(4 * s))) *
          cfg.groupWeight k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) g * r ^ cfg.d) := by
  let b := 8 * s + 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hmesh := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k) h.scale_limit
    h.subpower.1 h.subpower.2 1 (show -b < -s by dsimp [b]; linarith)
    (show (0 : ℝ) ≤ 16 by norm_num)
  have hcost := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    (fun k => by linarith [h.scale k] : ∀ k, 1 ≤ cfg.N k) h.scale_limit
    h.subpower.1 h.subpower.2 2 hε (show (0 : ℝ) ≤ 23040 by norm_num)
  filter_upwards [h.eventually_native_fine_joint_cap_range s b (2 * s) hs.le hb (by positivity),
    hmesh, hcost] with k caps hm hc
  intro g c₀ c₁ r τ₁ τ₂ har hr hc₁ hτ
  apply group_band_cap_at_sample h hs hse caps (by simpa only [pow_one] using hm.le)
    (Real.rpow_le_rpow_of_exponent_le (by linarith [h.scale k]) (by dsimp [b]; linarith))
    (by simpa only [Real.rpow_zero, mul_one] using hc.le) g c₀ c₁ r τ₁ τ₂ har hr hc₁ hτ

/-- (S) The group scalar support count: in one time bin of width `a`, the
covered incidences of one group meet at most `N^ε a^(-d)` hidden bins. -/
theorem Valid.eventually_group_support (h : cfg.Valid) {s : ℝ} (hs : 0 < s) (hsU : s ≤ cfg.U)
    (hse : s < cfg.e₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (g : ℤ × ℤ × ℤ) (τ : ℤ), ∃ J : Finset ℤ,
      (J.card : ℝ) ≤ cfg.N k ^ ε * (cfg.N k ^ (-s)) ^ (-cfg.d) ∧
      ∀ p ∈ cfg.goodSet k s,
        cfg.groupCode k (cfg.N k ^ (-s)) (cfg.N k ^ (-(2 * s))) p.1 = g →
        ⌊p.2 / cfg.N k ^ (-s)⌋ = τ → ⌊cfg.hidden k p / cfg.N k ^ (-s)⌋ ∈ J := by
  classical
  filter_upwards [h.eventually_group_scalar_bins s ε hs hsU hε] with k hS
  intro g τ
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hN1 : 1 ≤ cfg.N k := by linarith [h.scale k]
  have hK : 0 ≤ cfg.K k := by linarith [h.subpower.1 k]
  let a := cfg.N k ^ (-s)
  let v := cfg.N k ^ (-(2 * s))
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  have hv : 0 < v := Real.rpow_pos_of_pos hN _
  have hva : v ≤ a := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hdefa : cfg.N k ^ (-cfg.e₀) ≤ a := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  let U := cfg.goodSet k s ∩ {y : α × ℝ | cfg.groupCode k a v y.1 = g ∧ ⌊y.2 / a⌋ = τ}
  by_cases hU : U.Nonempty
  swap
  · refine ⟨∅, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · intro y hy hg ht
      exact False.elim (hU ⟨y, hy, hg, ht⟩)
  obtain ⟨y₀, hy₀⟩ := hU
  let p : Fin 3 → ℝ := ![cfg.b k y₀.1 0, cfg.b k y₀.1 1, cfg.b k y₀.1 3]
  have hp₀ : |p 0| ≤ cfg.K k := hy₀.1.2.1
  have hp₂ : |p 2| ≤ cfg.K k := hy₀.1.2.2.2.1
  have hcov (y : α × ℝ) (hy : y ∈ U) : ∃ i : Fin (cfg.n k s),
      y.1 ∈ cfg.B k s i ∧ y.2 ∈ I (cfg.T k s) (cfg.j k s i) := hy.1.2.2.2.2.2.2.2.2
  obtain ⟨i₀, _, _⟩ := hcov y₀ hy₀
  let label : α × ℝ → Fin (cfg.n k s) := fun y =>
    if hy : y ∈ U then Classical.choose (hcov y hy) else i₀
  have hlabel : ∀ y ∈ U, y.1 ∈ cfg.B k s (label y) ∧
      y.2 ∈ I (cfg.T k s) (cfg.j k s (label y)) := by
    intro y hy
    dsimp only [label]
    rw [dite_eq_left hy]
    exact Classical.choose_spec (hcov y hy)
  have hgaps (y : α × ℝ) (hy : y ∈ U) :
      |cfg.b k y.1 0 - p 0| ≤ a ∧ |cfg.b k y.1 1 - p 1| ≤ a ∧
      |cfg.b k y.1 3 - p 2| ≤ a :=
    cfg.groupCode_coordinate_gaps k a v ha hv hva y.1 y₀.1 (hy.2.1.trans hy₀.2.1.symm)
  have hunit (y : α × ℝ) (hy : y ∈ U) : |y.2| ≤ 1 := by
    rw [abs_of_nonneg hy.1.1.1]
    exact hy.1.1.2
  have hhidden (y : α × ℝ) (hy : y ∈ U) : |(cfg.x k y.1 y.2) 3| ≤ 3 * cfg.K k := by
    change |cfg.b k y.1 2 + y.2 * cfg.b k y.1 5| ≤ 3 * cfg.K k
    calc
      _ ≤ |cfg.b k y.1 2| + |y.2 * cfg.b k y.1 5| := abs_add_le _ _
      _ ≤ cfg.K k + 1 * (2 * cfg.K k) := add_le_add hy.1.2.2.2.2.2.1 (by
        rw [abs_mul]
        exact mul_le_mul (hunit y hy) hy.1.2.2.2.2.2.2.1 (abs_nonneg _) zero_le_one)
      _ = _ := by ring
  have hgeometry (y : α × ℝ) (hy : y ∈ U) :=
    native_initial_group_geometry (cfg.b k y.1) p y.2 a (hunit y hy)
      (hgaps y hy).1 (hgaps y hy).2.1 (hgaps y hy).2.2
      (hy.1.2.2.2.2.2.2.2.1.trans hdefa)
  obtain ⟨J, hJ, hcover⟩ := hS U label p τ hp₀ hp₂ hlabel hhidden
    (fun y hy => hy.2.2) (by
      intro y hy
      convert (hgeometry y hy).1 using 1 <;>
        dsimp [x, referenceZ, nativeHorizontalPoint] <;> congr 1 <;> ring) (by
      intro y hy
      convert (hgeometry y hy).2 using 1 <;>
        dsimp [x, referenceY, nativeHorizontalPoint] <;> congr 1 <;> ring)
  refine ⟨J, ?_, ?_⟩
  · change (J.card : ℝ) ≤ cfg.N k ^ ε / a ^ cfg.d at hJ
    change (J.card : ℝ) ≤ cfg.N k ^ ε * a ^ (-cfg.d)
    rw [Real.rpow_neg ha.le]
    simpa only [div_eq_mul_inv] using hJ
  · intro y hy hg ht
    exact hcover y ⟨hy, hg, ht⟩

end Data

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
