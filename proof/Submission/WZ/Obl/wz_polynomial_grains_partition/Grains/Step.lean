-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.Grains.Step.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_polynomial_grains_partition.Grains.Basic
import Submission.WZ.Obl.wz_polynomial_grains_partition.Grains.Merge

/-!
# One step of the grains recursion, with merged children

For a piece `A` in a box of side `ℓ`, x0325's step partitions `Leb|A` into `D^3 = 8^p` sign
cells (Guth–Katz), cuts by the `D^3` subcubes and removes the wall `W` (the `100δ`-thickening of
the zero sets and of the grid planes). Here the sign-cell pieces of each subcube are then merged
into blocks (`Merge.exists_merge`): a block weighs at most `2 |A| / D^3`, and the blocks of
positive mass number at most `2 D^3` (each subcube has at most `mass / τ + 1` blocks). A `δ`-tube
still meets at most `20 D` blocks. The leaves (wall pieces, by subcube) lie in the
`100δ`-thickening of the zero set of one polynomial of degree `≤ 18 D`.
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
namespace Grains

open MeasureTheory

namespace StepAux

open SplitAux

lemma zeroSet_mul (Q₁ Q₂ : MvPolynomial (Fin 3) ℝ) :
    zeroSet (Q₁ * Q₂) = zeroSet Q₁ ∪ zeroSet Q₂ := by
  ext x
  simp [zeroSet, mul_eq_zero]

/-- The product of the grid plane polynomials. -/
noncomputable def gridPoly (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) : MvPolynomial (Fin 3) ℝ :=
  ∏ rk : Fin 3 × Fin (D + 1), planePoly a h D rk

lemma zeroSet_gridPoly (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) :
    zeroSet (gridPoly a h D) = planes a h D := by
  ext x
  simp only [zeroSet, gridPoly, Set.mem_ofPred_eq, map_prod, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, eval_planePoly, planes, sub_eq_zero]
  constructor
  · rintro ⟨⟨r, k⟩, hk⟩
    exact ⟨r, k, hk⟩
  · rintro ⟨r, k, hk⟩
    exact ⟨⟨r, k⟩, hk⟩

lemma planePoly_ne_zero (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) (rk : Fin 3 × Fin (D + 1)) :
    planePoly a h D rk ≠ 0 := by
  intro h0
  have := congrArg (MvPolynomial.eval (fun _ : Fin 3 => a rk.1 + ((rk.2 : ℕ) : ℝ) * h + 1)) h0
  simp [planePoly] at this

lemma gridPoly_ne_zero (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) : gridPoly a h D ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun rk _ => planePoly_ne_zero a h D rk

lemma totalDegree_gridPoly_le (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) :
    (gridPoly a h D).totalDegree ≤ 3 * (D + 1) := by
  unfold gridPoly
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ rk, (planePoly a h D rk).totalDegree ≤ ∑ _rk : Fin 3 × Fin (D + 1), 1 :=
        Finset.sum_le_sum fun rk _ => totalDegree_planePoly_le a h D rk
    _ = 3 * (D + 1) := by simp

lemma wall_eq (Q : MvPolynomial (Fin 3) ℝ) (a : Fin 3 → ℝ) (h : ℝ) (D : ℕ) (ρ : ℝ) :
    wall Q a h D ρ = Metric.thickening ρ (zeroSet (Q * gridPoly a h D)) := by
  rw [zeroSet_mul, zeroSet_gridPoly]
  rfl

/-- A box lies in the `ρ`-thickening of its grid planes once the mesh is `< ρ`. -/
lemma box_subset_thickening_planes (a : Fin 3 → ℝ) {ℓ ρ : ℝ} (hℓ : 0 < ℓ) {D : ℕ}
    (hD : 0 < D) (hρ : ℓ / D < ρ) :
    box a ℓ ⊆ Metric.thickening ρ (planes a (ℓ / D) D) := by
  intro x hx
  have hsub := idx_mem_subbox a hℓ hD hx
  set k : Fin D := idx a (ℓ / D) hD x 0 with hk
  set c : ℝ := a 0 + ((k : ℕ) : ℝ) * (ℓ / D) - x 0 with hc
  let y : Space := x + c • EuclideanSpace.single 0 1
  have hy0 : y 0 = a 0 + ((k : ℕ) : ℝ) * (ℓ / D) := by
    simp [y, hc]
  have hx0 := hsub 0
  refine Metric.mem_thickening_iff.mpr ⟨y, ⟨0, ⟨(k : ℕ), by omega⟩, hy0⟩, ?_⟩
  have hdist : dist x y = |c| := by
    rw [dist_eq_norm]
    have : x - y = -(c • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) := by
      simp [y]
    rw [this, norm_neg, norm_smul, PiLp.norm_single, norm_one, mul_one,
      Real.norm_eq_abs]
  rw [hdist, abs_lt]
  constructor
  · linarith [hx0.2]
  · linarith [hx0.1, (show (0 : ℝ) < ℓ / D from div_pos hℓ (Nat.cast_pos.mpr hD))]

end StepAux

/-- Index of the merged children: subcube and block label. -/
abbrev Idx (p : ℕ) := (Fin 3 → Fin (2 ^ p)) × Fin (8 ^ p + 1)

open SplitAux StepAux in
/-- One step of the grains recursion, with merged children. -/
theorem split_step (p : ℕ) (hp : 1 ≤ p) {δ : ℝ} (hδ : 0 < δ) (A : Set Space)
    (hA : MeasurableSet A) (a : Fin 3 → ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (hAQ : A ⊆ box a ℓ) :
    ∃ (C : Idx p → Set Space) (L : (Fin 3 → Fin (2 ^ p)) → Set Space)
      (Q : MvPolynomial (Fin 3) ℝ),
      (∀ i, MeasurableSet (C i) ∧ C i ⊆ A ∧ C i ⊆ subbox a ℓ i.1) ∧
      (∀ q, MeasurableSet (L q) ∧ L q ⊆ A ∧ L q ⊆ subbox a ℓ q) ∧
      (Pairwise fun i j => Disjoint (C i) (C j)) ∧
      (Pairwise fun q q' => Disjoint (L q) (L q')) ∧
      (∀ i q, Disjoint (C i) (L q)) ∧
      A = (⋃ i, C i) ∪ ⋃ q, L q ∧
      (∀ i, ((2 : ENNReal) ^ p) ^ 3 * volume (C i) ≤ 2 * volume A) ∧
      (Q ≠ 0 ∧ Q.totalDegree ≤ 18 * 2 ^ p ∧
        ∀ q, L q ⊆ Metric.thickening (100 * δ) (zeroSet Q)) ∧
      (Finset.univ.filter fun i => volume (C i) ≠ 0).card ≤ 2 * 8 ^ p ∧
      (∀ x v : Space, ‖v‖ ≤ 1 →
        ({i | (Metric.thickening δ (segment ℝ x (x + v)) ∩ C i).Nonempty}.ncard : ℝ) ≤
          20 * 2 ^ p) ∧
      (∀ x v : Space, ‖v‖ ≤ 1 → δ ≤ ℓ / 2 ^ p →
        ({q | (Metric.thickening δ (segment ℝ x (x + v)) ∩ L q).Nonempty}.ncard : ℝ) ≤
          400 * 2 ^ p) := by
  classical
  have hD : 0 < 2 ^ p := pow_pos (by norm_num) p
  have hDR : ((2 ^ p : ℕ) : ℝ) = (2 : ℝ) ^ p := by push_cast; ring
  set h : ℝ := ℓ / ((2 ^ p : ℕ) : ℝ) with hhdef
  -- `volume.restrict A` is a finite measure, absolutely continuous w.r.t. `volume`
  have hAfin : volume A < ⊤ :=
    calc volume A ≤ volume (box a ℓ) := measure_mono hAQ
      _ = ENNReal.ofReal (ℓ * ℓ * ℓ) := volume_box_eq a hℓ.le
      _ < ⊤ := ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (volume.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAfin⟩
  have hμ : volume.restrict A ≪ volume :=
    Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  obtain ⟨P, hP0, hPdeg, hPμ, -⟩ := guth_katz_partitioning_ac (volume.restrict A) hμ (3 * p)
  -- degree budget
  have hS : ∑ j, (P j).totalDegree ≤ 12 * 2 ^ p := by
    have h1 := sum_totalDegree_cube_le (3 * p) P hPdeg
    have h2 : 1600 * 2 ^ (3 * p) ≤ (12 * 2 ^ p) ^ 3 := by
      rw [mul_pow, ← pow_mul, mul_comm p 3]
      exact Nat.mul_le_mul_right _ (by norm_num)
    exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num)).mp (h1.trans h2)
  have hQ0 : (∏ j, P j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hP0 j
  have hQdeg : (∏ j, P j).totalDegree ≤ 12 * 2 ^ p :=
    (MvPolynomial.totalDegree_finsetProd _ _).trans hS
  set W : Set Space := wall (∏ j, P j) a h (2 ^ p) (100 * δ) with hW
  have hWmeas : MeasurableSet W := Metric.isOpen_thickening.measurableSet
  have hsubbox : ∀ x ∈ A, x ∈ subbox a ℓ (idx a h hD x) := fun x hx =>
    idx_mem_subbox a hℓ hD (hAQ hx)
  -- x0325's children: sign pattern and subcube
  set c0 : (Fin (3 * p) → Bool) × (Fin 3 → Fin (2 ^ p)) → Set Space :=
    child A W P a h hD with hc0
  have hc0meas : ∀ i, MeasurableSet (c0 i) := fun i =>
    hA.inter (hWmeas.compl.inter
      ((measurableSet_sgn_eq P i.1).inter (measurableSet_idx_eq a h hD i.2)))
  have hc0disj : Pairwise fun i j => Disjoint (c0 i) (c0 j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact hij (Prod.ext (hxi.2.2.1.symm.trans hxj.2.2.1) (hxi.2.2.2.symm.trans hxj.2.2.2))
  have hc0mass : ∀ i, ((2 : ENNReal) ^ p) ^ 3 * volume (c0 i) ≤ volume A := by
    intro i
    have hcell := hPμ i.1
    rw [Measure.restrict_apply_univ, Measure.restrict_apply' hA] at hcell
    refine le_trans ?_ hcell
    rw [← pow_mul, mul_comm p 3]
    refine mul_le_mul_right (measure_mono ?_) _
    intro x hx
    obtain ⟨hxA, hxW, hxs, -⟩ := hx
    refine ⟨fun j => ?_, hxA⟩
    have hne : MvPolynomial.eval (fun i => x i) (P j) ≠ 0 := fun h0 =>
      hxW (Metric.self_subset_thickening (by positivity) _
        (Or.inl ((mem_zeroSet_prod P).mpr ⟨j, h0⟩)))
    rw [← hxs]
    simp only [sgn]
    by_cases hpos : 0 < MvPolynomial.eval (fun i => x i) (P j)
    · simp [hpos]
    · simp only [hpos, decide_false, Bool.false_eq_true, ite_false]
      exact lt_of_le_of_ne (not_lt.mp hpos) hne
  have hc0fin : ∀ i, volume (c0 i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hAfin.ne (measure_mono fun x hx => hx.1)
  -- the merging labels
  set D3 : ENNReal := ((2 : ENNReal) ^ p) ^ 3 with hD3
  have hD3ne : D3 ≠ 0 := by rw [hD3]; positivity
  have hD3top : D3 ≠ ⊤ := by rw [hD3]; exact ENNReal.pow_ne_top (ENNReal.pow_ne_top (by simp))
  have h83 : ((2 : ℝ) ^ p) ^ 3 = (8 : ℝ) ^ p := by
    rw [← pow_mul, mul_comm p 3, pow_mul]; norm_num
  have hD3R : D3.toReal = (8 : ℝ) ^ p := by
    rw [hD3, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat, h83]
  obtain ⟨g, hgb, hgmass, hgcount⟩ : ∃ g : (Fin 3 → Fin (2 ^ p)) → (Fin (3 * p) → Bool) → ℕ,
      (∀ q s, g q s ≤ 8 ^ p) ∧
      (∀ q m, D3 * ∑ s ∈ Finset.univ.filter (fun s => g q s = m), volume (c0 (s, q)) ≤
        2 * volume A) ∧
      ((Finset.univ : Finset (Fin 3 → Fin (2 ^ p))).sigma (fun q =>
        (Finset.univ.filter fun s => volume (c0 (s, q)) ≠ 0).image (g q))).card ≤ 2 * 8 ^ p := by
    rcases eq_or_ne (volume A) 0 with hA0 | hA0
    · -- a null piece: one label
      refine ⟨fun _ _ => 0, fun _ _ => Nat.zero_le _, fun q m => ?_, ?_⟩
      · have : ∀ s, volume (c0 (s, q)) = 0 := fun s =>
          measure_mono_null (fun x hx => hx.1) hA0
        simp [this]
      · have : ∀ q s, volume (c0 (s, q)) = 0 := fun q s =>
          measure_mono_null (fun x hx => hx.1) hA0
        simp [this]
    · set τ : ℝ := (volume A).toReal / (8 : ℝ) ^ p with hτ
      have hAR : 0 < (volume A).toReal := ENNReal.toReal_pos hA0 hAfin.ne
      have hτpos : 0 < τ := by rw [hτ]; positivity
      set w : (Fin 3 → Fin (2 ^ p)) → (Fin (3 * p) → Bool) → ℝ :=
        fun q s => (volume (c0 (s, q))).toReal with hw
      have hw0 : ∀ q s, 0 ≤ w q s := fun q s => ENNReal.toReal_nonneg
      have hwτ : ∀ q s, w q s ≤ τ := by
        intro q s
        have h1 := hc0mass (s, q)
        have h2 : (D3 * volume (c0 (s, q))).toReal ≤ (volume A).toReal :=
          ENNReal.toReal_mono hAfin.ne h1
        rw [ENNReal.toReal_mul, hD3R] at h2
        rw [hw, hτ, le_div_iff₀ (by positivity)]
        simp only at h2 ⊢
        linarith
      choose g hg1 hg2 using fun q => Merge.exists_merge (w q) (hw0 q) hτpos (hwτ q)
      -- total weight
      have htot : ∑ q, ∑ s, w q s ≤ (volume A).toReal := by
        have hU : ⋃ i, c0 i ⊆ A := Set.iUnion_subset fun i x hx => hx.1
        have h1 : ∑ i, volume (c0 i) ≤ volume A := by
          have hU' := measure_iUnion (μ := volume) hc0disj hc0meas
          rw [tsum_fintype] at hU'
          rw [← hU']
          exact measure_mono hU
        have h2 : (∑ i, volume (c0 i)).toReal ≤ (volume A).toReal :=
          ENNReal.toReal_mono hAfin.ne h1
        rw [ENNReal.toReal_sum (fun i _ => hc0fin i), Fintype.sum_prod_type] at h2
        rw [Finset.sum_comm]
        simpa [hw] using h2
      have hwq : ∀ q, ∑ s, w q s ≤ (volume A).toReal := by
        intro q
        refine le_trans ?_ htot
        exact Finset.single_le_sum (f := fun q => ∑ s, w q s)
          (fun q _ => Finset.sum_nonneg fun s _ => hw0 q s) (Finset.mem_univ q)
      refine ⟨g, fun q s => ?_, fun q m => ?_, ?_⟩
      · have h1 := hg2 q s
        have h2 : (∑ s, w q s) / τ ≤ (8 : ℝ) ^ p := by
          rw [div_le_iff₀ hτpos, hτ]
          field_simp
          linarith [hwq q]
        exact_mod_cast h1.trans h2
      · have h1 := hg1 q m
        have hfin : ∀ s ∈ Finset.univ.filter (fun s => g q s = m), volume (c0 (s, q)) ≠ ⊤ :=
          fun s _ => hc0fin _
        have hsum : ∑ s ∈ Finset.univ.filter (fun s => g q s = m), volume (c0 (s, q)) =
            ENNReal.ofReal (∑ s ∈ Finset.univ.filter (fun s => g q s = m), w q s) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => hw0 q s)]
          exact Finset.sum_congr rfl fun s _ => (ENNReal.ofReal_toReal (hc0fin _)).symm
        rw [hsum]
        calc D3 * ENNReal.ofReal (∑ s ∈ Finset.univ.filter (fun s => g q s = m), w q s)
            ≤ D3 * ENNReal.ofReal (2 * τ) := by gcongr
          _ = 2 * volume A := by
              have e1 : D3 * ENNReal.ofReal (2 * τ) = ENNReal.ofReal (D3.toReal * (2 * τ)) := by
                rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hD3top]
              have e2 : D3.toReal * (2 * τ) = 2 * (volume A).toReal := by
                rw [hD3R, hτ]; field_simp
              rw [e1, e2, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
                ENNReal.ofReal_toReal hAfin.ne]
      · -- each subcube has at most `mass / τ + 1` labels
        have hq : ∀ q, (((Finset.univ.filter fun s => volume (c0 (s, q)) ≠ 0).image (g q)).card
            : ℝ) ≤ (∑ s, w q s) / τ + 1 := by
          intro q
          have hsub : (Finset.univ.filter fun s => volume (c0 (s, q)) ≠ 0).image (g q) ⊆
              Finset.range (⌊(∑ s, w q s) / τ⌋₊ + 1) := by
            intro m hm
            rw [Finset.mem_image] at hm
            obtain ⟨s, -, rfl⟩ := hm
            rw [Finset.mem_range, Nat.lt_succ_iff]
            exact Nat.le_floor (hg2 q s)
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_range] at h1
          have h2 : ((⌊(∑ s, w q s) / τ⌋₊ + 1 : ℕ) : ℝ) ≤ (∑ s, w q s) / τ + 1 := by
            push_cast
            have h0 : 0 ≤ (∑ s, w q s) / τ :=
              div_nonneg (Finset.sum_nonneg fun s _ => hw0 q s) hτpos.le
            have := Nat.floor_le h0
            linarith
          exact le_trans (by exact_mod_cast h1) h2
        rw [Finset.card_sigma]
        have h1 : (∑ q, (((Finset.univ.filter fun s => volume (c0 (s, q)) ≠ 0).image
            (g q)).card : ℝ)) ≤ ∑ q : Fin 3 → Fin (2 ^ p), ((∑ s, w q s) / τ + 1) :=
          Finset.sum_le_sum fun q _ => hq q
        have h2 : ∑ q : Fin 3 → Fin (2 ^ p), ((∑ s, w q s) / τ + 1) ≤ 2 * (8 : ℝ) ^ p := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
            Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, mul_one]
          have h3 : (∑ q, ∑ s, w q s) / τ ≤ (8 : ℝ) ^ p := by
            rw [div_le_iff₀ hτpos, hτ]
            field_simp
            linarith
          have h4 : (((2 ^ p) ^ 3 : ℕ) : ℝ) = (8 : ℝ) ^ p := by
            push_cast
            rw [← pow_mul, mul_comm, pow_mul]
            norm_num
          rw [h4]
          linarith
        have := h1.trans h2
        exact_mod_cast this
  -- the merged children
  let C : Idx p → Set Space := fun i =>
    {x | x ∈ A ∧ x ∉ W ∧ idx a h hD x = i.1 ∧ g i.1 (sgn P x) = (i.2 : ℕ)}
  have hCeq : ∀ i : Idx p, C i = ⋃ s ∈ Finset.univ.filter (fun s => g i.1 s = (i.2 : ℕ)),
      c0 (s, i.1) := by
    intro i
    ext x
    simp only [C, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, exists_prop, hc0, child]
    constructor
    · rintro ⟨hxA, hxW, hxq, hxg⟩
      exact ⟨sgn P x, hxg, hxA, hxW, rfl, hxq⟩
    · rintro ⟨s, hs, hxA, hxW, hxs, hxq⟩
      exact ⟨hxA, hxW, hxq, by rw [hxs]; exact hs⟩
  have hCvol : ∀ i : Idx p, volume (C i) =
      ∑ s ∈ Finset.univ.filter (fun s => g i.1 s = (i.2 : ℕ)), volume (c0 (s, i.1)) := by
    intro i
    rw [hCeq i, measure_biUnion_finset]
    · intro s _ t _ hst
      exact hc0disj (fun h => hst (congrArg Prod.fst h))
    · intro s _
      exact hc0meas _
  set Qall : MvPolynomial (Fin 3) ℝ := (∏ j, P j) * gridPoly a h (2 ^ p) with hQall
  refine ⟨C, leaf A W a h hD, Qall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- children: measurable, in `A`, in their subcube
    intro i
    refine ⟨?_, fun x hx => hx.1, fun x hx => ?_⟩
    · rw [hCeq i]
      exact Finset.measurableSet_biUnion _ fun s _ => hc0meas _
    · rw [← hx.2.2.1]
      exact hsubbox x hx.1
  · -- leaves: measurable, in `A`, in their subcube
    intro q
    refine ⟨?_, fun x hx => hx.1, fun x hx => ?_⟩
    · exact hA.inter (hWmeas.inter (measurableSet_idx_eq a h hD q))
    · rw [← hx.2.2]
      exact hsubbox x hx.1
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hij
    refine Prod.ext (hxi.2.2.1.symm.trans hxj.2.2.1) (Fin.ext ?_)
    rw [← hxi.2.2.2, ← hxj.2.2.2, hxi.2.2.1.symm.trans hxj.2.2.1]
  · intro q q' hqq
    rw [Set.disjoint_left]
    intro x hxq hxq'
    exact hqq (hxq.2.2.symm.trans hxq'.2.2)
  · intro i q
    rw [Set.disjoint_left]
    intro x hxi hxq
    exact hxi.2.1 hxq.2.1
  · apply Set.Subset.antisymm
    · intro x hxA
      by_cases hxW : x ∈ W
      · exact Or.inr (Set.mem_iUnion.mpr ⟨idx a h hD x, hxA, hxW, rfl⟩)
      · refine Or.inl (Set.mem_iUnion.mpr
          ⟨(idx a h hD x, ⟨g (idx a h hD x) (sgn P x), Nat.lt_succ_of_le (hgb _ _)⟩), ?_⟩)
        exact ⟨hxA, hxW, rfl, rfl⟩
    · exact Set.union_subset (Set.iUnion_subset fun i x hx => hx.1)
        (Set.iUnion_subset fun q x hx => hx.1)
  · -- mass of the merged children
    intro i
    rw [hCvol i]
    exact hgmass i.1 i.2
  · -- the polynomial of the leaves
    refine ⟨mul_ne_zero hQ0 (gridPoly_ne_zero _ _ _), ?_, fun q => ?_⟩
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      have h1 := totalDegree_gridPoly_le a h (2 ^ p)
      have h2 : 1 ≤ 2 ^ p := hD
      omega
    · intro x hx
      have hxW : x ∈ W := hx.2.1
      rw [hW, wall_eq] at hxW
      exact hxW
  · -- the number of children of positive mass
    have hsub : (Finset.univ.filter fun i : Idx p => volume (C i) ≠ 0) ⊆
        ((Finset.univ : Finset (Fin 3 → Fin (2 ^ p))).sigma (fun q =>
          (Finset.univ.filter fun s => volume (c0 (s, q)) ≠ 0).image (g q))).image
          (fun y => (y.1, (⟨min y.2 (8 ^ p), Nat.lt_succ_of_le (min_le_right _ _)⟩ :
            Fin (8 ^ p + 1)))) := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [hCvol i] at hi
      obtain ⟨s, hs, hsne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi.2
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_image]
      refine ⟨⟨i.1, (i.2 : ℕ)⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma, Finset.mem_image]
        exact ⟨Finset.mem_univ _, s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsne⟩, hs.2⟩
      · refine Prod.ext rfl (Fin.ext ?_)
        simp only
        exact min_eq_left (Nat.lt_succ_iff.mp i.2.isLt)
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans hgcount)
  · -- a tube meets few merged children
    intro x v _
    have h1 := child_ncard_le A P a hℓ hδ hD hAQ x v
    have h2 : (∑ j, (P j).totalDegree) + 3 * (2 ^ p + 1) + 1 ≤ 20 * 2 ^ p := by
      have : 1 ≤ 2 ^ p := hD
      omega
    have hsub : {i : Idx p | (Metric.thickening δ (segment ℝ x (x + v)) ∩ C i).Nonempty} ⊆
        (fun j : (Fin (3 * p) → Bool) × (Fin 3 → Fin (2 ^ p)) =>
          ((j.2, ⟨min (g j.2 j.1) (8 ^ p), Nat.lt_succ_of_le (min_le_right _ _)⟩) : Idx p)) ''
        {j | (Metric.thickening δ (segment ℝ x (x + v)) ∩
          child A (wall (∏ j, P j) a (ℓ / ((2 ^ p : ℕ) : ℝ)) (2 ^ p) (100 * δ)) P a
            (ℓ / ((2 ^ p : ℕ) : ℝ)) hD j).Nonempty} := by
      rintro i ⟨y, hyT, hyA, hyW, hyq, hyg⟩
      refine ⟨(sgn P y, i.1), ⟨y, hyT, hyA, hyW, rfl, hyq⟩, ?_⟩
      refine Prod.ext rfl (Fin.ext ?_)
      simp only
      rw [hyg]
      exact min_eq_left (Nat.lt_succ_iff.mp i.2.isLt)
    have h3 := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le
      (Set.toFinite _))
    exact_mod_cast h3.trans (h1.trans h2)
  · -- a tube meets few leaves
    intro x v hv hδℓ
    have hsub :
        {q | (Metric.thickening δ (segment ℝ x (x + v)) ∩ leaf A W a h hD q).Nonempty} ⊆
        {q | (Metric.thickening δ (segment ℝ x (x + v)) ∩ subbox a ℓ q).Nonempty} := by
      rintro q ⟨y, hy1, hy2⟩
      refine ⟨y, hy1, ?_⟩
      rw [← hy2.2.2]
      exact hsubbox y hy2.1
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := tube_subbox_ncard a hδ (D := 2 ^ p) hD (by rw [hDR]; exact hδℓ) x v hv
    refine le_trans (Nat.cast_le.mpr h1) (h2.trans_eq ?_)
    rw [hDR]

end Grains
end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
