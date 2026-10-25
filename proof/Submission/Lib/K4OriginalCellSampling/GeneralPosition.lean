/- Adapted from: here:o204
   Session x0749, branch x0749, checked original-law sampling and geometry.
   Original source file and earlier provenance are retained below. -/
/- Adapted from LOT obligation o143, branch x0491, commit 13cbafc0;
   original file Submission/Lib/K4GeneralPositionSampling.lean.
   The final selection theorem is strengthened to require domination only
   on the bins of the selected width. The original attribution follows. -/
import Mathlib

/-!
# Directions in general position by independent sampling

Let `μ` be a probability law of planar velocities which is *broad*: every closed strip
`{v | |⟪n, v⟫ - c| ≤ δ}` with a unit normal `n` has mass at most `κ`. Then `n`
independent draws `v₀, …, vₙ₋₁` give lifted directions `(1, vᵢ) ∈ ℝ³` whose triple
determinants are all at least `δ²` in absolute value, except on an event of probability
at most `2 n³ κ`.

The determinant is the one used by the seven-direction tests of the local restoration
assertion: the matrix whose rows are three lifted directions.

The second part turns this into one fixed choice of seven directions for many states at once
(the paper's "palette domination ... averaging fixes one tuple ... fine bin centers" step in
the restoration of quadratic tests, Section 6):

* `exists_piece_density_ge`: density pigeonhole over countably many disjoint pieces;
* `mass_of_large_ratio`: Markov extraction of the states carrying a large ratio;
* `abs_tripleDet_sub_le`: moving three points changes their triple determinant by
  at most `8 e (2 R + e)`;
* `exists_seven_bins`: seven bins of side `w`, centers in general position, with joint mass at
  least a fixed fraction of their palette mass;
* `exists_seven_bins_states_of_bin_domination`: with domination on the selected-width bins, the states charging all
  seven bins carry a fixed fraction `/(2 K⁷)` of the mass, and each charges every bin.
-/

namespace Submission.Lib.K4OriginalCellSampling.Sampling

open MeasureTheory Set
open scoped ENNReal

/-- The lifted direction `(1, v)` of a planar velocity. -/
noncomputable def lift (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![1, v 0, v 1]

/-- The determinant of three lifted directions, in the matrix form of the
seven-direction tests. -/
noncomputable def tripleDet (u v w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Matrix.det (Matrix.of fun r t : Fin 3 => (![lift u, lift v, lift w] r) t)

lemma lift_zero (v : EuclideanSpace ℝ (Fin 2)) : lift v 0 = 1 := rfl

lemma tripleDet_eq (u v w : EuclideanSpace ℝ (Fin 2)) :
    tripleDet u v w = (v 0 - u 0) * (w 1 - u 1) - (v 1 - u 1) * (w 0 - u 0) := by
  simp only [tripleDet, lift, Matrix.det_fin_three]
  simp
  ring

/-- Breadth of a planar law: every closed strip of half-width `δ` has mass at most `κ`. -/
def StripBreadth (μ : Measure (EuclideanSpace ℝ (Fin 2))) (δ : ℝ) (κ : ℝ≥0∞) : Prop :=
  ∀ (m : EuclideanSpace ℝ (Fin 2)) (c : ℝ), ‖m‖ = 1 →
    μ {x | |inner ℝ m x - c| ≤ δ} ≤ κ

/-- A product event whose slices in one coordinate are small is small. -/
theorem pi_measure_le_of_slices {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {n : ℕ} (k : Fin (n + 1)) (B : Set (Fin (n + 1) → X))
    (hB : MeasurableSet B) {κ : ℝ≥0∞}
    (hslice : ∀ v : Fin (n + 1) → X, μ {x | Function.update v k x ∈ B} ≤ κ) :
    (Measure.pi fun _ : Fin (n + 1) => μ) B ≤ κ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) k
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) k
  let ν : Measure (Fin n → X) := Measure.pi fun _ : Fin n => μ
  have hS : MeasurableSet (e.symm ⁻¹' B) := e.symm.measurable hB
  have hpre : (Measure.pi fun _ : Fin (n + 1) => μ) B = (μ.prod ν) (e.symm ⁻¹' B) := by
    rw [← hmp.measure_preimage hS.nullMeasurableSet]
    congr 1
    ext v
    simp only [mem_preimage]
    change v ∈ B ↔ e.symm (e v) ∈ B
    rw [MeasurableEquiv.symm_apply_apply]
  rw [hpre, Measure.prod_apply_symm hS]
  calc
    ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' (e.symm ⁻¹' B)) ∂ν ≤ ∫⁻ _y, κ ∂ν := by
      apply lintegral_mono
      intro w
      show μ ((fun x => (x, w)) ⁻¹' (e.symm ⁻¹' B)) ≤ κ
      rcases isEmpty_or_nonempty X with hX | hX
      · have hempty : (fun x => (x, w)) ⁻¹' (e.symm ⁻¹' B) = ∅ := Set.eq_empty_of_isEmpty _
        rw [hempty, measure_empty]
        simp
      · have hset : (fun x => (x, w)) ⁻¹' (e.symm ⁻¹' B) =
            {x | Function.update (Fin.insertNth k (Classical.arbitrary X) w) k x ∈ B} := by
          ext x
          simp only [mem_preimage, mem_ofPred_eq, Fin.update_insertNth]
          rfl
        rw [hset]
        exact hslice _
    _ = κ := by simp [ν]

/-- A planar ball of radius `δ` lies in a strip of half-width `δ`. -/
lemma ball_subset_strip (u : EuclideanSpace ℝ (Fin 2)) (δ : ℝ) :
    {x : EuclideanSpace ℝ (Fin 2) | ‖x - u‖ < δ} ⊆
      {x | |inner ℝ (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) x - u 0| ≤ δ} := by
  intro x hx
  simp only [mem_ofPred_eq, EuclideanSpace.inner_single_left, map_one, one_mul] at hx ⊢
  have h := PiLp.norm_apply_le (x - u) 0
  simp only [PiLp.sub_apply, Real.norm_eq_abs] at h
  linarith

lemma norm_single_zero : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
  simp

/-- For two separated velocities, a small triple determinant confines the third one to a
strip of half-width `δ`. -/
lemma small_det_subset_strip {u v : EuclideanSpace ℝ (Fin 2)} {δ : ℝ} (hδ : 0 < δ)
    (huv : δ ≤ ‖v - u‖) :
    ∃ (m : EuclideanSpace ℝ (Fin 2)) (c : ℝ), ‖m‖ = 1 ∧
      {x | |tripleDet u v x| < δ ^ 2} ⊆ {x | |inner ℝ m x - c| ≤ δ} := by
  set d := v - u with hd
  have hdpos : 0 < ‖d‖ := lt_of_lt_of_le hδ huv
  let r : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-(d 1), d 0]
  have hr : ‖r‖ = ‖d‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [r, Fin.sum_univ_two]
    ring
  refine ⟨‖d‖⁻¹ • r, inner ℝ (‖d‖⁻¹ • r) u, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, hr, inv_mul_cancel₀ hdpos.ne']
  · intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    have hdet : tripleDet u v x = inner ℝ r (x - u) := by
      rw [tripleDet_eq, PiLp.inner_apply, Fin.sum_univ_two]
      simp [r, hd]
      ring
    rw [← inner_sub_right, inner_smul_left]
    simp only [conj_trivial]
    rw [← hdet, abs_mul, abs_inv, abs_norm]
    rw [inv_mul_le_iff₀ hdpos]
    nlinarith [abs_nonneg (tripleDet u v x)]

/-- Independent broad draws are in general position with high probability. -/
theorem general_position_of_breadth (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsProbabilityMeasure μ] {δ : ℝ} (hδ : 0 < δ) {κ : ℝ≥0∞} (hb : StripBreadth μ δ κ)
    (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => μ)
        {v | ∃ i j k : Fin (n + 1), i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
          |tripleDet (v i) (v j) (v k)| < δ ^ 2} ≤ 2 * ((n + 1) ^ 3 : ℝ≥0∞) * κ := by
  classical
  -- the bad event is covered by the close-pair events and the thin-strip events
  let close : Fin (n + 1) → Fin (n + 1) → Set (Fin (n + 1) → EuclideanSpace ℝ (Fin 2)) :=
    fun i j => {v | ‖v j - v i‖ < δ}
  let thin : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) →
      Set (Fin (n + 1) → EuclideanSpace ℝ (Fin 2)) :=
    fun i j k => {v | δ ≤ ‖v j - v i‖ ∧ |tripleDet (v i) (v j) (v k)| < δ ^ 2}
  have hcont_det : ∀ i j k : Fin (n + 1),
      Continuous fun v : Fin (n + 1) → EuclideanSpace ℝ (Fin 2) =>
        tripleDet (v i) (v j) (v k) := by
    intro i j k
    simp only [tripleDet_eq]
    fun_prop
  have hcover : {v : Fin (n + 1) → EuclideanSpace ℝ (Fin 2) | ∃ i j k : Fin (n + 1), i ≠ j ∧
      i ≠ k ∧ j ≠ k ∧ |tripleDet (v i) (v j) (v k)| < δ ^ 2} ⊆
      ⋃ i, ⋃ j, ⋃ k, ({v | i ≠ j ∧ i ≠ k ∧ j ≠ k} ∩ (close i j ∪ thin i j k)) := by
    intro v ⟨i, j, k, hij, hik, hjk, hsmall⟩
    simp only [mem_iUnion]
    refine ⟨i, j, k, ⟨hij, hik, hjk⟩, ?_⟩
    by_cases hc : ‖v j - v i‖ < δ
    · exact Or.inl hc
    · exact Or.inr ⟨not_lt.mp hc, hsmall⟩
  have hclose : ∀ i j : Fin (n + 1), i ≠ j →
      (Measure.pi fun _ : Fin (n + 1) => μ) (close i j) ≤ κ := by
    intro i j hij
    apply pi_measure_le_of_slices μ j
    · exact measurableSet_lt
        (continuous_norm.comp ((continuous_apply j).sub (continuous_apply i))).measurable
        measurable_const
    · intro v
      have hsub : {x | Function.update v j x ∈ close i j} ⊆ {x | ‖x - v i‖ < δ} := by
        intro x hx
        simp only [close, mem_ofPred_eq, Function.update_self,
          Function.update_of_ne hij] at hx
        exact hx
      exact (measure_mono (hsub.trans (ball_subset_strip (v i) δ))).trans
        (hb _ _ norm_single_zero)
  have hthin : ∀ i j k : Fin (n + 1), i ≠ k → j ≠ k →
      (Measure.pi fun _ : Fin (n + 1) => μ) (thin i j k) ≤ κ := by
    intro i j k hik hjk
    apply pi_measure_le_of_slices μ k
    · exact (measurableSet_le measurable_const
        (continuous_norm.comp ((continuous_apply j).sub (continuous_apply i))).measurable).inter
        (measurableSet_lt ((hcont_det i j k).abs.measurable) measurable_const)
    · intro v
      by_cases hsep : δ ≤ ‖v j - v i‖
      · obtain ⟨m, c, hm, hsub⟩ := small_det_subset_strip hδ hsep
        have hsub' : {x | Function.update v k x ∈ thin i j k} ⊆
            {x | |tripleDet (v i) (v j) x| < δ ^ 2} := by
          intro x hx
          simp only [thin, mem_ofPred_eq, Function.update_self,
            Function.update_of_ne hik, Function.update_of_ne hjk] at hx
          exact hx.2
        exact (measure_mono (hsub'.trans hsub)).trans (hb m c hm)
      · have hempty : {x | Function.update v k x ∈ thin i j k} = ∅ := by
          ext x
          simp only [thin, mem_ofPred_eq, Function.update_of_ne hik,
            Function.update_of_ne hjk, mem_empty_iff_false, iff_false, not_and]
          intro h
          exact absurd h hsep
        rw [hempty, measure_empty]
        simp
  calc
    _ ≤ (Measure.pi fun _ : Fin (n + 1) => μ)
          (⋃ i, ⋃ j, ⋃ k, ({v | i ≠ j ∧ i ≠ k ∧ j ≠ k} ∩ (close i j ∪ thin i j k))) :=
      measure_mono hcover
    _ ≤ ∑ i, ∑ j, ∑ k, (Measure.pi fun _ : Fin (n + 1) => μ)
          ({v | i ≠ j ∧ i ≠ k ∧ j ≠ k} ∩ (close i j ∪ thin i j k)) := by
      refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), ∑ _k : Fin (n + 1), 2 * κ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => ?_
      by_cases hd : i ≠ j ∧ i ≠ k ∧ j ≠ k
      · have hset : {v : Fin (n + 1) → EuclideanSpace ℝ (Fin 2) | i ≠ j ∧ i ≠ k ∧ j ≠ k} =
            univ := by
          ext v
          simp [hd]
        rw [hset, univ_inter]
        calc
          _ ≤ (Measure.pi fun _ : Fin (n + 1) => μ) (close i j) +
              (Measure.pi fun _ : Fin (n + 1) => μ) (thin i j k) := measure_union_le _ _
          _ ≤ κ + κ := add_le_add (hclose i j hd.1) (hthin i j k hd.2.1 hd.2.2)
          _ = 2 * κ := (two_mul κ).symm
      · have hset : {v : Fin (n + 1) → EuclideanSpace ℝ (Fin 2) | i ≠ j ∧ i ≠ k ∧ j ≠ k} =
            ∅ := by
          ext v
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact hd
        rw [hset, empty_inter, measure_empty]
        simp
    _ = 2 * ((n + 1) ^ 3 : ℝ≥0∞) * κ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-! ### Selecting seven bins with common witness states -/

/-- Density pigeonhole: if countably many disjoint pieces carry `Λ`-mass at least `X > 0`
and `ν`-mass at most `P`, one piece of positive `Λ`-mass has `Λ ≥ (X / P) ν` on it. -/
theorem exists_piece_density_ge {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (Λ ν : Measure α) (B : ι → Set α) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Function.onFun Disjoint B)) {X P : ℝ≥0∞}
    (hX0 : X ≠ 0) (hXtop : X ≠ ∞) (hP0 : P ≠ 0) (hPtop : P ≠ ∞)
    (hΛ : X ≤ Λ (⋃ i, B i)) (hν : ν (⋃ i, B i) ≤ P) :
    ∃ i, 0 < Λ (B i) ∧ X / P * ν (B i) ≤ Λ (B i) := by
  by_contra hcon
  push Not at hcon
  have hU : Λ (⋃ i, B i) = ∑' i, Λ (B i) := measure_iUnion hdisj hB
  have hV : ν (⋃ i, B i) = ∑' i, ν (B i) := measure_iUnion hdisj hB
  have hpos : ∃ i, 0 < Λ (B i) := by
    by_contra h
    push Not at h
    have h0 : ∑' i, Λ (B i) = 0 := by
      simp only [ENNReal.tsum_eq_zero]
      exact fun i => le_antisymm (h i) (zero_le)
    rw [hU, h0] at hΛ
    exact hX0 (le_antisymm hΛ (zero_le))
  obtain ⟨i0, hi0⟩ := hpos
  have hle : ∀ i, Λ (B i) ≤ X / P * ν (B i) := fun i => by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ Λ (B i)) with h | h
    · rw [← h]
      exact zero_le
    · exact (hcon i h).le
  have hsum : ∑' i, X / P * ν (B i) ≤ X := by
    rw [ENNReal.tsum_mul_left, ← hV]
    calc X / P * ν (⋃ i, B i) ≤ X / P * P := mul_le_mul_right hν _
      _ = X := ENNReal.div_mul_cancel hP0 hPtop
  have hfin : ∑' i, Λ (B i) ≠ ∞ := by
    refine ne_top_of_le_ne_top hXtop ?_
    exact (ENNReal.tsum_le_tsum hle).trans hsum
  have hlt : ∑' i, Λ (B i) < ∑' i, X / P * ν (B i) :=
    ENNReal.tsum_lt_tsum hfin hle (hcon i0 hi0)
  rw [hU] at hΛ
  exact absurd (hΛ.trans_lt (hlt.trans_le hsum)) (lt_irrefl X)

/-- Markov extraction: if `∑ m a ≥ X Q` while every `a ≤ K Q`, the states with
`X Q ≤ 2 M a` carry mass at least `X / (2 K)`, where `M` bounds the total mass. -/
theorem mass_of_large_ratio {ι : Type*} [Fintype ι] (m a : ι → ℝ≥0∞) {X Q K M : ℝ≥0∞}
    (hQ0 : Q ≠ 0) (hQtop : Q ≠ ∞) (hM0 : M ≠ 0) (hMtop : M ≠ ∞) (hKtop : K ≠ ∞)
    (hsum : X * Q ≤ ∑ s, m s * a s) (ha : ∀ s, a s ≤ K * Q) (hM : ∑ s, m s ≤ M) :
    X ≤ 2 * K * ∑ s ∈ Finset.univ.filter (fun s => X * Q ≤ 2 * M * a s), m s := by
  classical
  set G := Finset.univ.filter (fun s => X * Q ≤ 2 * M * a s) with hG
  have hsplit : ∑ s, m s * a s = ∑ s ∈ G, m s * a s + ∑ s ∈ Gᶜ, m s * a s := by
    rw [← Finset.sum_add_sum_compl G]
  -- the complement contributes at most `X Q / 2`
  have hcomp : 2 * M * ∑ s ∈ Gᶜ, m s * a s ≤ M * (X * Q) := by
    rw [Finset.mul_sum]
    calc ∑ s ∈ Gᶜ, 2 * M * (m s * a s) ≤ ∑ s ∈ Gᶜ, m s * (X * Q) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hs' : ¬ X * Q ≤ 2 * M * a s := by
            simpa [hG] using hs
          push Not at hs'
          calc 2 * M * (m s * a s) = m s * (2 * M * a s) := by ring
            _ ≤ m s * (X * Q) := mul_le_mul_right hs'.le _
      _ = (∑ s ∈ Gᶜ, m s) * (X * Q) := by rw [Finset.sum_mul]
      _ ≤ M * (X * Q) := by
          refine mul_le_mul_left ?_ _
          exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans hM
  -- the good states contribute at most `K Q m(G)`
  have hgood : ∑ s ∈ G, m s * a s ≤ K * Q * ∑ s ∈ G, m s := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    calc m s * a s ≤ m s * (K * Q) := mul_le_mul_right (ha s) _
      _ = K * Q * m s := by ring
  -- combine: `2 M X Q ≤ 2 M (K Q m(G)) + M X Q`
  have h2M : (2 : ℝ≥0∞) * M ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hMtop
  have hkey : 2 * M * (X * Q) ≤ 2 * M * (K * Q * ∑ s ∈ G, m s) + M * (X * Q) := by
    calc 2 * M * (X * Q) ≤ 2 * M * ∑ s, m s * a s := mul_le_mul_right hsum _
      _ = 2 * M * ∑ s ∈ G, m s * a s + 2 * M * ∑ s ∈ Gᶜ, m s * a s := by
          rw [hsplit, mul_add]
      _ ≤ 2 * M * (K * Q * ∑ s ∈ G, m s) + M * (X * Q) :=
          add_le_add (mul_le_mul_right hgood _) hcomp
  -- cancel `M Q`
  have hXQfin : M * (X * Q) ≠ ∞ ∨ True := Or.inr trivial
  by_cases hXtop : X = ∞
  · -- then `hsum` forces an infinite sum, impossible with finite `K Q M`
    exfalso
    have hfin : ∑ s, m s * a s ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := K * Q * M) ?_ ?_
      · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hKtop hQtop) hMtop
      · calc ∑ s, m s * a s ≤ ∑ s, m s * (K * Q) :=
              Finset.sum_le_sum fun s _ => mul_le_mul_right (ha s) _
          _ = (∑ s, m s) * (K * Q) := by rw [Finset.sum_mul]
          _ ≤ M * (K * Q) := mul_le_mul_left hM _
          _ = K * Q * M := by ring
    rw [hXtop, ENNReal.top_mul hQ0] at hsum
    exact hfin (top_le_iff.mp hsum)
  have hMXQ : M * (X * Q) ≠ ∞ := ENNReal.mul_ne_top hMtop (ENNReal.mul_ne_top hXtop hQtop)
  -- `2 M X Q - M X Q = M X Q ≤ 2 M K Q m(G)`
  have hsub : M * (X * Q) ≤ 2 * M * (K * Q * ∑ s ∈ G, m s) := by
    have h1 : 2 * M * (X * Q) = M * (X * Q) + M * (X * Q) := by ring
    rw [h1] at hkey
    exact (ENNReal.add_le_add_iff_right hMXQ).mp hkey
  -- divide by `M Q`
  have hrw : 2 * M * (K * Q * ∑ s ∈ G, m s) = M * ((2 * K * ∑ s ∈ G, m s) * Q) := by ring
  rw [hrw] at hsub
  have hsub2 : X * Q ≤ (2 * K * ∑ s ∈ G, m s) * Q :=
    (ENNReal.mul_le_mul_iff_right hM0 hMtop).mp hsub
  exact (ENNReal.mul_le_mul_iff_left hQ0 hQtop).mp hsub2

/-! ### Planar bins and their centers -/

/-- The index of the half-open planar bin of side `w` containing `v`. -/
noncomputable def binIndex (w : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℤ :=
  fun c => ⌊v c / w⌋

/-- The half-open planar bin of side `w` with index `β`. -/
def bin (w : ℝ) (β : Fin 2 → ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {v | binIndex w v = β}

/-- The center of the bin of side `w` with index `β`. -/
noncomputable def binCenter (w : ℝ) (β : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun c => w * ((β c : ℝ) + 1 / 2))

lemma measurableSet_bin (w : ℝ) (β : Fin 2 → ℤ) : MeasurableSet (bin w β) := by
  have : bin w β = ⋂ c : Fin 2, (fun v : EuclideanSpace ℝ (Fin 2) => ⌊v c / w⌋) ⁻¹' {β c} := by
    ext v
    simp [bin, binIndex, funext_iff]
  rw [this]
  refine MeasurableSet.iInter fun c => ?_
  have hm : Measurable fun v : EuclideanSpace ℝ (Fin 2) => ⌊v c / w⌋ := by
    have h1 : Measurable fun v : EuclideanSpace ℝ (Fin 2) => v c / w :=
      (show Continuous fun v : EuclideanSpace ℝ (Fin 2) => v c / w by fun_prop).measurable
    exact Int.measurable_floor.comp h1
  exact hm (measurableSet_singleton _)

lemma mem_bin_binIndex (w : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : v ∈ bin w (binIndex w v) :=
  rfl

/-- A point of a bin is within `w / 2` of its center in each coordinate. -/
lemma abs_sub_binCenter_le {w : ℝ} (hw : 0 < w) {β : Fin 2 → ℤ} {v : EuclideanSpace ℝ (Fin 2)}
    (hv : v ∈ bin w β) (c : Fin 2) : |v c - binCenter w β c| ≤ w / 2 := by
  have hβ : ⌊v c / w⌋ = β c := congrFun hv c
  have h1 : (β c : ℝ) ≤ v c / w := by rw [← hβ]; exact Int.floor_le _
  have h2 : v c / w < (β c : ℝ) + 1 := by rw [← hβ]; exact Int.lt_floor_add_one _
  have h1' : w * (β c : ℝ) ≤ v c := by
    have := mul_le_mul_of_nonneg_left h1 hw.le
    rwa [mul_div_cancel₀ _ hw.ne'] at this
  have h2' : v c < w * ((β c : ℝ) + 1) := by
    have := mul_lt_mul_of_pos_left h2 hw
    rwa [mul_div_cancel₀ _ hw.ne'] at this
  have hc : binCenter w β c = w * ((β c : ℝ) + 1 / 2) := rfl
  rw [hc, abs_le]
  constructor <;> nlinarith

/-- Moving the three points of a triple determinant by at most `e` in each coordinate, from
points with coordinates at most `R`, changes it by at most `8 e (2 R + e)`. -/
lemma abs_tripleDet_sub_le {u v x u' v' x' : EuclideanSpace ℝ (Fin 2)} {e R : ℝ}
    (he : 0 ≤ e) (hu : ∀ c, |u c| ≤ R) (hv : ∀ c, |v c| ≤ R) (hx : ∀ c, |x c| ≤ R)
    (hu' : ∀ c, |u c - u' c| ≤ e) (hv' : ∀ c, |v c - v' c| ≤ e)
    (hx' : ∀ c, |x c - x' c| ≤ e) :
    |tripleDet u v x - tripleDet u' v' x'| ≤ 8 * e * (2 * R + e) := by
  rw [tripleDet_eq, tripleDet_eq]
  -- abbreviations for the four differences
  set A := v 0 - u 0
  set B := x 1 - u 1
  set C := v 1 - u 1
  set D := x 0 - u 0
  set A' := v' 0 - u' 0
  set B' := x' 1 - u' 1
  set C' := v' 1 - u' 1
  set D' := x' 0 - u' 0
  have hR : 0 ≤ R := le_trans (abs_nonneg _) (hu 0)
  have bA : |A| ≤ 2 * R := by
    calc |A| ≤ |v 0| + |u 0| := abs_sub _ _
      _ ≤ 2 * R := by linarith [hv 0, hu 0]
  have bC : |C| ≤ 2 * R := by
    calc |C| ≤ |v 1| + |u 1| := abs_sub _ _
      _ ≤ 2 * R := by linarith [hv 1, hu 1]
  have dA : |A - A'| ≤ 2 * e := by
    have : A - A' = (v 0 - v' 0) - (u 0 - u' 0) := by simp only [A, A']; ring
    rw [this]
    calc |(v 0 - v' 0) - (u 0 - u' 0)| ≤ |v 0 - v' 0| + |u 0 - u' 0| := abs_sub _ _
      _ ≤ 2 * e := by linarith [hv' 0, hu' 0]
  have dB : |B - B'| ≤ 2 * e := by
    have : B - B' = (x 1 - x' 1) - (u 1 - u' 1) := by simp only [B, B']; ring
    rw [this]
    calc |(x 1 - x' 1) - (u 1 - u' 1)| ≤ |x 1 - x' 1| + |u 1 - u' 1| := abs_sub _ _
      _ ≤ 2 * e := by linarith [hx' 1, hu' 1]
  have dC : |C - C'| ≤ 2 * e := by
    have : C - C' = (v 1 - v' 1) - (u 1 - u' 1) := by simp only [C, C']; ring
    rw [this]
    calc |(v 1 - v' 1) - (u 1 - u' 1)| ≤ |v 1 - v' 1| + |u 1 - u' 1| := abs_sub _ _
      _ ≤ 2 * e := by linarith [hv' 1, hu' 1]
  have dD : |D - D'| ≤ 2 * e := by
    have : D - D' = (x 0 - x' 0) - (u 0 - u' 0) := by simp only [D, D']; ring
    rw [this]
    calc |(x 0 - x' 0) - (u 0 - u' 0)| ≤ |x 0 - x' 0| + |u 0 - u' 0| := abs_sub _ _
      _ ≤ 2 * e := by linarith [hx' 0, hu' 0]
  have bB' : |B'| ≤ 2 * R + 2 * e := by
    have hB : |B| ≤ 2 * R := by
      calc |B| ≤ |x 1| + |u 1| := abs_sub _ _
        _ ≤ 2 * R := by linarith [hx 1, hu 1]
    calc |B'| = |B - (B - B')| := by ring_nf
      _ ≤ |B| + |B - B'| := abs_sub _ _
      _ ≤ 2 * R + 2 * e := by linarith
  have bD' : |D'| ≤ 2 * R + 2 * e := by
    have hD : |D| ≤ 2 * R := by
      calc |D| ≤ |x 0| + |u 0| := abs_sub _ _
        _ ≤ 2 * R := by linarith [hx 0, hu 0]
    calc |D'| = |D - (D - D')| := by ring_nf
      _ ≤ |D| + |D - D'| := abs_sub _ _
      _ ≤ 2 * R + 2 * e := by linarith
  have key : A * B - C * D - (A' * B' - C' * D') =
      (A - A') * B' + A * (B - B') - ((C - C') * D' + C * (D - D')) := by ring
  rw [key]
  have t1 : |(A - A') * B'| ≤ 2 * e * (2 * R + 2 * e) := by
    rw [abs_mul]; exact mul_le_mul dA bB' (abs_nonneg _) (by linarith)
  have t2 : |A * (B - B')| ≤ 2 * R * (2 * e) := by
    rw [abs_mul]; exact mul_le_mul bA dB (abs_nonneg _) (by linarith)
  have t3 : |(C - C') * D'| ≤ 2 * e * (2 * R + 2 * e) := by
    rw [abs_mul]; exact mul_le_mul dC bD' (abs_nonneg _) (by linarith)
  have t4 : |C * (D - D')| ≤ 2 * R * (2 * e) := by
    rw [abs_mul]; exact mul_le_mul bC dD (abs_nonneg _) (by linarith)
  calc |(A - A') * B' + A * (B - B') - ((C - C') * D' + C * (D - D'))|
      ≤ |(A - A') * B'| + |A * (B - B')| + (|(C - C') * D'| + |C * (D - D')|) := by
        refine (abs_sub _ _).trans ?_
        exact add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ ≤ 8 * e * (2 * R + e) := by nlinarith

/-! ### Selecting seven bins -/

/-- Tuples of seven velocities in general position, with speeds at most `R`. -/
def goodTuples (δ R : ℝ) : Set (Fin 7 → EuclideanSpace ℝ (Fin 2)) :=
  {v | (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k → δ ^ 2 ≤ |tripleDet (v i) (v j) (v k)|) ∧
    ∀ i, ‖v i‖ ≤ R}

/-- Under breadth and a speed tail bound, seven independent draws are good with probability
at least `1 - (686 κ + 7 τ)`. -/
lemma one_sub_le_pi_goodTuples (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsProbabilityMeasure μ] {δ R : ℝ} (hδ : 0 < δ) {κ τ : ℝ≥0∞} (hb : StripBreadth μ δ κ)
    (htail : μ {v | R < ‖v‖} ≤ τ) :
    1 - (686 * κ + 7 * τ) ≤ (Measure.pi fun _ : Fin 7 => μ) (goodTuples δ R) := by
  set P := Measure.pi fun _ : Fin 7 => μ with hP
  have hbad := general_position_of_breadth μ hδ hb 6
  have h686 : (2 : ℝ≥0∞) * (((6 : ℕ) : ℝ≥0∞) + 1) ^ 3 = 686 := by norm_num
  rw [h686] at hbad
  have htails : ∀ i : Fin 7, P {v | R < ‖v i‖} ≤ τ := by
    intro i
    have hset : {v : Fin 7 → EuclideanSpace ℝ (Fin 2) | R < ‖v i‖} =
        Set.univ.pi (Function.update (fun _ => Set.univ) i {x | R < ‖x‖}) := by
      ext v
      simp only [mem_ofPred_eq, mem_univ_pi]
      constructor
      · intro h j
        by_cases hj : j = i
        · subst hj
          simpa using h
        · simp [Function.update_of_ne hj]
      · intro h
        simpa using h i
    rw [hset, hP, Measure.pi_pi, Finset.prod_eq_single i]
    · simpa using htail
    · intro j _ hj
      simp [Function.update_of_ne hj]
    · simp
  have hcompl : (goodTuples δ R)ᶜ ⊆
      {v | ∃ i j k : Fin 7, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ |tripleDet (v i) (v j) (v k)| < δ ^ 2} ∪
        ⋃ i : Fin 7, {v | R < ‖v i‖} := by
    intro v hv
    simp only [goodTuples, mem_compl_iff, mem_ofPred_eq, not_and_or, not_forall, not_le] at hv
    rcases hv with ⟨i, j, k, hij, hik, hjk, h⟩ | ⟨i, h⟩
    · exact Or.inl ⟨i, j, k, hij, hik, hjk, h⟩
    · exact Or.inr (mem_iUnion.mpr ⟨i, h⟩)
  have hbadc : P (goodTuples δ R)ᶜ ≤ 686 * κ + 7 * τ := by
    calc P (goodTuples δ R)ᶜ
        ≤ P ({v | ∃ i j k : Fin 7, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
              |tripleDet (v i) (v j) (v k)| < δ ^ 2} ∪ ⋃ i : Fin 7, {v | R < ‖v i‖}) :=
          measure_mono hcompl
      _ ≤ P {v | ∃ i j k : Fin 7, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
              |tripleDet (v i) (v j) (v k)| < δ ^ 2} + P (⋃ i : Fin 7, {v | R < ‖v i‖}) :=
          measure_union_le _ _
      _ ≤ 686 * κ + ∑ i : Fin 7, P {v | R < ‖v i‖} :=
          add_le_add hbad (measure_iUnion_fintype_le _ _)
      _ ≤ 686 * κ + ∑ _i : Fin 7, τ := add_le_add le_rfl (Finset.sum_le_sum fun i _ => htails i)
      _ = 686 * κ + 7 * τ := by simp
  have h1 : (1 : ℝ≥0∞) ≤ P (goodTuples δ R) + P (goodTuples δ R)ᶜ := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ = P (goodTuples δ R ∪ (goodTuples δ R)ᶜ) := by rw [union_compl_self]
      _ ≤ _ := measure_union_le _ _
  calc 1 - (686 * κ + 7 * τ) ≤ 1 - P (goodTuples δ R)ᶜ := tsub_le_tsub_left hbadc 1
    _ ≤ P (goodTuples δ R) := tsub_le_iff_right.mpr h1

/-- **Selection of seven direction bins.** Finitely many states with weights `m s` and
broad velocity laws `μ s` (closed strips of half-width `δ` carry mass `≤ κ`, speeds above `R`
carry mass `≤ τ`, with `686 κ + 7 τ < 1`). For a finite reference measure `π` (the palette)
and any bin side `w > 0`, some seven bins have centers whose lifted triple determinants are at
least `δ² - 4 w (2 R + w / 2)`, and their joint mass `∑ₛ m s ∏ᵢ μ s (binᵢ)` is positive and at
least `(1 - (686 κ + 7 τ)) (∑ₛ m s) / (π univ)⁷` times their palette mass `∏ᵢ π (binᵢ)`. -/
theorem exists_seven_bins {ι : Type*} [Fintype ι]
    (m : ι → ℝ≥0∞) (μ : ι → Measure (EuclideanSpace ℝ (Fin 2)))
    [∀ s, IsProbabilityMeasure (μ s)]
    (π : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure π] (hπ0 : π univ ≠ 0)
    {δ R w : ℝ} (hδ : 0 < δ) (hw : 0 < w) {κ τ : ℝ≥0∞}
    (hb : ∀ s, StripBreadth (μ s) δ κ) (htail : ∀ s, μ s {v | R < ‖v‖} ≤ τ)
    (hgood : 686 * κ + 7 * τ < 1) (hM0 : ∑ s, m s ≠ 0) (hMtop : ∑ s, m s ≠ ∞) :
    ∃ β : Fin 7 → Fin 2 → ℤ,
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        δ ^ 2 - 4 * w * (2 * R + w / 2) ≤
          |tripleDet (binCenter w (β i)) (binCenter w (β j)) (binCenter w (β k))|) ∧
      (∀ i c, |binCenter w (β i) c| ≤ R + w / 2) ∧
      0 < ∑ s, m s * ∏ i, μ s (bin w (β i)) ∧
      (1 - (686 * κ + 7 * τ)) * (∑ s, m s) / π univ ^ 7 * ∏ i, π (bin w (β i)) ≤
        ∑ s, m s * ∏ i, μ s (bin w (β i)) := by
  classical
  set M := ∑ s, m s with hM
  set Λ : Measure (Fin 7 → EuclideanSpace ℝ (Fin 2)) :=
    ∑ s, m s • Measure.pi (fun _ : Fin 7 => μ s) with hΛ
  set ν : Measure (Fin 7 → EuclideanSpace ℝ (Fin 2)) := Measure.pi (fun _ : Fin 7 => π) with hν
  let box : (Fin 7 → Fin 2 → ℤ) → Set (Fin 7 → EuclideanSpace ℝ (Fin 2)) :=
    fun β => Set.univ.pi fun i => bin w (β i)
  let G : Set (Fin 7 → Fin 2 → ℤ) := {β | (box β ∩ goodTuples δ R).Nonempty}
  let B : G → Set (Fin 7 → EuclideanSpace ℝ (Fin 2)) := fun β => box β.1
  have hB : ∀ β, MeasurableSet (B β) := fun β =>
    MeasurableSet.univ_pi fun i => measurableSet_bin w _
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro β β' hne
    rw [Function.onFun, Set.disjoint_left]
    intro v hv hv'
    apply hne
    apply Subtype.ext
    funext i
    have h1 : v i ∈ bin w (β.1 i) := hv i (mem_univ i)
    have h2 : v i ∈ bin w (β'.1 i) := hv' i (mem_univ i)
    exact h1.symm.trans h2
  have hcover : goodTuples δ R ⊆ ⋃ β, B β := by
    intro v hv
    refine mem_iUnion.mpr ⟨⟨fun i => binIndex w (v i), ?_⟩, ?_⟩
    · exact ⟨v, fun i _ => mem_bin_binIndex w (v i), hv⟩
    · exact fun i _ => mem_bin_binIndex w (v i)
  have hΛapp : ∀ S, Λ S = ∑ s, m s * Measure.pi (fun _ : Fin 7 => μ s) S := by
    intro S
    simp [hΛ, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  have hΛbox : ∀ β, Λ (box β) = ∑ s, m s * ∏ i, μ s (bin w (β i)) := by
    intro β
    rw [hΛapp]
    simp [box, Measure.pi_pi]
  have hνbox : ∀ β, ν (box β) = ∏ i, π (bin w (β i)) := fun β => by
    simp [hν, box, Measure.pi_pi]
  set X := (1 - (686 * κ + 7 * τ)) * M with hX
  have hXle : X ≤ Λ (⋃ β, B β) := by
    calc X = ∑ s, m s * (1 - (686 * κ + 7 * τ)) := by
          rw [hX, hM, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => mul_comm _ _
      _ ≤ ∑ s, m s * Measure.pi (fun _ : Fin 7 => μ s) (goodTuples δ R) :=
          Finset.sum_le_sum fun s _ =>
            mul_le_mul_right (one_sub_le_pi_goodTuples (μ s) hδ (hb s) (htail s)) _
      _ = Λ (goodTuples δ R) := (hΛapp _).symm
      _ ≤ Λ (⋃ β, B β) := measure_mono hcover
  have hνle : ν (⋃ β, B β) ≤ π univ ^ 7 := by
    calc ν (⋃ β, B β) ≤ ν univ := measure_mono (subset_univ _)
      _ = π univ ^ 7 := by simp [hν, Measure.pi_univ]
  have hX0 : X ≠ 0 := mul_ne_zero (tsub_pos_of_lt hgood).ne' hM0
  have hXtop : X ≠ ∞ :=
    ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) hMtop
  have hP0 : π univ ^ 7 ≠ 0 := pow_ne_zero _ hπ0
  have hPtop : π univ ^ 7 ≠ ∞ := ENNReal.pow_ne_top (measure_ne_top π univ)
  obtain ⟨⟨β, hβG⟩, hpos, hdens⟩ :=
    exists_piece_density_ge Λ ν B hB hdisj hX0 hXtop hP0 hPtop hXle hνle
  obtain ⟨v, hvbox, hvgood⟩ := hβG
  have hcoord : ∀ l c, |v l c| ≤ R := fun l c => by
    have h1 : ‖(v l) c‖ ≤ ‖v l‖ := PiLp.norm_apply_le (v l) c
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hvgood.2 l)
  have hdist : ∀ l c, |v l c - binCenter w (β l) c| ≤ w / 2 := fun l c =>
    abs_sub_binCenter_le hw (hvbox l (mem_univ l)) c
  refine ⟨β, ?_, ?_, ?_, ?_⟩
  · intro i j k hij hik hjk
    have hpert := abs_tripleDet_sub_le (e := w / 2) (R := R) (by positivity)
      (hcoord i) (hcoord j) (hcoord k) (hdist i) (hdist j) (hdist k)
    have hgoodijk := hvgood.1 i j k hij hik hjk
    have htri := abs_sub_abs_le_abs_sub (tripleDet (v i) (v j) (v k))
      (tripleDet (binCenter w (β i)) (binCenter w (β j)) (binCenter w (β k)))
    have he : 8 * (w / 2) * (2 * R + w / 2) = 4 * w * (2 * R + w / 2) := by ring
    linarith
  · intro i c
    have h1 := hdist i c
    have h2 := hcoord i c
    calc |binCenter w (β i) c| = |v i c - (v i c - binCenter w (β i) c)| := by ring_nf
      _ ≤ |v i c| + |v i c - binCenter w (β i) c| := abs_sub _ _
      _ ≤ R + w / 2 := add_le_add h2 h1
  · rw [← hΛbox]
    exact hpos
  · rw [← hΛbox, ← hνbox]
    exact hdens

/-- **Seven directions with common witness states.** Under the hypotheses of
`exists_seven_bins`, let every selected-width bin be dominated by the palette. Full-measure domination is not required.
Write `M = ∑ₛ m s` and `X = (1 - (686 κ + 7 τ)) M / (π univ)⁷`. For the selected bins `Jᵢ`,
the states with `X ∏ᵢ π Jᵢ ≤ 2 M ∏ᵢ μ s Jᵢ` carry mass at least `X / (2 K⁷)`, and each such
state charges every selected bin: `X π Jᵢ ≤ 2 M K⁶ μ s Jᵢ`. -/
theorem exists_seven_bins_states_of_bin_domination {ι : Type*} [Fintype ι]
    (m : ι → ℝ≥0∞) (μ : ι → Measure (EuclideanSpace ℝ (Fin 2)))
    [∀ s, IsProbabilityMeasure (μ s)]
    (π : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure π] (hπ0 : π univ ≠ 0)
    {K : ℝ≥0∞} {w : ℝ} (hK : K ≠ ∞)
    (hdom : ∀ s β, μ s (bin w β) ≤ K * π (bin w β))
    {δ R : ℝ} (hδ : 0 < δ) (hw : 0 < w) {κ τ : ℝ≥0∞}
    (hb : ∀ s, StripBreadth (μ s) δ κ) (htail : ∀ s, μ s {v | R < ‖v‖} ≤ τ)
    (hgood : 686 * κ + 7 * τ < 1) (hM0 : ∑ s, m s ≠ 0) (hMtop : ∑ s, m s ≠ ∞) :
    ∃ β : Fin 7 → Fin 2 → ℤ,
      (∀ i j k : Fin 7, i ≠ j → i ≠ k → j ≠ k →
        δ ^ 2 - 4 * w * (2 * R + w / 2) ≤
          |tripleDet (binCenter w (β i)) (binCenter w (β j)) (binCenter w (β k))|) ∧
      (∀ i c, |binCenter w (β i) c| ≤ R + w / 2) ∧
      (∀ i, π (bin w (β i)) ≠ 0) ∧
      (1 - (686 * κ + 7 * τ)) * (∑ s, m s) / π univ ^ 7 ≤
        2 * K ^ 7 * ∑ s ∈ Finset.univ.filter (fun s =>
          (1 - (686 * κ + 7 * τ)) * (∑ s, m s) / π univ ^ 7 * ∏ i, π (bin w (β i)) ≤
            2 * (∑ s, m s) * ∏ i, μ s (bin w (β i))), m s ∧
      ∀ s, (1 - (686 * κ + 7 * τ)) * (∑ s, m s) / π univ ^ 7 * ∏ i, π (bin w (β i)) ≤
            2 * (∑ s, m s) * ∏ i, μ s (bin w (β i)) →
        ∀ i, (1 - (686 * κ + 7 * τ)) * (∑ s, m s) / π univ ^ 7 * π (bin w (β i)) ≤
          2 * (∑ s, m s) * K ^ 6 * μ s (bin w (β i)) := by
  classical
  obtain ⟨β, hdet, hcen, hpos, hdens⟩ :=
    exists_seven_bins m μ π hπ0 hδ hw hb htail hgood hM0 hMtop
  set M := ∑ s, m s with hM
  set X := (1 - (686 * κ + 7 * τ)) * M / π univ ^ 7 with hX
  set Q := ∏ i, π (bin w (β i)) with hQ
  have hle : ∀ s β, μ s (bin w β) ≤ K * π (bin w β) := hdom
  have ha : ∀ s, ∏ i, μ s (bin w (β i)) ≤ K ^ 7 * Q := fun s => by
    calc ∏ i, μ s (bin w (β i)) ≤ ∏ i, K * π (bin w (β i)) :=
          Finset.prod_le_prod fun i _ => hle s _
      _ = K ^ 7 * Q := by rw [Finset.prod_mul_distrib, Finset.prod_const]; simp [hQ]
  -- every selected bin has positive palette mass
  obtain ⟨s0, -, hs0⟩ := Finset.exists_lt_of_sum_lt (by simpa using hpos :
    ∑ s, (0 : ℝ≥0∞) < ∑ s, m s * ∏ i, μ s (bin w (β i)))
  have hprod0 : ∏ i, μ s0 (bin w (β i)) ≠ 0 := fun h => by simp [h] at hs0
  have hπpos : ∀ i, π (bin w (β i)) ≠ 0 := fun i h => by
    apply hprod0
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have := hle s0 (β i)
    rw [h, mul_zero] at this
    exact le_antisymm this (zero_le)
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hπpos i
  have hQtop : Q ≠ ∞ := ENNReal.prod_ne_top fun i _ => measure_ne_top π _
  have hK7 : K ^ 7 ≠ ∞ := ENNReal.pow_ne_top hK
  refine ⟨β, hdet, hcen, hπpos, ?_, ?_⟩
  · exact mass_of_large_ratio m (fun s => ∏ i, μ s (bin w (β i))) hQ0 hQtop hM0 hMtop hK7
      hdens ha le_rfl
  · intro s hs i
    -- split off the `i`-th factor
    have hsplitμ : ∏ j, μ s (bin w (β j)) =
        μ s (bin w (β i)) * ∏ j ∈ Finset.univ.erase i, μ s (bin w (β j)) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    have hsplitπ : Q = π (bin w (β i)) * ∏ j ∈ Finset.univ.erase i, π (bin w (β j)) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    set Q' := ∏ j ∈ Finset.univ.erase i, π (bin w (β j)) with hQ'
    have hcard : (Finset.univ.erase i).card = 6 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have hrest : ∏ j ∈ Finset.univ.erase i, μ s (bin w (β j)) ≤ K ^ 6 * Q' := by
      calc ∏ j ∈ Finset.univ.erase i, μ s (bin w (β j))
          ≤ ∏ j ∈ Finset.univ.erase i, K * π (bin w (β j)) :=
            Finset.prod_le_prod fun j _ => hle s _
        _ = K ^ 6 * Q' := by rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    have hQ'0 : Q' ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hπpos j
    have hQ'top : Q' ≠ ∞ := ENNReal.prod_ne_top fun j _ => measure_ne_top π _
    have hmain : X * π (bin w (β i)) * Q' ≤ 2 * M * K ^ 6 * μ s (bin w (β i)) * Q' := by
      calc X * π (bin w (β i)) * Q' = X * Q := by rw [hsplitπ]; ring
        _ ≤ 2 * M * ∏ j, μ s (bin w (β j)) := hs
        _ = 2 * M * (μ s (bin w (β i)) * ∏ j ∈ Finset.univ.erase i, μ s (bin w (β j))) := by
            rw [hsplitμ]
        _ ≤ 2 * M * (μ s (bin w (β i)) * (K ^ 6 * Q')) :=
            mul_le_mul_right (mul_le_mul_right hrest _) _
        _ = 2 * M * K ^ 6 * μ s (bin w (β i)) * Q' := by ring
    exact (ENNReal.mul_le_mul_iff_left hQ'0 hQ'top).mp hmain

end Submission.Lib.K4OriginalCellSampling.Sampling
