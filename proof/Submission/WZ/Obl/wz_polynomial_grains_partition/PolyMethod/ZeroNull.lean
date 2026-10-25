-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod.ZeroNull.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_polynomial_grains_partition.PolyMethod.HamSandwich

/-!
# Zero sets of nonzero real polynomials are Lebesgue-null

* `volume_zeroSet_pi`: the zero set of a nonzero polynomial in `n` real variables is null, by
  induction on `n`: split off the first variable (`Fin.cons`, volume-preserving), write the
  polynomial as a univariate polynomial with coefficients in the remaining variables
  (`MvPolynomial.finSuccEquiv`); off the null zero set of a nonzero coefficient, each slice is
  a finite set of roots, and Tonelli concludes.
* `volume_zeroSet`: the same on `EuclideanSpace ℝ (Fin 3)`.
* `guth_katz_partitioning_ac`: for a measure absolutely continuous w.r.t. Lebesgue measure, the
  strict sign cells of the Guth–Katz partitioning carry all the mass.
-/

namespace WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod

namespace ZeroNullAux

open MeasureTheory

/-- `(y, s) ↦ Fin.cons y s` is volume-preserving from `ℝ × (Fin n → ℝ)` to `Fin (n + 1) → ℝ`. -/
lemma measurePreserving_cons (n : ℕ) :
    MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ))
      volume volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  convert h using 1
  funext p
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_zero']

/-- Zero sets of polynomials are closed. -/
lemma isClosed_zeroSet {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    IsClosed {x : Fin n → ℝ | MvPolynomial.eval x P = 0} :=
  isClosed_eq (MvPolynomial.continuous_eval P) continuous_const

end ZeroNullAux

open MeasureTheory ZeroNullAux in
/-- The zero set of a nonzero real polynomial in `n` variables is Lebesgue-null. -/
theorem volume_zeroSet_pi {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0) :
    MeasureTheory.volume {x : Fin n → ℝ | MvPolynomial.eval x P = 0} = 0 := by
  induction n with
  | zero =>
    have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x P = 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hP
      rw [MvPolynomial.eq_C_of_isEmpty P] at hx ⊢
      rw [MvPolynomial.eval_C] at hx
      rw [hx, map_zero]
    rw [hempty, measure_empty]
  | succ n ih =>
    set Q := MvPolynomial.finSuccEquiv ℝ n P with hQ
    have hQ0 : Q ≠ 0 := by
      intro h
      apply hP
      apply (MvPolynomial.finSuccEquiv ℝ n).injective
      rw [← hQ, h, map_zero]
    obtain ⟨k, hk⟩ : ∃ k, Q.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hQ0 (Polynomial.ext fun m => by rw [h m, Polynomial.coeff_zero])
    have hnull := ih (Q.coeff k) hk
    set S := {x : Fin (n + 1) → ℝ | MvPolynomial.eval x P = 0} with hS
    have hSc : IsClosed S := isClosed_zeroSet P
    rw [← (measurePreserving_cons n).measure_preimage hSc.measurableSet.nullMeasurableSet]
    have hmeas : MeasurableSet
        ((fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) ⁻¹' S) :=
      (measurePreserving_cons n).measurable hSc.measurableSet
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    have hae : ∀ᵐ s ∂(volume : Measure (Fin n → ℝ)), MvPolynomial.eval s (Q.coeff k) ≠ 0 := by
      rw [ae_iff]
      simpa only [ne_eq, not_not] using hnull
    filter_upwards [hae] with s hs
    have hne : Polynomial.map (MvPolynomial.eval s) Q ≠ 0 := by
      intro h
      apply hs
      have := congrArg (fun q => Polynomial.coeff q k) h
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using this
    have hfin : ((fun y : ℝ => ((y, s) : ℝ × (Fin n → ℝ))) ⁻¹'
        ((fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ)) ⁻¹' S)).Finite := by
      refine Set.Finite.subset (Polynomial.map (MvPolynomial.eval s) Q).roots.toFinset.finite_toSet
        ?_
      intro y hy
      simp only [Set.mem_preimage, hS, Set.mem_ofPred_eq] at hy
      rw [MvPolynomial.eval_eq_eval_mv_eval'] at hy
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_roots hne]
      exact hy
    simpa only [Pi.zero_apply] using hfin.measure_zero _

open MeasureTheory in
/-- The same on `EuclideanSpace ℝ (Fin 3)`. -/
theorem volume_zeroSet (P : MvPolynomial (Fin 3) ℝ) (hP : P ≠ 0) :
    MeasureTheory.volume {x : EuclideanSpace ℝ (Fin 3) | MvPolynomial.eval (fun i => x i) P = 0}
      = 0 := by
  have h := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (ZeroNullAux.isClosed_zeroSet P).measurableSet.nullMeasurableSet
  rw [← volume_zeroSet_pi P hP, ← h]
  rfl

open MeasureTheory PartitionAux in
/-- Guth–Katz partitioning for a measure absolutely continuous w.r.t. Lebesgue measure: the
`2^J` strict sign cells carry all the mass, each at most a `2^(-J)` share. -/
theorem guth_katz_partitioning_ac
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) [MeasureTheory.IsFiniteMeasure μ]
    (hμ : μ ≪ MeasureTheory.volume) (J : ℕ) :
    ∃ P : Fin J → MvPolynomial (Fin 3) ℝ, (∀ j, P j ≠ 0) ∧
      (∀ j : Fin J, (P j).totalDegree ^ 3 ≤ 27 * 2 ^ (j : ℕ)) ∧
      (∀ s : Fin J → Bool,
        2 ^ J * μ {x | ∀ j, if s j = true then 0 < MvPolynomial.eval (fun i => x i) (P j)
                              else MvPolynomial.eval (fun i => x i) (P j) < 0} ≤ μ Set.univ) ∧
      ∑ s : Fin J → Bool, μ {x | ∀ j, if s j = true then 0 < MvPolynomial.eval (fun i => x i) (P j)
                              else MvPolynomial.eval (fun i => x i) (P j) < 0} = μ Set.univ := by
  classical
  obtain ⟨P, hP0, hPdeg, hPμ⟩ := guth_katz_partitioning μ J
  refine ⟨P, hP0, hPdeg, hPμ, ?_⟩
  -- the sign cells
  set C : (Fin J → Bool) → Set (EuclideanSpace ℝ (Fin 3)) := fun s =>
    {x | ∀ j, if s j = true then 0 < MvPolynomial.eval (fun i => x i) (P j)
              else MvPolynomial.eval (fun i => x i) (P j) < 0} with hC
  -- the zero sets
  set Z : Fin J → Set (EuclideanSpace ℝ (Fin 3)) := fun j =>
    {x | MvPolynomial.eval (fun i => x i) (P j) = 0} with hZ
  have hCmeas : ∀ s, MeasurableSet (C s) := by
    intro s
    have : C s = ⋂ j, {x | if s j = true then 0 < MvPolynomial.eval (fun i => x i) (P j)
              else MvPolynomial.eval (fun i => x i) (P j) < 0} := by
      ext x; simp [hC]
    rw [this]
    refine MeasurableSet.iInter fun j => ?_
    by_cases hb : s j = true
    · simp only [hb, ↓reduceIte]
      exact measurableSet_lt measurable_const (measurable_eval (P j))
    · simp only [hb]
      exact measurableSet_lt (measurable_eval (P j)) measurable_const
  have hCdisj : Pairwise (Function.onFun Disjoint C) := by
    intro s t hst
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hst
    rw [Function.onFun, Set.disjoint_left]
    intro x hxs hxt
    have h1 := hxs j
    have h2 := hxt j
    cases hs : s j <;> cases ht : t j <;> simp [hs, ht] at hj h1 h2 <;> linarith
  have hZnull : μ (⋃ j, Z j) = 0 :=
    measure_iUnion_null fun j => hμ (volume_zeroSet (P j) (hP0 j))
  have hcover : Set.univ ⊆ (⋃ s, C s) ∪ ⋃ j, Z j := by
    intro x _
    by_cases h : ∃ j, MvPolynomial.eval (fun i => x i) (P j) = 0
    · obtain ⟨j, hj⟩ := h
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩)
    · push Not at h
      refine Or.inl (Set.mem_iUnion.mpr ⟨fun j => decide (0 < MvPolynomial.eval (fun i => x i)
        (P j)), ?_⟩)
      intro j
      by_cases hpos : 0 < MvPolynomial.eval (fun i => x i) (P j)
      · simp [hpos]
      · simp only [hpos, decide_false]
        exact lt_of_le_of_ne (not_lt.mp hpos) (h j)
  have hunion : μ (⋃ s, C s) = ∑ s, μ (C s) := by
    rw [measure_iUnion hCdisj hCmeas, tsum_fintype]
  apply le_antisymm
  · rw [← hunion]
    exact measure_mono (Set.subset_univ _)
  · calc μ Set.univ ≤ μ ((⋃ s, C s) ∪ ⋃ j, Z j) := measure_mono hcover
      _ ≤ μ (⋃ s, C s) + μ (⋃ j, Z j) := measure_union_le _ _
      _ = ∑ s, μ (C s) := by rw [hZnull, add_zero, hunion]

end WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod
