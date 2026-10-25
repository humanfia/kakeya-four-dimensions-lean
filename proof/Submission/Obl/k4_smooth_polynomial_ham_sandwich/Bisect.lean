import Mathlib
import Submission.WZ.Obl.wz_polynomial_grains_partition.PolyMethod.ZeroNull

/-!
# Polynomial ham sandwich in `ℝⁿ` with rectangular monomials

The algebraic half of `Submission.k4_smooth_polynomial_ham_sandwich`.

* `volume_zeroSet_eucl`: the zero set of a nonzero real polynomial on `EuclideanSpace ℝ (Fin n)`
  is Lebesgue-null (transported from `WangZahlLot`'s `volume_zeroSet_pi`).
* `exists_bisecting_poly_rect`: fewer than `(d+1)^n` finite measures on `ℝⁿ` are simultaneously
  bisected by a nonzero polynomial whose monomials have all exponents `≤ d`, so of total degree
  `≤ n * d`. It is the Stone–Tukey theorem (`WangZahlLot`'s `stone_tukey`) applied to
  `card + 1` distinct monomials; the argument follows `WangZahlLot`'s three-dimensional
  `PolyMethod.PartitionAux.exists_bisecting_poly`, written here for every `n`.
* `exists_bisecting_poly_deg`: the form with `k ≤ T ^ n` measures and degree `≤ n * T`.
* `exists_balanced_poly`: for finitely many sets of finite volume, a nonzero polynomial of degree
  `≤ n * T` whose positive and negative parts carry exactly the same volume of each set, its zero
  set none.
-/

namespace Submission.Obl.k4_smooth_polynomial_ham_sandwich

open MeasureTheory

/-- Evaluation of a polynomial at a point of `EuclideanSpace ℝ (Fin n)` is continuous. -/
theorem continuous_evalE {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    Continuous fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => x j) P :=
  (MvPolynomial.continuous_eval P).comp (PiLp.continuous_ofLp 2 _)

/-- Evaluation of a polynomial at a point of `EuclideanSpace ℝ (Fin n)` is measurable. -/
theorem measurable_evalE {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun j => x j) P :=
  (continuous_evalE P).measurable

/-- The zero set of a nonzero real polynomial on `EuclideanSpace ℝ (Fin n)` is Lebesgue-null. -/
theorem volume_zeroSet_eucl {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0) :
    volume {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun j => x j) P = 0} = 0 := by
  have hc : IsClosed {x : Fin n → ℝ | MvPolynomial.eval x P = 0} :=
    isClosed_eq (MvPolynomial.continuous_eval P) continuous_const
  have h := (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    hc.measurableSet.nullMeasurableSet
  rw [← WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod.volume_zeroSet_pi P hP, ← h]
  rfl

/-- Polynomial ham sandwich in `ℝⁿ`: fewer than `(d+1)^n` finite measures are simultaneously
bisected by a nonzero polynomial all of whose exponents are at most `d`, hence of total degree at
most `n * d`. -/
theorem exists_bisecting_poly_rect {n : ℕ} {ι : Type*} [Fintype ι]
    (ν : ι → Measure (EuclideanSpace ℝ (Fin n))) [∀ i, IsFiniteMeasure (ν i)] (d : ℕ)
    (hk : Fintype.card ι < (d + 1) ^ n) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ P.totalDegree ≤ n * d ∧ ∀ i,
      2 * ν i {x | 0 < MvPolynomial.eval (fun j => x j) P} ≤ ν i Set.univ ∧
      2 * ν i {x | MvPolynomial.eval (fun j => x j) P < 0} ≤ ν i Set.univ := by
  classical
  set N := Fintype.card ι
  let e : ι ≃ Fin N := Fintype.equivFin ι
  have hcard : Fintype.card (Fin (N + 1)) ≤ Fintype.card (Fin n → Fin (d + 1)) := by
    simp only [Fintype.card_fin, Fintype.card_fun]; omega
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  -- `N + 1` distinct exponents with all entries `≤ d`
  let E : Fin (N + 1) → (Fin n →₀ ℕ) := fun j =>
    Finsupp.equivFunOnFinite.symm (fun i => ((emb j i : Fin (d + 1)) : ℕ))
  have hE_apply : ∀ j i, E j i = ((emb j i : Fin (d + 1)) : ℕ) := fun j i => by
    simp [E]
  have hE_inj : Function.Injective E := by
    intro j j' h
    apply emb.injective
    funext i
    have := congrArg (fun m : Fin n →₀ ℕ => m i) h
    simp only [hE_apply] at this
    exact Fin.ext this
  have hE_deg : ∀ j, ((E j).sum fun _ => id) ≤ n * d := by
    intro j
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    calc ∑ i, id ((E j) i) = ∑ i : Fin n, ((emb j i : Fin (d + 1)) : ℕ) := by
          simp [hE_apply]
      _ ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (emb j i).isLt
      _ = n * d := by simp
  let f : Fin (N + 1) → EuclideanSpace ℝ (Fin n) → ℝ := fun j x =>
    MvPolynomial.eval (fun i => x i) (MvPolynomial.monomial (E j) 1)
  have hf : ∀ j, Measurable (f j) := fun j => measurable_evalE _
  obtain ⟨c, hc1, hc⟩ :=
    WangZahlLot.Obl.wz_polynomial_grains_partition.PolyMethod.stone_tukey f hf
      (fun i => ν (e.symm i))
  let P : MvPolynomial (Fin n) ℝ := ∑ j, MvPolynomial.monomial (E j) (c j)
  have hPeval : ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => x i) P = ∑ j, c j * f j x := by
    intro x; simp [P, f, MvPolynomial.eval_monomial]
  refine ⟨P, ?_, ?_, fun i => ?_⟩
  · have hc0 : c ≠ 0 := by
      intro h; rw [h, norm_zero] at hc1; exact zero_ne_one hc1
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hc0
    intro hP
    have := congrArg (fun q : MvPolynomial (Fin n) ℝ => q.coeff (E j0)) hP
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hE_inj.eq_iff] at this
    simp at this
    exact hj0 this
  · exact (MvPolynomial.totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun j _ => (MvPolynomial.totalDegree_monomial_le _ _).trans (hE_deg j))
  · have := hc (e i)
    simp only [Equiv.symm_apply_apply] at this
    simp only [hPeval]
    exact this

/-- Polynomial ham sandwich with the degree budget of the obligation: `k ≤ T ^ n` finite
measures on `ℝⁿ` (`n ≥ 1`, `T ≥ 1`) are simultaneously bisected by a nonzero polynomial of total
degree at most `n * T`. -/
theorem exists_bisecting_poly_deg (n : ℕ) (hn : 1 ≤ n) (T : ℝ) (hT : 1 ≤ T) {k : ℕ}
    (hk : (k : ℝ) ≤ T ^ n) (ν : Fin k → Measure (EuclideanSpace ℝ (Fin n)))
    [∀ i, IsFiniteMeasure (ν i)] :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ (P.totalDegree : ℝ) ≤ n * T ∧ ∀ i,
      2 * ν i {x | 0 < MvPolynomial.eval (fun j => x j) P} ≤ ν i Set.univ ∧
      2 * ν i {x | MvPolynomial.eval (fun j => x j) P < 0} ≤ ν i Set.univ := by
  set d := ⌊T⌋₊ with hd_def
  have hd : T < d + 1 := Nat.lt_floor_add_one T
  have hdT : (d : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hcard : Fintype.card (Fin k) < (d + 1) ^ n := by
    rw [Fintype.card_fin]
    have : (k : ℝ) < ((d + 1 : ℕ) : ℝ) ^ n := by
      calc (k : ℝ) ≤ T ^ n := hk
        _ < ((d : ℝ) + 1) ^ n := pow_lt_pow_left₀ hd (by linarith) (by omega)
        _ = ((d + 1 : ℕ) : ℝ) ^ n := by push_cast; ring
    exact_mod_cast this
  obtain ⟨P, hP0, hPdeg, hP⟩ := exists_bisecting_poly_rect ν d hcard
  refine ⟨P, hP0, ?_, hP⟩
  calc (P.totalDegree : ℝ) ≤ ((n * d : ℕ) : ℝ) := by exact_mod_cast hPdeg
    _ = n * d := by push_cast; ring
    _ ≤ n * T := by gcongr

/-- From the two half-mass bounds and a null zero set: the positive and negative parts carry
exactly the same mass. -/
theorem balance_of_bisect {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (h0 : μ {x | g x = 0} = 0)
    (hpos : 2 * μ {x | 0 < g x} ≤ μ Set.univ) (hneg : 2 * μ {x | g x < 0} ≤ μ Set.univ) :
    μ {x | 0 < g x} = μ {x | g x < 0} := by
  have hmpos : MeasurableSet {x | 0 < g x} := measurableSet_lt measurable_const hg
  have hmneg : MeasurableSet {x | g x < 0} := measurableSet_lt hg measurable_const
  have hdisj : Disjoint {x | 0 < g x} {x | g x < 0} := by
    rw [Set.disjoint_left]
    intro x h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    linarith
  have hcover : Set.univ ⊆ ({x | 0 < g x} ∪ {x | g x < 0}) ∪ {x | g x = 0} := by
    intro x _
    rcases lt_trichotomy (g x) 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  have hsum : μ Set.univ ≤ μ {x | 0 < g x} + μ {x | g x < 0} := by
    calc μ Set.univ ≤ μ (({x | 0 < g x} ∪ {x | g x < 0}) ∪ {x | g x = 0}) := measure_mono hcover
      _ ≤ μ ({x | 0 < g x} ∪ {x | g x < 0}) + μ {x | g x = 0} := measure_union_le _ _
      _ = μ {x | 0 < g x} + μ {x | g x < 0} := by rw [h0, add_zero, measure_union hdisj hmneg]
  have ha : μ {x | 0 < g x} ≠ ⊤ := measure_ne_top _ _
  have hb : μ {x | g x < 0} ≠ ⊤ := measure_ne_top _ _
  have hu : μ Set.univ ≠ ⊤ := measure_ne_top _ _
  have hreal : (μ {x | 0 < g x}).toReal = (μ {x | g x < 0}).toReal := by
    have e1 : 2 * (μ {x | 0 < g x}).toReal ≤ (μ Set.univ).toReal := by
      have := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by norm_num) ha) hu).2 hpos
      simpa [ENNReal.toReal_mul] using this
    have e2 : 2 * (μ {x | g x < 0}).toReal ≤ (μ Set.univ).toReal := by
      have := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top (by norm_num) hb) hu).2 hneg
      simpa [ENNReal.toReal_mul] using this
    have e3 : (μ Set.univ).toReal ≤ (μ {x | 0 < g x}).toReal + (μ {x | g x < 0}).toReal := by
      have := (ENNReal.toReal_le_toReal hu (ENNReal.add_ne_top.2 ⟨ha, hb⟩)).2 hsum
      rwa [ENNReal.toReal_add ha hb] at this
    linarith
  exact (ENNReal.toReal_eq_toReal_iff' ha hb).1 hreal

/-- Exactly balanced polynomial: finitely many sets of finite volume, at most `T ^ n` of them,
have a common nonzero polynomial of total degree at most `n * T` whose positive and negative parts
carry the same volume of each set; its zero set is null. -/
theorem exists_balanced_poly (n : ℕ) (hn : 1 ≤ n) (T : ℝ) (hT : 1 ≤ T) (k : ℕ)
    (Q : Fin k → Set (EuclideanSpace ℝ (Fin n))) (hk : (k : ℝ) ≤ T ^ n)
    (hQ : ∀ h, volume (Q h) ≠ ⊤) :
    ∃ P : MvPolynomial (Fin n) ℝ, P ≠ 0 ∧ (P.totalDegree : ℝ) ≤ n * T ∧
      volume {x : EuclideanSpace ℝ (Fin n) | MvPolynomial.eval (fun j => x j) P = 0} = 0 ∧
      ∀ h, volume.restrict (Q h) {x | 0 < MvPolynomial.eval (fun j => x j) P} =
        volume.restrict (Q h) {x | MvPolynomial.eval (fun j => x j) P < 0} := by
  have : ∀ h, IsFiniteMeasure (volume.restrict (Q h)) := fun h =>
    isFiniteMeasure_restrict.2 (hQ h)
  obtain ⟨P, hP0, hPdeg, hP⟩ :=
    exists_bisecting_poly_deg n hn T hT hk (fun h => volume.restrict (Q h))
  have hnull := volume_zeroSet_eucl P hP0
  refine ⟨P, hP0, hPdeg, hnull, fun h => ?_⟩
  have h0 : volume.restrict (Q h) {x | MvPolynomial.eval (fun j => x j) P = 0} = 0 :=
    nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hnull.le)
  exact balance_of_bisect _ (measurable_evalE P) h0 (hP h).1 (hP h).2

end Submission.Obl.k4_smooth_polynomial_ham_sandwich
