-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod.HamSandwich.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.PolyMethod.BorsukUlam

/-!
# Ham sandwich and polynomial partitioning (from Borsuk–Ulam)

* `ham_sandwich`: the Stone–Tukey ham sandwich theorem for `N` finite measures and `N + 1`
  measurable functions, deduced from `BorsukUlamStatement`. To avoid needing that zero sets are
  null, the sign function is smoothed by the clamps `t ↦ max (-1) (min 1 (k * t))`; Borsuk–Ulam
  gives a zero `c_k` of the smoothed odd map, a subsequence converges on the (compact) unit
  sphere, and Fatou's lemma passes to the limit.
* `polynomial_partitioning`: Guth–Katz polynomial partitioning of a finite measure on `ℝ³`
  into `2 ^ J` sign cells, by induction on `J`, bisecting all current cells at once with a
  combination of `2 ^ J + 1` distinct monomials `X₀^a X₁^b X₂^c` (`a, b, c ≤ k`, `k ^ 3 ≤ 2 ^ J`).
-/

namespace WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod

namespace HamSandwichAux

open MeasureTheory Filter Topology

/-- The clamp `t ↦ max (-1) (min 1 t)`. -/
noncomputable def clamp (t : ℝ) : ℝ := max (-1) (min 1 t)

lemma continuous_clamp : Continuous clamp := by
  unfold clamp; fun_prop

lemma clamp_neg (t : ℝ) : clamp (-t) = - clamp t := by
  unfold clamp
  rcases le_total t (-1) with h | h <;> rcases le_total t 1 with h' | h' <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

lemma abs_clamp_le (t : ℝ) : |clamp t| ≤ 1 := by
  unfold clamp; rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma clamp_of_one_le {t : ℝ} (h : 1 ≤ t) : clamp t = 1 := by
  unfold clamp; rw [min_eq_left h]; norm_num

/-- Passing to the limit in the smoothed ham sandwich condition: if `h n → H` pointwise,
`k n → ∞` and `∫ clamp (k n * h n) dμ = 0` for all `n`, then `{H > 0}` has at most half of the
mass of `μ` (Fatou's lemma applied to `1 + clamp (k n * h n) ∈ [0, 2]`). -/
lemma half_measure_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (h : ℕ → α → ℝ) (H : α → ℝ) (hh : ∀ n, Measurable (h n)) (hH : Measurable H)
    (hlim : ∀ x, Tendsto (fun n => h n x) atTop (𝓝 (H x)))
    (k : ℕ → ℝ) (hk : Tendsto k atTop atTop)
    (hint : ∀ n, ∫ x, clamp (k n * h n x) ∂μ = 0) :
    2 * μ {x | 0 < H x} ≤ μ Set.univ := by
  set g : ℕ → α → ℝ := fun n x => 1 + clamp (k n * h n x) with hg_def
  have hc_meas : ∀ n, Measurable (fun x => clamp (k n * h n x)) := fun n =>
    continuous_clamp.measurable.comp (measurable_const.mul (hh n))
  have hg_meas : ∀ n, Measurable (g n) := fun n => measurable_const.add (hc_meas n)
  have hg_nonneg : ∀ n x, 0 ≤ g n x := fun n x => by
    have := abs_clamp_le (k n * h n x); rw [abs_le] at this; simp only [hg_def]; linarith
  have hclamp_int : ∀ n, Integrable (fun x => clamp (k n * h n x)) μ := fun n =>
    Integrable.of_bound (hc_meas n).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_clamp_le _)
  have hg_int : ∀ n, ∫ x, g n x ∂μ = μ.real Set.univ := fun n => by
    simp only [hg_def]
    rw [integral_add (integrable_const 1) (hclamp_int n), hint n, integral_const]
    simp
  have hg_intble : ∀ n, Integrable (g n) μ := fun n => (integrable_const 1).add (hclamp_int n)
  have hlint : ∀ n, ∫⁻ x, ENNReal.ofReal (g n x) ∂μ = μ Set.univ := fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hg_intble n)
      (Eventually.of_forall (hg_nonneg n)), hg_int n]
    simp
  have hA : MeasurableSet {x | 0 < H x} := measurableSet_lt measurable_const hH
  have hpt : ∀ x, {x | 0 < H x}.indicator (fun _ => (2 : ENNReal)) x ≤
      liminf (fun n => ENNReal.ofReal (g n x)) atTop := by
    intro x
    by_cases hx : 0 < H x
    · rw [Set.indicator_of_mem (s := {x | 0 < H x}) hx]
      have hev : ∀ᶠ n in atTop, ENNReal.ofReal (g n x) = 2 := by
        have h1 : ∀ᶠ n in atTop, H x / 2 < h n x :=
          (hlim x).eventually (lt_mem_nhds (by linarith))
        have h2 : ∀ᶠ n in atTop, 2 / H x ≤ k n := hk.eventually_ge_atTop _
        filter_upwards [h1, h2] with n hn1 hn2
        have hpos : 0 < 2 / H x := div_pos two_pos hx
        have : 1 ≤ k n * h n x := by
          calc (1 : ℝ) = (2 / H x) * (H x / 2) := by field_simp
            _ ≤ k n * h n x := mul_le_mul hn2 hn1.le (by linarith) (by linarith)
        simp only [hg_def, clamp_of_one_le this]; norm_num
      rw [(tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)).liminf_eq]
    · rw [Set.indicator_of_notMem (s := {x | 0 < H x}) hx]; exact zero_le
  calc 2 * μ {x | 0 < H x}
      = ∫⁻ x, {x | 0 < H x}.indicator (fun _ => (2 : ENNReal)) x ∂μ :=
        (lintegral_indicator_const hA 2).symm
    _ ≤ ∫⁻ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂μ := lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) atTop :=
        lintegral_liminf_le (fun n => (hg_meas n).ennreal_ofReal)
    _ = μ Set.univ := by simp only [hlint]; exact liminf_const _

/-- The smoothed odd map `(Fin (N+1) → ℝ) → (Fin N → ℝ)` used in the ham sandwich argument. -/
noncomputable def smoothF {α : Type*} [MeasurableSpace α] {N : ℕ}
    (f : Fin (N + 1) → α → ℝ) (μ : Fin N → Measure α) (k : ℕ)
    (c : Fin (N + 1) → ℝ) (i : Fin N) : ℝ :=
  ∫ x, clamp ((k : ℝ) * ∑ j, c j * f j x) ∂(μ i)

end HamSandwichAux

open MeasureTheory Filter Topology HamSandwichAux in
/-- Stone–Tukey ham sandwich for `N` finite measures and `N+1` measurable functions. -/
theorem ham_sandwich (hBU : BorsukUlamStatement) {α : Type*} [MeasurableSpace α] {N : ℕ}
    (f : Fin (N + 1) → α → ℝ) (hf : ∀ j, Measurable (f j))
    (μ : Fin N → MeasureTheory.Measure α) [∀ i, MeasureTheory.IsFiniteMeasure (μ i)] :
    ∃ c : Fin (N + 1) → ℝ, ‖c‖ = 1 ∧ ∀ i,
      2 * μ i {x | 0 < ∑ j, c j * f j x} ≤ μ i Set.univ ∧
      2 * μ i {x | ∑ j, c j * f j x < 0} ≤ μ i Set.univ := by
  have hLcont : ∀ x, Continuous fun c : Fin (N + 1) → ℝ => ∑ j, c j * f j x := fun x => by
    fun_prop
  have hLmeas : ∀ c : Fin (N + 1) → ℝ, Measurable fun x => ∑ j, c j * f j x := fun c =>
    Finset.measurable_sum _ fun j _ => measurable_const.mul (hf j)
  have hcont : ∀ k, Continuous (smoothF f μ k) := fun k => by
    refine continuous_pi fun i => ?_
    refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun c => ?_) (fun c => ?_)
      (integrable_const 1) (Eventually.of_forall fun x => ?_)
    · exact
        (continuous_clamp.measurable.comp (measurable_const.mul (hLmeas c))).aestronglyMeasurable
    · exact Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_clamp_le _
    · exact continuous_clamp.comp (continuous_const.mul (hLcont x))
  have hodd : ∀ k c, smoothF f μ k (-c) = -smoothF f μ k c := fun k c => by
    funext i
    simp only [smoothF, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg, clamp_neg,
      integral_neg]
  -- Borsuk–Ulam: a zero `c k` of norm one of each smoothed map
  choose c hc1 hc0 using fun k => hBU N (smoothF f μ k) (hcont k) (hodd k)
  -- a convergent subsequence on the unit sphere
  obtain ⟨a, ha, ψ, hψ, hlim⟩ := (isCompact_sphere (0 : Fin (N + 1) → ℝ) 1).tendsto_subseq
    (x := c) (fun n => mem_sphere_zero_iff_norm.2 (hc1 n))
  have hpt : ∀ x, Tendsto (fun n => ∑ j, c (ψ n) j * f j x) atTop (𝓝 (∑ j, a j * f j x)) :=
    fun x => ((hLcont x).tendsto a).comp hlim
  have hk : Tendsto (fun n => ((ψ n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hψ.tendsto_atTop
  have hzero : ∀ n i, ∫ x, clamp (((ψ n : ℕ) : ℝ) * ∑ j, c (ψ n) j * f j x) ∂(μ i) = 0 :=
    fun n i => congrFun (hc0 (ψ n)) i
  refine ⟨a, mem_sphere_zero_iff_norm.1 ha, fun i => ⟨?_, ?_⟩⟩
  · exact half_measure_le (μ i) (fun n x => ∑ j, c (ψ n) j * f j x) (fun x => ∑ j, a j * f j x)
      (fun n => hLmeas _) (hLmeas a) hpt _ hk (fun n => hzero n i)
  · have hset : {x | ∑ j, a j * f j x < 0} = {x | 0 < -∑ j, a j * f j x} := by
      ext x; simp
    rw [hset]
    refine half_measure_le (μ i) (fun n x => -∑ j, c (ψ n) j * f j x)
      (fun x => -∑ j, a j * f j x) (fun n => (hLmeas _).neg) (hLmeas a).neg
      (fun x => (hpt x).neg) _ hk (fun n => ?_)
    simp only [mul_neg, clamp_neg, integral_neg, hzero n i, neg_zero]

namespace PartitionAux

open MeasureTheory

/-- The sign cell `s` of a family of polynomials on `ℝ³`. -/
def cell {J : ℕ} (P : Fin J → MvPolynomial (Fin 3) ℝ) (s : Fin J → Bool) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ∀ j, if s j = true then 0 < MvPolynomial.eval (fun i => x i) (P j)
              else MvPolynomial.eval (fun i => x i) (P j) < 0}

lemma continuous_coords : Continuous fun x : EuclideanSpace ℝ (Fin 3) => fun i => x i := by
  fun_prop

lemma measurable_eval (Q : MvPolynomial (Fin 3) ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin 3) => MvPolynomial.eval (fun i => x i) Q :=
  ((MvPolynomial.continuous_eval Q).comp continuous_coords).measurable

/-- Polynomial ham sandwich in `ℝ³`: fewer than `(k+1)^3` finite measures are simultaneously
bisected by a nonzero polynomial of degree at most `3 k`. -/
lemma exists_bisecting_poly (hBU : BorsukUlamStatement) {ι : Type*} [Fintype ι]
    (ν : ι → Measure (EuclideanSpace ℝ (Fin 3))) [∀ i, IsFiniteMeasure (ν i)] (k : ℕ)
    (hk : Fintype.card ι < (k + 1) ^ 3) :
    ∃ Q : MvPolynomial (Fin 3) ℝ, Q ≠ 0 ∧ Q.totalDegree ≤ 3 * k ∧ ∀ i,
      2 * ν i {x | 0 < MvPolynomial.eval (fun i => x i) Q} ≤ ν i Set.univ ∧
      2 * ν i {x | MvPolynomial.eval (fun i => x i) Q < 0} ≤ ν i Set.univ := by
  classical
  set N := Fintype.card ι
  let e : ι ≃ Fin N := Fintype.equivFin ι
  have hcard : Fintype.card (Fin (N + 1)) ≤ Fintype.card (Fin 3 → Fin (k + 1)) := by
    simp only [Fintype.card_fin, Fintype.card_fun]; omega
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  -- `N + 1` distinct exponents with all entries `≤ k`
  let E : Fin (N + 1) → (Fin 3 →₀ ℕ) := fun j =>
    Finsupp.equivFunOnFinite.symm (fun i => ((emb j i : Fin (k + 1)) : ℕ))
  have hE_apply : ∀ j i, E j i = ((emb j i : Fin (k + 1)) : ℕ) := fun j i => by
    simp [E]
  have hE_inj : Function.Injective E := by
    intro j j' h
    apply emb.injective
    funext i
    have := congrArg (fun m : Fin 3 →₀ ℕ => m i) h
    simp only [hE_apply] at this
    exact Fin.ext this
  have hE_deg : ∀ j, ((E j).sum fun _ => id) ≤ 3 * k := by
    intro j
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    calc ∑ i, id ((E j) i) = ∑ i : Fin 3, ((emb j i : Fin (k + 1)) : ℕ) := by
          simp [hE_apply]
      _ ≤ ∑ _i : Fin 3, k := Finset.sum_le_sum fun i _ => Nat.lt_succ_iff.mp (emb j i).isLt
      _ = 3 * k := by simp
  let f : Fin (N + 1) → EuclideanSpace ℝ (Fin 3) → ℝ := fun j x =>
    MvPolynomial.eval (fun i => x i) (MvPolynomial.monomial (E j) 1)
  have hf : ∀ j, Measurable (f j) := fun j => measurable_eval _
  obtain ⟨c, hc1, hc⟩ := ham_sandwich hBU f hf (fun i => ν (e.symm i))
  let Q : MvPolynomial (Fin 3) ℝ := ∑ j, MvPolynomial.monomial (E j) (c j)
  have hQeval : ∀ x : EuclideanSpace ℝ (Fin 3),
      MvPolynomial.eval (fun i => x i) Q = ∑ j, c j * f j x := by
    intro x; simp [Q, f, MvPolynomial.eval_monomial]
  refine ⟨Q, ?_, ?_, fun i => ?_⟩
  · have hc0 : c ≠ 0 := by
      intro h; rw [h, norm_zero] at hc1; exact zero_ne_one hc1
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hc0
    intro hQ
    have := congrArg (fun q : MvPolynomial (Fin 3) ℝ => q.coeff (E j0)) hQ
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hE_inj.eq_iff] at this
    simp at this
    exact hj0 this
  · exact (MvPolynomial.totalDegree_finsetSum _ _).trans
      (Finset.sup_le fun j _ => (MvPolynomial.totalDegree_monomial_le _ _).trans (hE_deg j))
  · have := hc (e i)
    simp only [Equiv.symm_apply_apply] at this
    simp only [hQeval]
    exact this

end PartitionAux

open MeasureTheory PartitionAux in
/-- Guth–Katz polynomial partitioning of a finite measure on ℝ³ into `2^J` sign cells. -/
theorem polynomial_partitioning (hBU : BorsukUlamStatement)
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) [MeasureTheory.IsFiniteMeasure μ]
    (J : ℕ) :
    ∃ P : Fin J → MvPolynomial (Fin 3) ℝ, (∀ j, P j ≠ 0) ∧
      (∀ j : Fin J, (P j).totalDegree ^ 3 ≤ 27 * 2 ^ (j : ℕ)) ∧
      ∀ s : Fin J → Bool,
        2 ^ J * μ {x | ∀ j, if s j = true then 0 < MvPolynomial.eval (fun i => x i) (P j)
                              else MvPolynomial.eval (fun i => x i) (P j) < 0} ≤ μ Set.univ := by
  induction J with
  | zero =>
    refine ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun s => ?_⟩
    simp
  | succ J ih =>
    classical
    obtain ⟨P, hP0, hPdeg, hPμ⟩ := ih
    -- `k` is the least natural number with `2 ^ J < (k + 1) ^ 3`, so `k ^ 3 ≤ 2 ^ J`
    have hex : ∃ k : ℕ, 2 ^ J < (k + 1) ^ 3 := ⟨2 ^ J, by
      calc 2 ^ J < 2 ^ J + 1 := Nat.lt_succ_self _
        _ ≤ (2 ^ J + 1) ^ 3 := Nat.le_self_pow (by norm_num) _⟩
    set k := Nat.find hex with hk_def
    have hk1 : 2 ^ J < (k + 1) ^ 3 := Nat.find_spec hex
    have hk2 : k ^ 3 ≤ 2 ^ J := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0]; simp
      · have := Nat.find_min hex (show k - 1 < k by omega)
        rw [not_lt] at this
        rwa [Nat.sub_add_cancel hpos] at this
    -- bisect all `2 ^ J` current cells at once
    obtain ⟨Q, hQ0, hQdeg, hQμ⟩ := exists_bisecting_poly hBU
      (fun s : Fin J → Bool => μ.restrict (cell P s)) k (by simpa using hk1)
    let P' : Fin (J + 1) → MvPolynomial (Fin 3) ℝ := Fin.snoc P Q
    have hP'last : P' (Fin.last J) = Q := Fin.snoc_last (α := fun _ => MvPolynomial (Fin 3) ℝ) _ _
    have hP'cs : ∀ j : Fin J, P' (Fin.castSucc j) = P j := fun j =>
      Fin.snoc_castSucc (α := fun _ => MvPolynomial (Fin 3) ℝ) _ _ _
    refine ⟨P', ?_, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [hP'last]; exact hQ0
      · rw [hP'cs]; exact hP0 j
    · intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [hP'last, Fin.val_last]
        calc Q.totalDegree ^ 3 ≤ (3 * k) ^ 3 := Nat.pow_le_pow_left hQdeg 3
          _ = 27 * k ^ 3 := by ring
          _ ≤ 27 * 2 ^ J := Nat.mul_le_mul_left _ hk2
      · rw [hP'cs, Fin.val_castSucc]
        exact hPdeg j
    · intro s
      set s0 : Fin J → Bool := fun j => s (Fin.castSucc j) with hs0
      set T : Set (EuclideanSpace ℝ (Fin 3)) := {x | if s (Fin.last J) = true then
          0 < MvPolynomial.eval (fun i => x i) Q else MvPolynomial.eval (fun i => x i) Q < 0}
        with hT
      have hset : {x : EuclideanSpace ℝ (Fin 3) | ∀ j, if s j = true then
            0 < MvPolynomial.eval (fun i => x i) (P' j)
          else MvPolynomial.eval (fun i => x i) (P' j) < 0} =
          T ∩ cell P s0 := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Fin.forall_fin_succ', hP'cs,
          hP'last, cell, hT, hs0]
        tauto
      have hTmeas : MeasurableSet T := by
        by_cases hb : s (Fin.last J) = true
        · simp only [hT, hb, ↓reduceIte]
          exact measurableSet_lt measurable_const (measurable_eval Q)
        · simp only [hT, hb]
          exact measurableSet_lt (measurable_eval Q) measurable_const
      have hhalf : 2 * μ (T ∩ cell P s0) ≤ μ (cell P s0) := by
        have h := hQμ s0
        simp only [Measure.restrict_apply_univ] at h
        rw [← Measure.restrict_apply hTmeas]
        by_cases hb : s (Fin.last J) = true
        · simp only [hT, hb, ↓reduceIte]
          exact h.1
        · simp only [hT, hb]
          exact h.2
      rw [hset, pow_succ, mul_assoc]
      exact (mul_le_mul_right hhalf _).trans (hPμ s0)

/-- The Stone–Tukey ham sandwich theorem, unconditionally: `N` finite measures are bisected by a
nonzero (unit sup norm) combination of any `N + 1` measurable functions. -/
theorem stone_tukey {α : Type*} [MeasurableSpace α] {N : ℕ}
    (f : Fin (N + 1) → α → ℝ) (hf : ∀ j, Measurable (f j))
    (μ : Fin N → MeasureTheory.Measure α) [∀ i, MeasureTheory.IsFiniteMeasure (μ i)] :
    ∃ c : Fin (N + 1) → ℝ, ‖c‖ = 1 ∧ ∀ i,
      2 * μ i {x | 0 < ∑ j, c j * f j x} ≤ μ i Set.univ ∧
      2 * μ i {x | ∑ j, c j * f j x < 0} ≤ μ i Set.univ :=
  ham_sandwich borsukUlam f hf μ

/-- Guth–Katz polynomial partitioning of a finite measure on `ℝ³`, unconditionally: nonzero
polynomials `P 0, …, P (J-1)` with `deg (P j) ^ 3 ≤ 27 · 2 ^ j` whose `2 ^ J` strict sign cells
each carry at most a `2 ^ (-J)` share of the measure. -/
theorem guth_katz_partitioning
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) [MeasureTheory.IsFiniteMeasure μ]
    (J : ℕ) :
    ∃ P : Fin J → MvPolynomial (Fin 3) ℝ, (∀ j, P j ≠ 0) ∧
      (∀ j : Fin J, (P j).totalDegree ^ 3 ≤ 27 * 2 ^ (j : ℕ)) ∧
      ∀ s : Fin J → Bool,
        2 ^ J * μ {x | ∀ j, if s j = true then 0 < MvPolynomial.eval (fun i => x i) (P j)
                              else MvPolynomial.eval (fun i => x i) (P j) < 0} ≤ μ Set.univ :=
  polynomial_partitioning borsukUlam μ J

end WangZahlLot.Obl.wz_coarse_tube_grains.PolyMethod
