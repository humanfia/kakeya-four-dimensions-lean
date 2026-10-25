import Mathlib

set_option linter.unusedVariables false

/-!
# Continuous multilinear Kakeya and its cell form

The frozen hypothesis of `o092` (and the accepted `Submission.k4_multilinear_kakeya`) is the
determinant-weighted multilinear Kakeya inequality for *finitely many* weighted tubes. Section 6
of the paper applies it to *measures* of lines (tangent lines of trajectories weighted by the
trajectory prior), "by rounding line parameters arbitrarily finely on a bounded region".

This file proves that passage (`setLIntegral_contTubeSum_le`): for finite measures `μ i` on
parameter spaces, measurable base points of norm at most `B` and measurable unit directions,
the continuous tube sum `contTubeSum μ a e r` obeys the same inequality on every ball, with
constant `2 ^ n * C`. Its cell form (`sum_volume_mul_rpow_le`) bounds
`∑ c, vol (E c) * lam c ^ (1/(n-1))` over disjoint cells carrying lower bounds `lam c`; and
`le_contTubeSum` produces such lower bounds from measurable sets of successful tuples. With
`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg` this gives the cell counts of the velocity graph
(`n = 3`) and of strip filling and heavy intercept groups (`n = 2`).
-/

namespace Submission.Lib.K4ContinuousKakeya

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The finite determinant-weighted multilinear Kakeya inequality in dimension `n` with
constant `C`, in exactly the shape of the frozen hypothesis of `o092` (and of the accepted
theorem `Submission.k4_multilinear_kakeya`). -/
def FiniteMK (n : ℕ) (C : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ (N : Fin n → ℕ) (a e : (i : Fin n) → Fin (N i) → EuclideanSpace ℝ (Fin n))
    (w : (i : Fin n) → Fin (N i) → ℝ), (∀ (i : Fin n) (k : Fin (N i)), ‖e i k‖ = 1) →
    (∀ (i : Fin n) (k : Fin (N i)), 0 ≤ w i k) →
    MeasureTheory.lintegral MeasureTheory.volume (fun x : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal ((∑ T : ((i : Fin n) → Fin (N i)),
        |Matrix.det (Matrix.of fun i j : Fin n => e i (T i) j)| *
        ∏ i : Fin n, (w i (T i) * (Metric.thickening r (Set.range fun t : ℝ =>
          a i (T i) + t • e i (T i))).indicator (fun _ => (1 : ℝ)) x)) ^
            ((1 : ℝ) / ((n : ℝ) - 1)))) ≤
    ENNReal.ofReal (C * r ^ n * ∏ i : Fin n,
      (∑ k : Fin (N i), w i k) ^ ((1 : ℝ) / ((n : ℝ) - 1)))

/-- The open tube of radius `r` about the full line through `a` with direction `e`. -/
def tube {n : ℕ} (r : ℝ) (a e : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.thickening r (Set.range fun t : ℝ => a + t • e)

lemma measurableSet_tube {n : ℕ} (r : ℝ) (a e : EuclideanSpace ℝ (Fin n)) :
    MeasurableSet (tube r a e) :=
  Metric.isOpen_thickening.measurableSet

/-- For products of numbers of absolute value at most one, the difference of products is
bounded by the sum of the differences. -/
lemma abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |∏ i ∈ s, f i - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has, Finset.sum_insert has]
    have hfa : |f a| ≤ 1 := hf a (Finset.mem_insert_self a s)
    have hgs : |∏ i ∈ s, g i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _)
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    calc |f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i|
        = |f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i| := by ring_nf
      _ ≤ |f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)| + |(f a - g a) * ∏ i ∈ s, g i| :=
          abs_add_le _ _
      _ = |f a| * |∏ i ∈ s, f i - ∏ i ∈ s, g i| + |f a - g a| * |∏ i ∈ s, g i| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * (∑ i ∈ s, |f i - g i|) + |f a - g a| * 1 := by
          gcongr
      _ = |f a - g a| + ∑ i ∈ s, |f i - g i| := by ring

lemma abs_apply_le_norm {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (j : Fin n) : |v j| ≤ ‖v‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j

/-- The determinant of a matrix whose rows are vectors of norm at most one changes by at most
`n! * n * δ` when every row moves by at most `δ`. -/
lemma abs_det_sub_le {n : ℕ} (e e' : Fin n → EuclideanSpace ℝ (Fin n)) (δ : ℝ)
    (he : ∀ i, ‖e i‖ ≤ 1) (he' : ∀ i, ‖e' i‖ ≤ 1) (hδ : ∀ i, ‖e i - e' i‖ ≤ δ) :
    |Matrix.det (Matrix.of fun i j : Fin n => e i j) -
        Matrix.det (Matrix.of fun i j : Fin n => e' i j)| ≤ (n.factorial * n : ℝ) * δ := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  calc |∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ • ∏ i, Matrix.of (fun i j => e i j) (σ i) i -
          Equiv.Perm.sign σ • ∏ i, Matrix.of (fun i j => e' i j) (σ i) i)|
      ≤ ∑ σ : Equiv.Perm (Fin n), |Equiv.Perm.sign σ • ∏ i, Matrix.of (fun i j => e i j) (σ i) i -
          Equiv.Perm.sign σ • ∏ i, Matrix.of (fun i j => e' i j) (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ : Equiv.Perm (Fin n), (n * δ) := by
        apply Finset.sum_le_sum
        intro σ _
        rw [← smul_sub]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · rw [h, one_smul]
          calc |∏ i, Matrix.of (fun i j => e i j) (σ i) i - ∏ i, Matrix.of (fun i j => e' i j) (σ i) i|
              ≤ ∑ i : Fin n, |Matrix.of (fun i j => e i j) (σ i) i -
                  Matrix.of (fun i j => e' i j) (σ i) i| :=
                abs_prod_sub_prod_le _ _ _
                  (fun i _ => (abs_apply_le_norm _ _).trans (he _))
                  (fun i _ => (abs_apply_le_norm _ _).trans (he' _))
            _ ≤ ∑ i : Fin n, δ := by
                apply Finset.sum_le_sum
                intro i _
                simp only [Matrix.of_apply]
                calc |e (σ i) i - e' (σ i) i| = |(e (σ i) - e' (σ i)) i| := by simp
                  _ ≤ ‖e (σ i) - e' (σ i)‖ := abs_apply_le_norm _ _
                  _ ≤ δ := hδ _
            _ = n * δ := by simp
        · rw [h, Units.neg_smul, one_smul, abs_neg]
          calc |∏ i, Matrix.of (fun i j => e i j) (σ i) i - ∏ i, Matrix.of (fun i j => e' i j) (σ i) i|
              ≤ ∑ i : Fin n, |Matrix.of (fun i j => e i j) (σ i) i -
                  Matrix.of (fun i j => e' i j) (σ i) i| :=
                abs_prod_sub_prod_le _ _ _
                  (fun i _ => (abs_apply_le_norm _ _).trans (he _))
                  (fun i _ => (abs_apply_le_norm _ _).trans (he' _))
            _ ≤ ∑ i : Fin n, δ := by
                apply Finset.sum_le_sum
                intro i _
                simp only [Matrix.of_apply]
                calc |e (σ i) i - e' (σ i) i| = |(e (σ i) - e' (σ i)) i| := by simp
                  _ ≤ ‖e (σ i) - e' (σ i)‖ := abs_apply_le_norm _ _
                  _ ≤ δ := hδ _
            _ = n * δ := by simp
    _ = (n.factorial * n : ℝ) * δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Enlarging a tube: a point of the radius-`r` tube about a line with base point of norm at
most `B` and unit direction, lying in the ball of radius `R`, lies in the radius-`2r` tube about
any line whose base point and direction are `δ`-close, provided `δ (1 + R + B + r) ≤ r`. -/
lemma mem_tube_of_close {n : ℕ} {r R B δ : ℝ} {a e a' e' x : EuclideanSpace ℝ (Fin n)}
    (he : ‖e‖ = 1) (ha : ‖a‖ ≤ B) (hx : ‖x‖ ≤ R) (hδ0 : 0 ≤ δ)
    (haa : ‖a - a'‖ ≤ δ) (hee : ‖e - e'‖ ≤ δ) (hδ : δ * (1 + R + B + r) ≤ r)
    (hmem : x ∈ tube r a e) : x ∈ tube (2 * r) a' e' := by
  obtain ⟨y, ⟨t, rfl⟩, hxy⟩ := Metric.mem_thickening_iff.mp hmem
  have hxy' : ‖x - (a + t • e)‖ < r := by rwa [dist_eq_norm] at hxy
  have ht : |t| ≤ R + B + r := by
    have h1 : ‖t • e‖ = |t| := by rw [norm_smul, he, mul_one, Real.norm_eq_abs]
    have h3 : ‖t • e‖ ≤ ‖a + t • e - x‖ + ‖x‖ + ‖a‖ := by
      calc ‖t • e‖ = ‖(a + t • e - x) + x - a‖ := by congr 1; abel
        _ ≤ ‖a + t • e - x + x‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ ‖a + t • e - x‖ + ‖x‖ + ‖a‖ := by gcongr; exact norm_add_le _ _
    have h4 : ‖a + t • e - x‖ = ‖x - (a + t • e)‖ := norm_sub_rev _ _
    rw [h1, h4] at h3
    linarith
  apply Metric.mem_thickening_iff.mpr
  refine ⟨a' + t • e', ⟨t, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have hsplit : x - (a' + t • e') = (x - (a + t • e)) + (a - a') + t • (e - e') := by
    rw [smul_sub]; abel
  rw [hsplit]
  calc ‖(x - (a + t • e)) + (a - a') + t • (e - e')‖
      ≤ ‖(x - (a + t • e)) + (a - a')‖ + ‖t • (e - e')‖ := norm_add_le _ _
    _ ≤ ‖x - (a + t • e)‖ + ‖a - a'‖ + ‖t • (e - e')‖ := by gcongr; exact norm_add_le _ _
    _ < r + δ + (R + B + r) * δ := by
        rw [norm_smul, Real.norm_eq_abs]
        have : |t| * ‖e - e'‖ ≤ (R + B + r) * δ :=
          mul_le_mul ht hee (norm_nonneg _) (by linarith [abs_nonneg t])
        linarith
    _ ≤ 2 * r := by nlinarith

/-- The continuous determinant-weighted tube sum of `n` finite families of lines, given by
base points `a i l` and directions `e i l`, weighted by finite measures `μ i`. -/
def contTubeSum {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : Fin n) → Measure (α i)) (a e : (i : Fin n) → α i → EuclideanSpace ℝ (Fin n))
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ∫⁻ l, ENNReal.ofReal |Matrix.det (Matrix.of fun i j : Fin n => e i (l i) j)| *
    ∏ i, (tube r (a i (l i)) (e i (l i))).indicator (fun _ => (1 : ℝ≥0∞)) x ∂(Measure.pi μ)

/-- A finite measurable partition of a parameter space by `δ`-small cells of the line
parameters, with representatives from the compact parameter set. -/
lemma exists_line_partition {n : ℕ} (hn : 1 ≤ n) {B δ : ℝ} (hδ : 0 < δ) :
    ∃ (m : ℕ) (z : Fin m → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      (∀ k, ‖(z k).1‖ ≤ B ∧ ‖(z k).2‖ = 1) ∧
      ∀ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), ‖p.1‖ ≤ B → ‖p.2‖ = 1 →
        ∃ k, p ∈ Metric.ball (z k) δ := by
  set K₀ : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    Metric.closedBall 0 B ×ˢ Metric.sphere 0 1 with hK₀
  have hK : IsCompact K₀ := (isCompact_closedBall 0 B).prod (isCompact_sphere 0 1)
  obtain ⟨t, htK, htf, hcov⟩ := finite_cover_balls_of_compact hK hδ
  classical
  let T := htf.toFinset
  refine ⟨T.card, fun k => (T.equivFin.symm k : _), ?_, ?_⟩
  · intro k
    have hk : ((T.equivFin.symm k : _) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∈ K₀ :=
      htK ((Set.Finite.mem_toFinset htf).mp (T.equivFin.symm k).2)
    rw [hK₀, Set.mem_prod, Metric.mem_closedBall, dist_zero_right, mem_sphere_zero_iff_norm] at hk
    exact hk
  · intro p hp1 hp2
    have hpK : p ∈ K₀ := by
      rw [hK₀, Set.mem_prod, Metric.mem_closedBall, dist_zero_right, mem_sphere_zero_iff_norm]
      exact ⟨hp1, hp2⟩
    obtain ⟨y, hyt, hpy⟩ := Set.mem_iUnion₂.mp (hcov hpK)
    have hyT : y ∈ T := (Set.Finite.mem_toFinset htf).mpr hyt
    refine ⟨T.equivFin ⟨y, hyT⟩, ?_⟩
    simpa using hpy


/-- The main estimate at a fixed discretization width `δ`. -/
lemma setLIntegral_contTubeSum_le_aux {n : ℕ} (hn : 2 ≤ n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : FiniteMK n C)
    {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : Fin n) → Measure (α i)) [∀ i, IsFiniteMeasure (μ i)]
    (a e : (i : Fin n) → α i → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, Measurable (a i)) (he : ∀ i, Measurable (e i))
    (he1 : ∀ i l, ‖e i l‖ = 1) {B : ℝ} (hB : ∀ i l, ‖a i l‖ ≤ B) {r : ℝ} (hr : 0 < r) (R : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδr : δ * (1 + R + B + r) ≤ r) :
    ∫⁻ x in Metric.closedBall 0 R, contTubeSum μ a e r x ^ ((1 : ℝ) / ((n : ℝ) - 1)) ≤
      ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ i, (μ i univ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) +
      ENNReal.ofReal ((n.factorial * n : ℝ) * δ * ∏ i, (μ i univ).toReal) ^
          ((1 : ℝ) / ((n : ℝ) - 1)) * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) := by
  classical
  set p : ℝ := (1 : ℝ) / ((n : ℝ) - 1) with hp_def
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by rw [hp_def]; apply div_pos one_pos; linarith
  have hp1 : p ≤ 1 := by rw [hp_def, div_le_one (by linarith)]; linarith
  set c : ℝ := (n.factorial * n : ℝ) with hc_def
  have hc0 : 0 ≤ c := by positivity
  -- the net and the partitions
  obtain ⟨m, z, hz, hcov⟩ := exists_line_partition (n := n) (B := B) (by omega) hδ
  let U : (i : Fin n) → Fin m → Set (α i) := fun i k =>
    (fun l => (a i l, e i l)) ⁻¹' Metric.ball (z k) δ
  have hUm : ∀ i k, MeasurableSet (U i k) := fun i k =>
    ((ha i).prodMk (he i)) Metric.isOpen_ball.measurableSet
  let P : (i : Fin n) → Fin m → Set (α i) := fun i => disjointed (U i)
  have hPU : ∀ i k, P i k ⊆ U i k := fun i k => disjointed_subset (U i) k
  have hPm : ∀ i k, MeasurableSet (P i k) := by
    intro i k
    change MeasurableSet (disjointed (U i) k)
    rw [disjointed_eq_inter_compl]
    exact (hUm i k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hUm i j).compl)
  have hPdisj : ∀ i, Pairwise (Function.onFun Disjoint (P i)) := fun i => disjoint_disjointed (U i)
  have hPcov : ∀ i (l : α i), ∃ k, l ∈ P i k := by
    intro i l
    have hU : l ∈ ⋃ k, U i k := by
      obtain ⟨k, hk⟩ := hcov (a i l, e i l) (hB i l) (he1 i l)
      exact Set.mem_iUnion.mpr ⟨k, hk⟩
    rw [← iUnion_disjointed] at hU
    exact Set.mem_iUnion.mp hU
  -- the weights
  let W : (i : Fin n) → Fin m → ℝ := fun i k => (μ i (P i k)).toReal
  have hW0 : ∀ i k, 0 ≤ W i k := fun i k => ENNReal.toReal_nonneg
  have hWsum : ∀ i, ∑ k, μ i (P i k) = μ i univ := by
    intro i
    have h := measure_iUnion (μ := μ i) (hPdisj i) (hPm i)
    rw [tsum_fintype] at h
    rw [← h]
    congr 1
    apply Set.eq_univ_of_forall
    intro l
    exact Set.mem_iUnion.mpr (hPcov i l)
  -- the finite tube sum at radius `2r`
  let D : (Fin n → Fin m) → ℝ := fun T =>
    |Matrix.det (Matrix.of fun i j : Fin n => (z (T i)).2 j)|
  let ind : Fin m → EuclideanSpace ℝ (Fin n) → ℝ := fun k x =>
    (Metric.thickening (2 * r) (Set.range fun t : ℝ => (z k).1 + t • (z k).2)).indicator
      (fun _ => (1 : ℝ)) x
  have hind01 : ∀ k x, 0 ≤ ind k x ∧ ind k x ≤ 1 := by
    intro k x
    simp only [ind]
    by_cases hx : x ∈ Metric.thickening (2 * r) (Set.range fun t : ℝ => (z k).1 + t • (z k).2)
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  let Sfin : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    ∑ T : (i : Fin n) → Fin m, |Matrix.det (Matrix.of fun i j : Fin n => (z (T i)).2 j)| *
      ∏ i : Fin n, (W i (T i) * (Metric.thickening (2 * r)
        (Set.range fun t : ℝ => (z (T i)).1 + t • (z (T i)).2)).indicator (fun _ => (1 : ℝ)) x)
  have hSfin0 : ∀ x, 0 ≤ Sfin x := by
    intro x
    apply Finset.sum_nonneg
    intro T _
    apply mul_nonneg (abs_nonneg _)
    apply Finset.prod_nonneg
    intro i _
    exact mul_nonneg (hW0 _ _) (hind01 _ _).1
  set M : ℝ := ∏ i, (μ i univ).toReal with hM_def
  have hM0 : 0 ≤ M := Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg
  have hWtot : ∀ i, ∑ k, W i k = (μ i univ).toReal := by
    intro i
    simp only [W]
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top _ _), hWsum i]
  -- the pointwise bound
  have hpt : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ R →
      contTubeSum μ a e r x ≤ ENNReal.ofReal (Sfin x + c * δ * M) := by
    intro x hx
    have hg : ∀ l : (i : Fin n) → α i,
        ENNReal.ofReal |Matrix.det (Matrix.of fun i j : Fin n => e i (l i) j)| *
          ∏ i, (tube r (a i (l i)) (e i (l i))).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
        ∑ T : (i : Fin n) → Fin m, (Set.univ.pi fun i => P i (T i)).indicator
          (fun _ => ENNReal.ofReal ((D T + c * δ) * ∏ i, ind (T i) x)) l := by
      intro l
      choose T₀ hT₀ using fun i => hPcov i (l i)
      refine le_trans ?_ (Finset.single_le_sum (f := fun T : (i : Fin n) → Fin m =>
          (Set.univ.pi fun i => P i (T i)).indicator
            (fun _ => ENNReal.ofReal ((D T + c * δ) * ∏ i, ind (T i) x)) l)
          (fun _ _ => zero_le) (Finset.mem_univ T₀))
      have hl : l ∈ Set.univ.pi fun i => P i (T₀ i) := fun i _ => hT₀ i
      simp only
      rw [Set.indicator_of_mem hl]
      have hclose : ∀ i, ‖a i (l i) - (z (T₀ i)).1‖ ≤ δ ∧ ‖e i (l i) - (z (T₀ i)).2‖ ≤ δ := by
        intro i
        have h := hPU i (T₀ i) (hT₀ i)
        simp only [U, Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
        exact ⟨(le_max_left _ _).trans h.le, (le_max_right _ _).trans h.le⟩
      by_cases hall : ∀ i, x ∈ tube r (a i (l i)) (e i (l i))
      · have hprod : ∏ i, (tube r (a i (l i)) (e i (l i))).indicator
            (fun _ => (1 : ℝ≥0∞)) x = 1 := by
          apply Finset.prod_eq_one
          intro i _
          rw [Set.indicator_of_mem (hall i)]
        have hind : ∀ i, ind (T₀ i) x = 1 := by
          intro i
          have hmem : x ∈ Metric.thickening (2 * r)
              (Set.range fun t : ℝ => (z (T₀ i)).1 + t • (z (T₀ i)).2) :=
            mem_tube_of_close (he1 i (l i)) (hB i (l i)) hx hδ.le (hclose i).1 (hclose i).2 hδr
              (hall i)
          simp only [ind]
          rw [Set.indicator_of_mem hmem]
        have hdet : |Matrix.det (Matrix.of fun i j : Fin n => e i (l i) j)| ≤ D T₀ + c * δ := by
          have h := abs_det_sub_le (fun i => e i (l i)) (fun i => (z (T₀ i)).2) δ
            (fun i => (he1 i (l i)).le) (fun i => (hz (T₀ i)).2.le) (fun i => (hclose i).2)
          have h2 := abs_add_le (Matrix.det (Matrix.of fun i j : Fin n => (z (T₀ i)).2 j))
            (Matrix.det (Matrix.of fun i j : Fin n => e i (l i) j) -
              Matrix.det (Matrix.of fun i j : Fin n => (z (T₀ i)).2 j))
          simp only [add_sub_cancel] at h2
          simp only [D]
          linarith
        rw [hprod, mul_one]
        simp only [hind, Finset.prod_const_one, mul_one]
        exact ENNReal.ofReal_le_ofReal hdet
      · simp only [not_forall] at hall
        obtain ⟨i₀, hi₀⟩ := hall
        have h0 : ∏ i, (tube r (a i (l i)) (e i (l i))).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i₀) (Set.indicator_of_notMem hi₀ _)
        rw [h0, mul_zero]
        exact zero_le
    have hbox : ∀ T : (i : Fin n) → Fin m, MeasurableSet (Set.univ.pi fun i => P i (T i)) :=
      fun T => MeasurableSet.univ_pi fun i => hPm i (T i)
    calc contTubeSum μ a e r x
        ≤ ∫⁻ l, ∑ T : (i : Fin n) → Fin m, (Set.univ.pi fun i => P i (T i)).indicator
          (fun _ => ENNReal.ofReal ((D T + c * δ) * ∏ i, ind (T i) x)) l ∂(Measure.pi μ) :=
          lintegral_mono hg
      _ = ∑ T : (i : Fin n) → Fin m, ∫⁻ l, (Set.univ.pi fun i => P i (T i)).indicator
          (fun _ => ENNReal.ofReal ((D T + c * δ) * ∏ i, ind (T i) x)) l ∂(Measure.pi μ) :=
          lintegral_finsetSum _ fun T _ => measurable_const.indicator (hbox T)
      _ = ∑ T : (i : Fin n) → Fin m, ENNReal.ofReal ((D T + c * δ) * ∏ i, ind (T i) x) *
            ∏ i, μ i (P i (T i)) := by
          apply Finset.sum_congr rfl
          intro T _
          rw [lintegral_indicator_const (hbox T), Measure.pi_pi]
      _ = ENNReal.ofReal (∑ T : (i : Fin n) → Fin m,
            (D T + c * δ) * ∏ i, (W i (T i) * ind (T i) x)) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          · apply Finset.sum_congr rfl
            intro T _
            have hDc : 0 ≤ D T + c * δ := by positivity
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hDc,
              ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (hW0 _ _) (hind01 _ _).1),
              ENNReal.ofReal_prod_of_nonneg (fun i _ => (hind01 _ _).1), mul_assoc,
              ← Finset.prod_mul_distrib]
            congr 1
            apply Finset.prod_congr rfl
            intro i _
            rw [ENNReal.ofReal_mul (hW0 _ _), mul_comm]
            congr 1
            simp only [W]
            rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
          · intro T _
            apply mul_nonneg (by positivity)
            exact Finset.prod_nonneg fun i _ => mul_nonneg (hW0 _ _) (hind01 _ _).1
      _ ≤ ENNReal.ofReal (Sfin x + c * δ * M) := by
          apply ENNReal.ofReal_le_ofReal
          have hsplit : ∑ T : (i : Fin n) → Fin m, (D T + c * δ) * ∏ i, (W i (T i) * ind (T i) x)
              = Sfin x + c * δ * ∑ T : (i : Fin n) → Fin m, ∏ i, (W i (T i) * ind (T i) x) := by
            simp only [Sfin, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
            rfl
          rw [hsplit]
          gcongr
          have hprodsum : ∑ T : (i : Fin n) → Fin m, ∏ i, (W i (T i) * ind (T i) x) =
              ∏ i, ∑ k, W i k * ind k x := by
            rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
          rw [hprodsum, hM_def]
          apply Finset.prod_le_prod₀
          · intro i _
            exact Finset.sum_nonneg fun k _ => mul_nonneg (hW0 _ _) (hind01 _ _).1
          · intro i _
            rw [← hWtot i]
            apply Finset.sum_le_sum
            intro k _
            calc W i k * ind k x ≤ W i k * 1 := mul_le_mul_of_nonneg_left (hind01 _ _).2 (hW0 _ _)
              _ = W i k := mul_one _
  -- integrate the pointwise bound over the ball
  have hmeasS : Measurable fun x => ENNReal.ofReal (Sfin x ^ p) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro T _
    apply Measurable.const_mul
    apply Finset.measurable_prod
    intro i _
    apply Measurable.const_mul
    exact measurable_const.indicator Metric.isOpen_thickening.measurableSet
  set E₀ : ℝ≥0∞ := ENNReal.ofReal (c * δ * M) ^ p with hE₀
  have hpt2 : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
      contTubeSum μ a e r x ^ p ≤ ENNReal.ofReal (Sfin x ^ p) + E₀ := by
    intro x hx
    have hx' : ‖x‖ ≤ R := by simpa using hx
    calc contTubeSum μ a e r x ^ p ≤ ENNReal.ofReal (Sfin x + c * δ * M) ^ p :=
          ENNReal.rpow_le_rpow (hpt x hx') hp0.le
      _ ≤ (ENNReal.ofReal (Sfin x) + ENNReal.ofReal (c * δ * M)) ^ p :=
          ENNReal.rpow_le_rpow ENNReal.ofReal_add_le hp0.le
      _ ≤ ENNReal.ofReal (Sfin x) ^ p + ENNReal.ofReal (c * δ * M) ^ p :=
          ENNReal.rpow_add_le_add_rpow _ _ hp0.le hp1
      _ = ENNReal.ofReal (Sfin x ^ p) + E₀ := by
          rw [ENNReal.ofReal_rpow_of_nonneg (hSfin0 x) hp0.le]
  have hfin := hC (2 * r) (by positivity) (fun _ => m) (fun i k => (z k).1) (fun i k => (z k).2) W
    (fun i k => (hz k).2) hW0
  calc ∫⁻ x in Metric.closedBall 0 R, contTubeSum μ a e r x ^ p
      ≤ ∫⁻ x in Metric.closedBall 0 R, (ENNReal.ofReal (Sfin x ^ p) + E₀) :=
        setLIntegral_mono' measurableSet_closedBall hpt2
    _ = (∫⁻ x in Metric.closedBall 0 R, ENNReal.ofReal (Sfin x ^ p)) +
          E₀ * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ (∫⁻ x, ENNReal.ofReal (Sfin x ^ p)) +
          E₀ * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) := by
        gcongr
        exact Measure.restrict_le_self
    _ ≤ ENNReal.ofReal (C * (2 * r) ^ n * ∏ i, (∑ k, W i k) ^ p) +
          E₀ * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ i, (μ i univ) ^ p +
          E₀ * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) := by
        congr 1
        simp only [hWtot]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg
          (fun i _ => Real.rpow_nonneg ENNReal.toReal_nonneg _)]
        congr 1
        · congr 1; ring
        · apply Finset.prod_congr rfl
          intro i _
          rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le,
            ENNReal.ofReal_toReal (measure_ne_top _ _)]

end

/-- **Continuous multilinear Kakeya.** The finite determinant-weighted multilinear Kakeya
inequality with constant `C` implies, for finite measures on bounded line parameters with unit
directions, the same inequality for the continuous tube sum on every ball, with constant
`2 ^ n * C`. -/
theorem setLIntegral_contTubeSum_le {n : ℕ} (hn : 2 ≤ n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : FiniteMK n C)
    {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : Fin n) → Measure (α i)) [∀ i, IsFiniteMeasure (μ i)]
    (a e : (i : Fin n) → α i → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, Measurable (a i)) (he : ∀ i, Measurable (e i))
    (he1 : ∀ i l, ‖e i l‖ = 1) {B : ℝ} (hB : ∀ i l, ‖a i l‖ ≤ B) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    ∫⁻ x in Metric.closedBall 0 R, contTubeSum μ a e r x ^ ((1 : ℝ) / ((n : ℝ) - 1)) ≤
      ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ i, (μ i univ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
  set p : ℝ := (1 : ℝ) / ((n : ℝ) - 1) with hp_def
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by rw [hp_def]; apply div_pos one_pos; linarith
  set c : ℝ := (n.factorial * n : ℝ) with hc_def
  set M : ℝ := ∏ i, (μ i univ).toReal with hM_def
  set V : ℝ≥0∞ := volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) with hV_def
  have hV : V ≠ ⊤ := measure_closedBall_lt_top.ne
  set Q : ℝ := max 1 (1 + R + B + r) with hQ_def
  have hQ : 0 < Q := lt_of_lt_of_le one_pos (le_max_left _ _)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hT : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (c * δ * M) ^ p * V)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun δ : ℝ => c * δ * M) (nhds 0) (nhds 0) := by
      have hcont : Continuous (fun δ : ℝ => c * δ * M) := by fun_prop
      simpa using hcont.tendsto 0
    have h2 : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (c * δ * M)) (nhds 0) (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal h1
    have h3 : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (c * δ * M) ^ p) (nhds 0) (nhds 0) := by
      have := (ENNReal.continuous_rpow_const (y := p)).tendsto 0 |>.comp h2
      rw [ENNReal.zero_rpow_of_pos hp0] at this
      exact this
    have h4 := ENNReal.Tendsto.mul_const h3 (Or.inr hV)
    simp only [zero_mul] at h4
    exact h4.mono_left nhdsWithin_le_nhds
  have hεpos : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have e1 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ENNReal.ofReal (c * δ * M) ^ p * V < ε := hT (Iio_mem_nhds hεpos)
  have e2 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < δ := self_mem_nhdsWithin
  have e3 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < r / Q :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  obtain ⟨δ, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  have hδr : δ * (1 + R + B + r) ≤ r := by
    calc δ * (1 + R + B + r) ≤ δ * Q := mul_le_mul_of_nonneg_left (le_max_right _ _) h2.le
      _ ≤ r / Q * Q := mul_le_mul_of_nonneg_right h3.le hQ.le
      _ = r := div_mul_cancel₀ r hQ.ne'
  calc ∫⁻ x in Metric.closedBall 0 R, contTubeSum μ a e r x ^ p
      ≤ ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ i, (μ i univ) ^ p +
          ENNReal.ofReal (c * δ * M) ^ p * V :=
        setLIntegral_contTubeSum_le_aux hn hC0 hC μ a e ha he he1 hB hr R h2 hδr
    _ ≤ ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ i, (μ i univ) ^ p + ε := by
        gcongr

/-- **Cell form of continuous multilinear Kakeya.** If finitely many pairwise disjoint
measurable cells inside a ball carry lower bounds `lam c` for the continuous tube sum, then
`∑ c, vol (E c) * lam c ^ (1/(n-1))` obeys the multilinear Kakeya bound. Combined with
`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg` (power mean) this counts the cells. -/
theorem sum_volume_mul_rpow_le {n : ℕ} (hn : 2 ≤ n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : FiniteMK n C)
    {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : Fin n) → Measure (α i)) [∀ i, IsFiniteMeasure (μ i)]
    (a e : (i : Fin n) → α i → EuclideanSpace ℝ (Fin n))
    (ha : ∀ i, Measurable (a i)) (he : ∀ i, Measurable (e i))
    (he1 : ∀ i l, ‖e i l‖ = 1) {B : ℝ} (hB : ∀ i l, ‖a i l‖ ≤ B) {r : ℝ} (hr : 0 < r) (R : ℝ)
    {ι : Type*} (s : Finset ι) (E : ι → Set (EuclideanSpace ℝ (Fin n))) (lam : ι → ℝ≥0∞)
    (hEm : ∀ c ∈ s, MeasurableSet (E c)) (hEd : (s : Set ι).PairwiseDisjoint E)
    (hER : ∀ c ∈ s, E c ⊆ Metric.closedBall 0 R)
    (hlam : ∀ c ∈ s, ∀ x ∈ E c, lam c ≤ contTubeSum μ a e r x) :
    ∑ c ∈ s, volume (E c) * lam c ^ ((1 : ℝ) / ((n : ℝ) - 1)) ≤
      ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ i, (μ i univ) ^ ((1 : ℝ) / ((n : ℝ) - 1)) := by
  set p : ℝ := (1 : ℝ) / ((n : ℝ) - 1) with hp_def
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : 0 < p := by rw [hp_def]; apply div_pos one_pos; linarith
  calc ∑ c ∈ s, volume (E c) * lam c ^ p
      = ∑ c ∈ s, ∫⁻ _ in E c, lam c ^ p := by
        apply Finset.sum_congr rfl
        intro c _
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∑ c ∈ s, ∫⁻ x in E c, contTubeSum μ a e r x ^ p := by
        apply Finset.sum_le_sum
        intro c hc
        exact setLIntegral_mono' (hEm c hc) fun x hx => ENNReal.rpow_le_rpow (hlam c hc x hx) hp0.le
    _ = ∫⁻ x in ⋃ c ∈ s, E c, contTubeSum μ a e r x ^ p :=
        (lintegral_biUnion_finset hEd hEm _).symm
    _ ≤ ∫⁻ x in Metric.closedBall 0 R, contTubeSum μ a e r x ^ p :=
        lintegral_mono_set (Set.iUnion₂_subset hER)
    _ ≤ ENNReal.ofReal (2 ^ n * C * r ^ n) * ∏ i, (μ i univ) ^ p :=
        setLIntegral_contTubeSum_le hn hC0 hC μ a e ha he he1 hB hr R

/-- A lower bound for the continuous tube sum at a point from a measurable set of successful
tuples: each member has determinant at least `θ` and all its tubes contain the point. -/
lemma le_contTubeSum {n : ℕ} {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : Fin n) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (a e : (i : Fin n) → α i → EuclideanSpace ℝ (Fin n)) (r θ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (G : Set ((i : Fin n) → α i)) (hGm : MeasurableSet G)
    (hG : ∀ l ∈ G, θ ≤ |Matrix.det (Matrix.of fun i j : Fin n => e i (l i) j)| ∧
      ∀ i, x ∈ tube r (a i (l i)) (e i (l i))) :
    ENNReal.ofReal θ * Measure.pi μ G ≤ contTubeSum μ a e r x := by
  rw [← lintegral_indicator_const hGm]
  apply lintegral_mono
  intro l
  by_cases hl : l ∈ G
  · rw [Set.indicator_of_mem hl]
    obtain ⟨hθ, hx⟩ := hG l hl
    have hprod : ∏ i, (tube r (a i (l i)) (e i (l i))).indicator
        (fun _ => (1 : ℝ≥0∞)) x = 1 := by
      apply Finset.prod_eq_one
      intro i _
      rw [Set.indicator_of_mem (hx i)]
    show ENNReal.ofReal θ ≤ ENNReal.ofReal |Matrix.det (Matrix.of fun i j : Fin n => e i (l i) j)| *
      ∏ i, (tube r (a i (l i)) (e i (l i))).indicator (fun _ => (1 : ℝ≥0∞)) x
    rw [hprod, mul_one]
    exact ENNReal.ofReal_le_ofReal hθ
  · rw [Set.indicator_of_notMem hl]
    exact zero_le

end Submission.Lib.K4ContinuousKakeya
