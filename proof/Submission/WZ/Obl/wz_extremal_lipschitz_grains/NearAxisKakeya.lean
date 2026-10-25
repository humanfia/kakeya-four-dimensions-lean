-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.NearAxisKakeya.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Multilinear Kakeya for nearly axis-parallel cylinders

This file proves the Loomis–Whitney inequality in `ℝ³` (coordinates `Fin 3 → ℝ`) and, by an
induction on scales, a trilinear Kakeya estimate for three families of nearly axis-parallel
cylinders: on the box `[0, K^m)³`, for cylinders of sup-radius `1` whose slopes are at most
`1 / K`, the integral of `(f₀ f₁ f₂)^(1/2)` is at most `512^m (#₀ #₁ #₂)^(1/2)`.

Each step decomposes the box into cubes of side `K`, applies Loomis–Whitney on every cube (where
the cylinders are within distance `1` of axis-parallel ones), compares the count of cylinders
meeting a cube with the count of fattened cylinders, and rescales by `K`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains.MK

lemma sqrt_sq_eq (a : ℝ≥0∞) : (a ^ (1/2:ℝ)) ^ (2:ℝ) = a := by
  rw [← ENNReal.rpow_mul]; norm_num

lemma holder_two {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a ^ (1/2:ℝ) * g a ^ (1/2:ℝ) ∂μ ≤ (∫⁻ a, f a ∂μ) ^ (1/2:ℝ) * (∫⁻ a, g a ∂μ) ^ (1/2:ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun a => f a ^ (1/2:ℝ)) (g := fun a => g a ^ (1/2:ℝ))
    (hf.pow_const _) (hg.pow_const _)
  simp only [Pi.mul_apply, sqrt_sq_eq] at h
  convert h using 2

/-- Loomis–Whitney in product coordinates `q = (z, (x, y))`. -/
theorem lw_prod (A B C : ℝ × ℝ → ℝ≥0∞) (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) :
    ∫⁻ q : ℝ × (ℝ × ℝ), A (q.2.2, q.1) ^ (1/2:ℝ) * B (q.2.1, q.1) ^ (1/2:ℝ) * C q.2 ^ (1/2:ℝ)
      ≤ (∫⁻ w, A w) ^ (1/2:ℝ) * (∫⁻ w, B w) ^ (1/2:ℝ) * (∫⁻ w, C w) ^ (1/2:ℝ) := by
  rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
  -- inner Cauchy–Schwarz for each fixed `z`
  have hin : ∀ z : ℝ, ∫⁻ xy : ℝ × ℝ, A (xy.2, z) ^ (1/2:ℝ) * B (xy.1, z) ^ (1/2:ℝ) *
      C xy ^ (1/2:ℝ) ∂(volume : Measure (ℝ × ℝ))
      ≤ ((∫⁻ x, B (x, z)) * (∫⁻ y, A (y, z))) ^ (1/2:ℝ) * (∫⁻ w, C w) ^ (1/2:ℝ) := by
    intro z
    have h1 := holder_two (volume : Measure (ℝ × ℝ))
      (f := fun xy : ℝ × ℝ => A (xy.2, z) * B (xy.1, z)) (g := C) (by fun_prop) hC.aemeasurable
    have h2 : ∫⁻ xy : ℝ × ℝ, A (xy.2, z) * B (xy.1, z) =
        (∫⁻ x, B (x, z)) * (∫⁻ y, A (y, z)) := by
      have := lintegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (f := fun x => B (x, z)) (g := fun y => A (y, z)) (by fun_prop) (by fun_prop)
      rw [← this, Measure.volume_eq_prod]
      congr 1; ext xy; ring
    rw [h2] at h1
    calc ∫⁻ xy : ℝ × ℝ, A (xy.2, z) ^ (1/2:ℝ) * B (xy.1, z) ^ (1/2:ℝ) * C xy ^ (1/2:ℝ)
        = ∫⁻ xy : ℝ × ℝ, (A (xy.2, z) * B (xy.1, z)) ^ (1/2:ℝ) * C xy ^ (1/2:ℝ) := by
          congr 1; ext xy
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ ≤ _ := h1
  calc ∫⁻ z, ∫⁻ xy : ℝ × ℝ, A (xy.2, z) ^ (1/2:ℝ) * B (xy.1, z) ^ (1/2:ℝ) * C xy ^ (1/2:ℝ)
        ∂(volume : Measure (ℝ × ℝ))
      ≤ ∫⁻ z, ((∫⁻ x, B (x, z)) * (∫⁻ y, A (y, z))) ^ (1/2:ℝ) * (∫⁻ w, C w) ^ (1/2:ℝ) :=
        lintegral_mono hin
    _ = (∫⁻ z, (∫⁻ x, B (x, z)) ^ (1/2:ℝ) * (∫⁻ y, A (y, z)) ^ (1/2:ℝ)) *
          (∫⁻ w, C w) ^ (1/2:ℝ) := by
        rw [← lintegral_mul_const]
        · congr 1; ext z; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        · exact ((Measurable.lintegral_prod_left' (by fun_prop)).pow_const _).mul
            ((Measurable.lintegral_prod_left' (by fun_prop)).pow_const _)
    _ ≤ ((∫⁻ z, ∫⁻ x, B (x, z)) ^ (1/2:ℝ) * (∫⁻ z, ∫⁻ y, A (y, z)) ^ (1/2:ℝ)) *
          (∫⁻ w, C w) ^ (1/2:ℝ) := by
        gcongr
        exact holder_two volume (Measurable.lintegral_prod_left' (by fun_prop)).aemeasurable
          (Measurable.lintegral_prod_left' (by fun_prop)).aemeasurable
    _ = _ := by
        have eB : ∫⁻ z, ∫⁻ x, B (x, z) = ∫⁻ w, B w := by
          rw [lintegral_lintegral_swap (by fun_prop), Measure.volume_eq_prod,
            lintegral_prod _ (by fun_prop)]
        have eA : ∫⁻ z, ∫⁻ y, A (y, z) = ∫⁻ w, A w := by
          rw [lintegral_lintegral_swap (by fun_prop), Measure.volume_eq_prod,
            lintegral_prod _ (by fun_prop)]
        rw [eA, eB]; ring

/-- the equivalence `p ↦ (p 2, (p 0, p 1))` -/
def e3 : (Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)

lemma e3_apply (p : Fin 3 → ℝ) : e3 p = (p 2, (p 0, p 1)) := rfl

lemma e3_mp : MeasurePreserving e3 volume volume := by
  refine (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans ?_
  exact (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)

theorem lw_fin3 (A B C : ℝ × ℝ → ℝ≥0∞) (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) :
    ∫⁻ p : Fin 3 → ℝ, A (p 1, p 2) ^ (1/2:ℝ) * B (p 0, p 2) ^ (1/2:ℝ) * C (p 0, p 1) ^ (1/2:ℝ)
      ≤ (∫⁻ w, A w) ^ (1/2:ℝ) * (∫⁻ w, B w) ^ (1/2:ℝ) * (∫⁻ w, C w) ^ (1/2:ℝ) := by
  have h := e3_mp.lintegral_comp (f := fun q : ℝ × (ℝ × ℝ) =>
    A (q.2.2, q.1) ^ (1/2:ℝ) * B (q.2.1, q.1) ^ (1/2:ℝ) * C q.2 ^ (1/2:ℝ)) (by fun_prop)
  simp only [e3_apply] at h
  rw [h]
  exact lw_prod A B C hA hB hC


/-- The two coordinates transverse to the axis `j`. -/
def tr (j : Fin 3) (p : Fin 3 → ℝ) : ℝ × ℝ := (p (j.succAbove 0), p (j.succAbove 1))

lemma tr_zero (p : Fin 3 → ℝ) : tr 0 p = (p 1, p 2) := rfl
lemma tr_one (p : Fin 3 → ℝ) : tr 1 p = (p 0, p 2) := rfl
lemma tr_two (p : Fin 3 → ℝ) : tr 2 p = (p 0, p 1) := rfl

lemma continuous_tr (j : Fin 3) : Continuous (tr j) := by
  unfold tr; fun_prop

/-- The closed cylinder of family `j` with horizontal sup-radius `r` around the line
`{q | tr j q = b + q j • s}`. -/
def cyl (j : Fin 3) (b s : ℝ × ℝ) (r : ℝ) : Set (Fin 3 → ℝ) :=
  {p | dist (tr j p) (b + p j • s) ≤ r}

lemma isClosed_cyl (j : Fin 3) (b s : ℝ × ℝ) (r : ℝ) : IsClosed (cyl j b s r) := by
  unfold cyl
  apply isClosed_le _ continuous_const
  exact (continuous_tr j).dist (continuous_const.add ((continuous_apply j).smul continuous_const))

lemma measurableSet_cyl (j : Fin 3) (b s : ℝ × ℝ) (r : ℝ) : MeasurableSet (cyl j b s r) :=
  (isClosed_cyl j b s r).measurableSet

/-- Multiplicity of a finite family of cylinders. -/
noncomputable def cnt {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ) (r : ℝ) (p : Fin 3 → ℝ) :
    ℝ≥0∞ :=
  ∑ i, (cyl j (b i) (s i) r).indicator 1 p

lemma measurable_cnt {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ) (r : ℝ) :
    Measurable (cnt j b s r) := by
  unfold cnt
  exact Finset.measurable_sum _ fun i _ => measurable_one.indicator (measurableSet_cyl _ _ _ _)

lemma cnt_le_card {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ) (r : ℝ)
    (p : Fin 3 → ℝ) : cnt j b s r p ≤ Fintype.card ι := by
  unfold cnt
  calc ∑ i, (cyl j (b i) (s i) r).indicator 1 p ≤ ∑ _i : ι, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun i _ => indicator_le_self' (fun _ _ => zero_le_one) p
    _ = Fintype.card ι := by simp

/-- Axis-parallel half-open cube. -/
def cube (c : Fin 3 → ℝ) (W : ℝ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ (fun k => Set.Ico (c k) (c k + W))

lemma measurableSet_cube (c : Fin 3 → ℝ) (W : ℝ) : MeasurableSet (cube c W) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico

lemma volume_cube (c : Fin 3 → ℝ) (W : ℝ) :
    volume (cube c W) = ENNReal.ofReal W ^ 3 := by
  rw [cube, volume_pi_pi]
  simp [Real.volume_Ico]

lemma dist_tr_lt {c : Fin 3 → ℝ} {W : ℝ} {p q : Fin 3 → ℝ} (hp : p ∈ cube c W)
    (hq : q ∈ cube c W) (j : Fin 3) : dist (tr j p) (tr j q) < W := by
  have h : ∀ k, |p k - q k| < W := by
    intro k
    have h1 := hp k (mem_univ _); have h2 := hq k (mem_univ _)
    simp only [mem_Ico] at h1 h2
    rw [abs_lt]; constructor <;> linarith
  have hW : 0 < W := lt_of_le_of_lt (abs_nonneg _) (h 0)
  rw [tr, tr, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  exact ⟨h _, h _⟩

lemma abs_sub_le_of_mem_cube {c : Fin 3 → ℝ} {W : ℝ} {p : Fin 3 → ℝ} (hp : p ∈ cube c W)
    (k : Fin 3) : |p k - c k| ≤ W := by
  have h1 := hp k (mem_univ _)
  simp only [mem_Ico] at h1
  rw [abs_le]; constructor <;> linarith

/-- Inside a cube of side `W`, a cylinder with slope at most `ν` lies over a square. -/
lemma tr_mem_closedBall {j : Fin 3} {b s : ℝ × ℝ} {r ν W : ℝ} {c p : Fin 3 → ℝ}
    (hs : ‖s‖ ≤ ν) (hp : p ∈ cube c W) (hpc : p ∈ cyl j b s r) :
    tr j p ∈ Metric.closedBall (b + c j • s) (r + W * ν) := by
  rw [Metric.mem_closedBall]
  have hW : 0 ≤ W := le_trans (abs_nonneg _) (abs_sub_le_of_mem_cube hp 0)
  calc dist (tr j p) (b + c j • s) ≤ dist (tr j p) (b + p j • s) + dist (b + p j • s) (b + c j • s) :=
        dist_triangle _ _ _
    _ ≤ r + W * ν := by
        apply add_le_add hpc
        rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (abs_sub_le_of_mem_cube hp j) hs (norm_nonneg _) hW

/-- A cylinder meeting a cube of side `W` covers the whole cube after fattening. -/
lemma mem_cyl_fat {j : Fin 3} {b s : ℝ × ℝ} {r ν W : ℝ} {c p q : Fin 3 → ℝ}
    (hs : ‖s‖ ≤ ν) (hp : p ∈ cube c W) (hq : q ∈ cube c W) (hqc : q ∈ cyl j b s r) :
    p ∈ cyl j b s (r + W + W * ν) := by
  have hW : 0 ≤ W := le_trans (abs_nonneg _) (abs_sub_le_of_mem_cube hp 0)
  show dist (tr j p) (b + p j • s) ≤ r + W + W * ν
  calc dist (tr j p) (b + p j • s) ≤ dist (tr j p) (tr j q) + dist (tr j q) (b + q j • s)
        + dist (b + q j • s) (b + p j • s) := dist_triangle4 _ _ _ _
    _ ≤ W + r + W * ν := by
        refine add_le_add (add_le_add (dist_tr_lt hp hq j).le hqc) ?_
        rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
        have : |q j - p j| ≤ W := by
          have h1 := hp j (mem_univ _); have h2 := hq j (mem_univ _)
          simp only [mem_Ico] at h1 h2
          rw [abs_le]; constructor <;> linarith
        exact mul_le_mul this hs (norm_nonneg _) hW
    _ = r + W + W * ν := by ring


lemma volume_closedBall_prod (a : ℝ × ℝ) (r : ℝ) :
    volume (Metric.closedBall a r) = ENNReal.ofReal (2 * r) ^ 2 := by
  rw [← closedBall_prod_same, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_closedBall,
    Real.volume_closedBall, sq]

/-- The cylinders of a family that meet a given cube. -/
noncomputable def hit {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ) (c : Fin 3 → ℝ)
    (W : ℝ) : Finset ι := by
  classical exact Finset.univ.filter (fun i => (cyl j (b i) (s i) 1 ∩ cube c W).Nonempty)

lemma mem_hit {ι : Type*} [Fintype ι] {j : Fin 3} {b s : ι → ℝ × ℝ} {c : Fin 3 → ℝ} {W : ℝ}
    {i : ι} : i ∈ hit j b s c W ↔ (cyl j (b i) (s i) 1 ∩ cube c W).Nonempty := by
  classical
  unfold hit
  simp

/-- The square-count dominating a family on a cube. -/
noncomputable def sqCount {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ) (c : Fin 3 → ℝ)
    (W R : ℝ) (w : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ i ∈ hit j b s c W, (Metric.closedBall (b i + c j • s i) R).indicator 1 w

/-- On a cube, a count of cylinders of slope `≤ ν` is dominated by a count of squares in the
transverse coordinates. -/
lemma cnt_le_sq {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ) {ν W : ℝ}
    (hs : ∀ i, ‖s i‖ ≤ ν) (c : Fin 3 → ℝ) {p : Fin 3 → ℝ} (hp : p ∈ cube c W) :
    cnt j b s 1 p ≤ sqCount j b s c W (1 + W * ν) (tr j p) := by
  classical
  unfold cnt sqCount
  rw [← Finset.sum_subset (Finset.subset_univ (hit j b s c W))]
  · apply Finset.sum_le_sum
    intro i _
    by_cases hpi : p ∈ cyl j (b i) (s i) 1
    · rw [indicator_of_mem hpi, indicator_of_mem (tr_mem_closedBall (hs i) hp hpi)]
      simp
    · rw [indicator_of_notMem hpi]; exact zero_le
  · intro i _ hi
    apply indicator_of_notMem
    intro hpi
    exact hi (mem_hit.2 ⟨p, hpi, hp⟩)

lemma card_le_cnt_fat {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ) {ν W : ℝ}
    (hs : ∀ i, ‖s i‖ ≤ ν) (c : Fin 3 → ℝ) {p : Fin 3 → ℝ} (hp : p ∈ cube c W) :
    ((hit j b s c W).card : ℝ≥0∞) ≤ cnt j b s (1 + W + W * ν) p := by
  classical
  unfold cnt
  calc ((hit j b s c W).card : ℝ≥0∞)
      = ∑ i ∈ hit j b s c W,
          (cyl j (b i) (s i) (1 + W + W * ν)).indicator (1 : (Fin 3 → ℝ) → ℝ≥0∞) p := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨q, hq1, hq2⟩ := mem_hit.1 hi
        rw [indicator_of_mem (mem_cyl_fat (hs i) hp hq2 hq1)]
        simp
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)


/-- Product of the three square-rooted counts. -/
noncomputable def tri {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
    (b₀ s₀ : ι₀ → ℝ × ℝ) (b₁ s₁ : ι₁ → ℝ × ℝ) (b₂ s₂ : ι₂ → ℝ × ℝ) (r : ℝ)
    (p : Fin 3 → ℝ) : ℝ≥0∞ :=
  cnt 0 b₀ s₀ r p ^ (1/2:ℝ) * cnt 1 b₁ s₁ r p ^ (1/2:ℝ) * cnt 2 b₂ s₂ r p ^ (1/2:ℝ)

lemma measurable_tri {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
    (b₀ s₀ : ι₀ → ℝ × ℝ) (b₁ s₁ : ι₁ → ℝ × ℝ) (b₂ s₂ : ι₂ → ℝ × ℝ) (r : ℝ) :
    Measurable (tri b₀ s₀ b₁ s₁ b₂ s₂ r) := by
  unfold tri
  exact (((measurable_cnt _ _ _ _).pow_const _).mul ((measurable_cnt _ _ _ _).pow_const _)).mul
    ((measurable_cnt _ _ _ _).pow_const _)

lemma measurable_sqCount {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ)
    (c : Fin 3 → ℝ) (W R : ℝ) : Measurable (sqCount j b s c W R) := by
  unfold sqCount
  exact Finset.measurable_sum _ fun i _ =>
    measurable_one.indicator Metric.isClosed_closedBall.measurableSet

lemma lintegral_sqCount {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ)
    (c : Fin 3 → ℝ) (W R : ℝ) :
    ∫⁻ w, sqCount j b s c W R w = (hit j b s c W).card * ENNReal.ofReal (2 * R) ^ 2 := by
  unfold sqCount
  rw [lintegral_finsetSum _ (fun i _ =>
    measurable_one.indicator Metric.isClosed_closedBall.measurableSet)]
  simp_rw [lintegral_indicator_one Metric.isClosed_closedBall.measurableSet,
    volume_closedBall_prod]
  simp

lemma sqrt_mul_sq (N a : ℝ≥0∞) : (N * a ^ 2) ^ (1/2:ℝ) = N ^ (1/2:ℝ) * a := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- The basic one-cube estimate. -/
theorem cube_est {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
    (b₀ s₀ : ι₀ → ℝ × ℝ) (b₁ s₁ : ι₁ → ℝ × ℝ) (b₂ s₂ : ι₂ → ℝ × ℝ) {ν W : ℝ} (hW : 0 < W)
    (hs₀ : ∀ i, ‖s₀ i‖ ≤ ν) (hs₁ : ∀ i, ‖s₁ i‖ ≤ ν) (hs₂ : ∀ i, ‖s₂ i‖ ≤ ν)
    (c : Fin 3 → ℝ) :
    ∫⁻ p in cube c W, tri b₀ s₀ b₁ s₁ b₂ s₂ 1 p
      ≤ ENNReal.ofReal (2 * (1 + W * ν)) ^ 3 / ENNReal.ofReal W ^ 3 *
        ∫⁻ p in cube c W, tri b₀ s₀ b₁ s₁ b₂ s₂ (1 + W + W * ν) p := by
  obtain ⟨R, hR⟩ : ∃ R, R = 1 + W * ν := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = ENNReal.ofReal (2 * R) := ⟨_, rfl⟩
  obtain ⟨N₀, hN₀⟩ : ∃ N : ℝ≥0∞, N = ((hit 0 b₀ s₀ c W).card : ℝ≥0∞) := ⟨_, rfl⟩
  obtain ⟨N₁, hN₁⟩ : ∃ N : ℝ≥0∞, N = ((hit 1 b₁ s₁ c W).card : ℝ≥0∞) := ⟨_, rfl⟩
  obtain ⟨N₂, hN₂⟩ : ∃ N : ℝ≥0∞, N = ((hit 2 b₂ s₂ c W).card : ℝ≥0∞) := ⟨_, rfl⟩
  rw [← hR, ← ha]
  have step1 : ∫⁻ p in cube c W, tri b₀ s₀ b₁ s₁ b₂ s₂ 1 p
      ≤ (N₀ ^ (1/2:ℝ) * a) * (N₁ ^ (1/2:ℝ) * a) * (N₂ ^ (1/2:ℝ) * a) := by
    calc ∫⁻ p in cube c W, tri b₀ s₀ b₁ s₁ b₂ s₂ 1 p
        ≤ ∫⁻ p in cube c W, sqCount 0 b₀ s₀ c W R (p 1, p 2) ^ (1/2:ℝ) *
            sqCount 1 b₁ s₁ c W R (p 0, p 2) ^ (1/2:ℝ) *
            sqCount 2 b₂ s₂ c W R (p 0, p 1) ^ (1/2:ℝ) := by
          apply setLIntegral_mono (by
            exact ((((measurable_sqCount _ _ _ _ _ _).comp (by fun_prop)).pow_const _).mul
              (((measurable_sqCount _ _ _ _ _ _).comp (by fun_prop)).pow_const _)).mul
              (((measurable_sqCount _ _ _ _ _ _).comp (by fun_prop)).pow_const _))
          intro p hp
          unfold tri
          have h0 := cnt_le_sq 0 b₀ s₀ hs₀ c hp
          have h1 := cnt_le_sq 1 b₁ s₁ hs₁ c hp
          have h2 := cnt_le_sq 2 b₂ s₂ hs₂ c hp
          rw [tr_zero, ← hR] at h0
          rw [tr_one, ← hR] at h1
          rw [tr_two, ← hR] at h2
          gcongr
      _ ≤ ∫⁻ p : Fin 3 → ℝ, sqCount 0 b₀ s₀ c W R (p 1, p 2) ^ (1/2:ℝ) *
            sqCount 1 b₁ s₁ c W R (p 0, p 2) ^ (1/2:ℝ) *
            sqCount 2 b₂ s₂ c W R (p 0, p 1) ^ (1/2:ℝ) := by
          exact setLIntegral_le_lintegral (cube c W) (fun p : Fin 3 → ℝ =>
            sqCount 0 b₀ s₀ c W R (p 1, p 2) ^ (1/2:ℝ) *
            sqCount 1 b₁ s₁ c W R (p 0, p 2) ^ (1/2:ℝ) *
            sqCount 2 b₂ s₂ c W R (p 0, p 1) ^ (1/2:ℝ))
      _ ≤ (∫⁻ w, sqCount 0 b₀ s₀ c W R w) ^ (1/2:ℝ) * (∫⁻ w, sqCount 1 b₁ s₁ c W R w) ^ (1/2:ℝ)
            * (∫⁻ w, sqCount 2 b₂ s₂ c W R w) ^ (1/2:ℝ) :=
          lw_fin3 (sqCount 0 b₀ s₀ c W R) (sqCount 1 b₁ s₁ c W R) (sqCount 2 b₂ s₂ c W R)
            (measurable_sqCount _ _ _ _ _ _) (measurable_sqCount _ _ _ _ _ _)
            (measurable_sqCount _ _ _ _ _ _)
      _ = _ := by
          simp_rw [lintegral_sqCount, sqrt_mul_sq, ha, hN₀, hN₁, hN₂]
  have step2 : ENNReal.ofReal W ^ 3 * (N₀ ^ (1/2:ℝ) * N₁ ^ (1/2:ℝ) * N₂ ^ (1/2:ℝ))
      ≤ ∫⁻ p in cube c W, tri b₀ s₀ b₁ s₁ b₂ s₂ (1 + W + W * ν) p := by
    rw [← volume_cube c W, mul_comm, ← setLIntegral_const]
    apply setLIntegral_mono (measurable_tri _ _ _ _ _ _ _)
    intro p hp
    unfold tri
    have h0 := card_le_cnt_fat 0 b₀ s₀ hs₀ c hp
    have h1 := card_le_cnt_fat 1 b₁ s₁ hs₁ c hp
    have h2 := card_le_cnt_fat 2 b₂ s₂ hs₂ c hp
    rw [← hN₀] at h0
    rw [← hN₁] at h1
    rw [← hN₂] at h2
    gcongr
  have hw0 : ENNReal.ofReal W ^ 3 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hW).ne'
  have hwt : ENNReal.ofReal W ^ 3 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  calc ∫⁻ p in cube c W, tri b₀ s₀ b₁ s₁ b₂ s₂ 1 p
      ≤ a ^ 3 * (N₀ ^ (1/2:ℝ) * N₁ ^ (1/2:ℝ) * N₂ ^ (1/2:ℝ)) := by
        refine step1.trans (le_of_eq ?_); ring
    _ = a ^ 3 / ENNReal.ofReal W ^ 3 *
          (ENNReal.ofReal W ^ 3 * (N₀ ^ (1/2:ℝ) * N₁ ^ (1/2:ℝ) * N₂ ^ (1/2:ℝ))) := by
        rw [← mul_assoc (a ^ 3 / ENNReal.ofReal W ^ 3), ENNReal.div_mul_cancel hw0 hwt]
    _ ≤ _ := by gcongr


/-! ### The grid of cubes of side `W` -/

/-- Grid cube with integer index `k`. -/
def gcube (W : ℝ) (k : Fin 3 → ℤ) : Set (Fin 3 → ℝ) := cube (fun i => W * k i) W

lemma mem_gcube_floor {W : ℝ} (hW : 0 < W) (p : Fin 3 → ℝ) :
    p ∈ gcube W (fun i => ⌊p i / W⌋) := by
  intro i _
  simp only [mem_Ico]
  have h1 := Int.floor_le (p i / W)
  have h2 := Int.lt_floor_add_one (p i / W)
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hW.le
    rwa [mul_div_cancel₀ _ hW.ne'] at this
  · have := mul_lt_mul_of_pos_left h2 hW
    rw [mul_div_cancel₀ _ hW.ne', mul_add, mul_one] at this
    linarith

lemma gcube_index_eq {W : ℝ} (hW : 0 < W) {p : Fin 3 → ℝ} {k : Fin 3 → ℤ}
    (hp : p ∈ gcube W k) : k = fun i => ⌊p i / W⌋ := by
  funext i
  have h := hp i (mem_univ _)
  simp only [mem_Ico] at h
  symm
  rw [Int.floor_eq_iff]
  constructor
  · rw [le_div_iff₀ hW]; linarith
  · rw [div_lt_iff₀ hW]; linarith

lemma pairwise_disjoint_gcube {W : ℝ} (hW : 0 < W) :
    Pairwise (Function.onFun Disjoint (gcube W)) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro p hp hp'
  exact hkk' ((gcube_index_eq hW hp).trans (gcube_index_eq hW hp').symm)

lemma iUnion_gcube {W : ℝ} (hW : 0 < W) : (⋃ k, gcube W k) = univ :=
  eq_univ_of_forall fun p => mem_iUnion.2 ⟨_, mem_gcube_floor hW p⟩

lemma lintegral_eq_tsum_gcube {W : ℝ} (hW : 0 < W) (f : (Fin 3 → ℝ) → ℝ≥0∞) :
    ∫⁻ p, f p = ∑' k, ∫⁻ p in gcube W k, f p := by
  conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure (Fin 3 → ℝ))), ← iUnion_gcube hW]
  exact lintegral_iUnion (fun k => measurableSet_cube _ _) (pairwise_disjoint_gcube hW) f

/-- A grid cube of side `K` lies inside the box `[0, K^(m+1))^3` or misses it. -/
lemma gcube_sub_or_disjoint (K : ℕ) (hK : 1 ≤ K) (m : ℕ) (k : Fin 3 → ℤ) :
    gcube K k ⊆ cube 0 ((K : ℝ) ^ (m + 1)) ∨ Disjoint (gcube K k) (cube 0 ((K : ℝ) ^ (m + 1))) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases h : ∀ i, 0 ≤ k i ∧ k i + 1 ≤ (K : ℤ) ^ m
  · left
    intro p hp i _
    have hpi := hp i (mem_univ _)
    simp only [mem_Ico, Pi.zero_apply, zero_add] at hpi ⊢
    obtain ⟨h1, h2⟩ := h i
    have h1' : (0 : ℝ) ≤ k i := by exact_mod_cast h1
    have h2' : (k i : ℝ) + 1 ≤ (K : ℝ) ^ m := by exact_mod_cast h2
    constructor
    · nlinarith
    · calc p i < K * k i + K := hpi.2
        _ = K * (k i + 1) := by ring
        _ ≤ K * (K : ℝ) ^ m := mul_le_mul_of_nonneg_left h2' hK0.le
        _ = (K : ℝ) ^ (m + 1) := by ring
  · right
    simp only [not_forall, not_and, not_le] at h
    obtain ⟨i, hi⟩ := h
    rw [Set.disjoint_left]
    intro p hp hp'
    have hpi := hp i (mem_univ _)
    have hpi' := hp' i (mem_univ _)
    simp only [mem_Ico, Pi.zero_apply, zero_add] at hpi hpi'
    by_cases h0 : 0 ≤ k i
    · have h3 := hi h0
      have h3' : (K : ℤ) ^ m ≤ k i := by omega
      have h3'' : (K : ℝ) ^ m ≤ k i := by exact_mod_cast h3'
      have : (K : ℝ) ^ (m + 1) ≤ K * k i := by
        calc (K : ℝ) ^ (m + 1) = K * (K : ℝ) ^ m := by ring
          _ ≤ K * k i := mul_le_mul_of_nonneg_left h3'' hK0.le
      linarith
    · have h4 : k i + 1 ≤ 0 := by omega
      have h4' : (k i : ℝ) + 1 ≤ 0 := by exact_mod_cast h4
      have : (K : ℝ) * k i + K ≤ 0 := by nlinarith
      linarith

/-- Summing a cube-by-cube estimate over the box `[0, K^(m+1))^3`. -/
lemma box_le_of_cube_le (K : ℕ) (hK : 1 ≤ K) (m : ℕ) {f g : (Fin 3 → ℝ) → ℝ≥0∞} (C : ℝ≥0∞)
    (h : ∀ k : Fin 3 → ℤ, ∫⁻ p in gcube K k, f p ≤ C * ∫⁻ p in gcube K k, g p) :
    ∫⁻ p in cube 0 ((K : ℝ) ^ (m + 1)), f p ≤ C * ∫⁻ p in cube 0 ((K : ℝ) ^ (m + 1)), g p := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hD := measurableSet_cube (0 : Fin 3 → ℝ) ((K : ℝ) ^ (m + 1))
  rw [← lintegral_indicator hD, ← lintegral_indicator hD, lintegral_eq_tsum_gcube hK0,
    lintegral_eq_tsum_gcube hK0, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rcases gcube_sub_or_disjoint K hK m k with hs | hd
  · rw [setLIntegral_indicator hD, setLIntegral_indicator hD, Set.inter_eq_right.2 hs]
    exact h k
  · rw [setLIntegral_indicator hD, setLIntegral_indicator hD, hd.symm.inter_eq]
    simp

/-! ### Rescaling and covering -/

lemma smul_mem_cube_iff {K : ℝ} (hK : 0 < K) (L : ℝ) (p : Fin 3 → ℝ) :
    K • p ∈ cube 0 (K * L) ↔ p ∈ cube 0 L := by
  simp only [cube, mem_pi, mem_univ, true_implies, mem_Ico, Pi.zero_apply, zero_add,
    Pi.smul_apply, smul_eq_mul]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨nonneg_of_mul_nonneg_right (by linarith) hK, lt_of_mul_lt_mul_left h2 hK.le⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_nonneg hK.le h1, mul_lt_mul_of_pos_left h2 hK⟩

lemma tr_smul (j : Fin 3) (K : ℝ) (p : Fin 3 → ℝ) : tr j (K • p) = K • tr j p := by
  simp [tr]

lemma smul_mem_cyl_iff {K : ℝ} (hK : 0 < K) (j : Fin 3) (b s : ℝ × ℝ) (r : ℝ)
    (p : Fin 3 → ℝ) : K • p ∈ cyl j b s r ↔ p ∈ cyl j (K⁻¹ • b) s (r / K) := by
  simp only [cyl, mem_ofPred_eq]
  have e : b + (K • p) j • s = K • (K⁻¹ • b + p j • s) := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hK.ne', one_smul, Pi.smul_apply, smul_eq_mul,
      mul_smul]
  rw [tr_smul, e, dist_smul₀, Real.norm_eq_abs, abs_of_pos hK, le_div_iff₀ hK, mul_comm]

lemma cnt_smul {ι : Type*} [Fintype ι] {K : ℝ} (hK : 0 < K) (j : Fin 3) (b s : ι → ℝ × ℝ)
    (r : ℝ) (p : Fin 3 → ℝ) :
    cnt j b s r (K • p) = cnt j (fun i => K⁻¹ • b i) s (r / K) p := by
  unfold cnt
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : p ∈ cyl j (K⁻¹ • b i) (s i) (r / K)
  · rw [indicator_of_mem ((smul_mem_cyl_iff hK j _ _ _ p).2 h), indicator_of_mem h]; rfl
  · rw [indicator_of_notMem (fun h' => h ((smul_mem_cyl_iff hK j _ _ _ p).1 h')),
      indicator_of_notMem h]

/-- The four unit shifts used to cover a cylinder of radius `2`. -/
def shift (σ : Bool × Bool) : ℝ × ℝ := (if σ.1 then 1 else -1, if σ.2 then 1 else -1)

lemma exists_shift {x : ℝ} (hx : |x| ≤ 2) : ∃ t : Bool, |x - (if t then 1 else -1)| ≤ 1 := by
  rw [abs_le] at hx
  by_cases h : 0 ≤ x
  · exact ⟨true, by simp only [ite_true]; rw [abs_le]; constructor <;> linarith⟩
  · exact ⟨false, by simp only [Bool.false_eq_true, ite_false]; rw [abs_le]; constructor <;> linarith⟩

lemma mem_cyl_shift {j : Fin 3} {b s : ℝ × ℝ} {r : ℝ} (hr : r ≤ 2) {p : Fin 3 → ℝ}
    (hp : p ∈ cyl j b s r) : ∃ σ : Bool × Bool, p ∈ cyl j (b + shift σ) s 1 := by
  simp only [cyl, mem_ofPred_eq, Prod.dist_eq, Real.dist_eq, max_le_iff] at hp ⊢
  obtain ⟨t₁, ht₁⟩ := exists_shift (x := (tr j p).1 - (b + p j • s).1) (by linarith [hp.1])
  obtain ⟨t₂, ht₂⟩ := exists_shift (x := (tr j p).2 - (b + p j • s).2) (by linarith [hp.2])
  refine ⟨(t₁, t₂), ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, shift] at ht₁ ⊢
    convert ht₁ using 2; ring
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, shift] at ht₂ ⊢
    convert ht₂ using 2; ring

lemma cnt_le_cnt_shift {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ) {r : ℝ}
    (hr : r ≤ 2) (p : Fin 3 → ℝ) :
    cnt j b s r p ≤ cnt j (fun x : ι × (Bool × Bool) => b x.1 + shift x.2)
      (fun x => s x.1) 1 p := by
  unfold cnt
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : p ∈ cyl j (b i) (s i) r
  · obtain ⟨σ, hσ⟩ := mem_cyl_shift hr h
    rw [indicator_of_mem h]
    calc (1 : (Fin 3 → ℝ) → ℝ≥0∞) p
        = (cyl j (b i + shift σ) (s i) 1).indicator 1 p := by rw [indicator_of_mem hσ]
      _ ≤ ∑ σ', (cyl j (b i + shift σ') (s i) 1).indicator (1 : (Fin 3 → ℝ) → ℝ≥0∞) p :=
          Finset.single_le_sum (f := fun σ' => (cyl j (b i + shift σ') (s i) 1).indicator
            (1 : (Fin 3 → ℝ) → ℝ≥0∞) p) (fun _ _ => zero_le) (Finset.mem_univ σ)
  · rw [indicator_of_notMem h]; exact zero_le


lemma lintegral_cube_smul {K : ℝ} (hK : 0 < K) (L : ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ p in cube 0 (K * L), F p = ENNReal.ofReal K ^ 3 * ∫⁻ p in cube 0 L, F (K • p) := by
  have hD := measurableSet_cube (0 : Fin 3 → ℝ) (K * L)
  have hD' := measurableSet_cube (0 : Fin 3 → ℝ) L
  have hmap := Measure.map_addHaar_smul (volume : Measure (Fin 3 → ℝ)) hK.ne'
  rw [Module.finrank_fin_fun] at hmap
  have key : ∫⁻ p, (cube 0 (K * L)).indicator F (K • p) =
      ENNReal.ofReal |(K ^ 3)⁻¹| * ∫⁻ p, (cube 0 (K * L)).indicator F p := by
    have h1 := lintegral_map (μ := (volume : Measure (Fin 3 → ℝ))) (hF.indicator hD)
      (measurable_const_smul K)
    rw [hmap, lintegral_smul_measure, smul_eq_mul] at h1
    exact h1.symm
  have hind : ∀ p, (cube 0 (K * L)).indicator F (K • p) =
      (cube 0 L).indicator (fun p => F (K • p)) p := by
    intro p
    by_cases hp : p ∈ cube 0 L
    · rw [indicator_of_mem ((smul_mem_cube_iff hK L p).2 hp), indicator_of_mem hp]
    · rw [indicator_of_notMem (fun h => hp ((smul_mem_cube_iff hK L p).1 h)),
        indicator_of_notMem hp]
  simp_rw [hind] at key
  rw [lintegral_indicator hD', lintegral_indicator hD] at key
  rw [key, ← mul_assoc]
  have h3 : ENNReal.ofReal K ^ 3 * ENNReal.ofReal |(K ^ 3)⁻¹| = 1 := by
    rw [abs_of_pos (by positivity), ← ENNReal.ofReal_pow hK.le,
      ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  rw [h3, one_mul]

lemma sqrt_mul_four (N : ℝ≥0∞) : (N * ((2 : ℕ) * (2 : ℕ))) ^ (1/2:ℝ) = N ^ (1/2:ℝ) * 2 := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [show ((2 : ℕ) : ℝ≥0∞) * ((2 : ℕ) : ℝ≥0∞) = 2 ^ (2:ℝ) by norm_num, ← ENNReal.rpow_mul]
  norm_num

lemma tri_mono_card {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
    (b₀ s₀ : ι₀ → ℝ × ℝ) (b₁ s₁ : ι₁ → ℝ × ℝ) (b₂ s₂ : ι₂ → ℝ × ℝ) (r : ℝ) (p : Fin 3 → ℝ) :
    tri b₀ s₀ b₁ s₁ b₂ s₂ r p ≤ (Fintype.card ι₀ : ℝ≥0∞) ^ (1/2:ℝ) *
      (Fintype.card ι₁ : ℝ≥0∞) ^ (1/2:ℝ) * (Fintype.card ι₂ : ℝ≥0∞) ^ (1/2:ℝ) := by
  unfold tri
  gcongr <;> exact cnt_le_card _ _ _ _ _

/-- **Multilinear Kakeya for nearly axis-parallel cylinders** (with loss `512^m` on the box of
side `K^m`), by induction on scales. -/
theorem nearAxis (K : ℕ) (hK : 2 ≤ K) (m : ℕ) :
    ∀ {ι₀ ι₁ ι₂ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
      (b₀ s₀ : ι₀ → ℝ × ℝ) (b₁ s₁ : ι₁ → ℝ × ℝ) (b₂ s₂ : ι₂ → ℝ × ℝ),
      (∀ i, ‖s₀ i‖ ≤ 1 / K) → (∀ i, ‖s₁ i‖ ≤ 1 / K) → (∀ i, ‖s₂ i‖ ≤ 1 / K) →
      ∫⁻ p in cube 0 ((K : ℝ) ^ m), tri b₀ s₀ b₁ s₁ b₂ s₂ 1 p ≤
        512 ^ m * (Fintype.card ι₀ : ℝ≥0∞) ^ (1/2:ℝ) * (Fintype.card ι₁ : ℝ≥0∞) ^ (1/2:ℝ) *
          (Fintype.card ι₂ : ℝ≥0∞) ^ (1/2:ℝ) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  induction m with
  | zero =>
    intro ι₀ ι₁ ι₂ _ _ _ b₀ s₀ b₁ s₁ b₂ s₂ _ _ _
    calc ∫⁻ p in cube 0 ((K : ℝ) ^ 0), tri b₀ s₀ b₁ s₁ b₂ s₂ 1 p
        ≤ ∫⁻ p in cube 0 ((K : ℝ) ^ 0), (Fintype.card ι₀ : ℝ≥0∞) ^ (1/2:ℝ) *
            (Fintype.card ι₁ : ℝ≥0∞) ^ (1/2:ℝ) * (Fintype.card ι₂ : ℝ≥0∞) ^ (1/2:ℝ) :=
          lintegral_mono fun p => tri_mono_card _ _ _ _ _ _ _ p
      _ = _ := by
          rw [setLIntegral_const, volume_cube, pow_zero, ENNReal.ofReal_one, one_pow, mul_one,
            pow_zero, one_mul]
  | succ m ih =>
    intro ι₀ ι₁ ι₂ _ _ _ b₀ s₀ b₁ s₁ b₂ s₂ hs₀ hs₁ hs₂
    have hKν : (K : ℝ) * (1 / K) = 1 := by field_simp
    -- one step of the cube decomposition
    have step : ∫⁻ p in cube 0 ((K : ℝ) ^ (m + 1)), tri b₀ s₀ b₁ s₁ b₂ s₂ 1 p ≤
        ENNReal.ofReal (2 * (1 + K * (1 / K))) ^ 3 / ENNReal.ofReal K ^ 3 *
          ∫⁻ p in cube 0 ((K : ℝ) ^ (m + 1)),
            tri b₀ s₀ b₁ s₁ b₂ s₂ (1 + K + K * (1 / K)) p := by
      apply box_le_of_cube_le K (by omega) m
      intro k
      exact cube_est b₀ s₀ b₁ s₁ b₂ s₂ hK0 hs₀ hs₁ hs₂ _
    rw [hKν] at step
    -- rescale by `K`
    have hscale : ∫⁻ p in cube 0 ((K : ℝ) ^ (m + 1)), tri b₀ s₀ b₁ s₁ b₂ s₂ (1 + K + 1) p =
        ENNReal.ofReal K ^ 3 * ∫⁻ p in cube 0 ((K : ℝ) ^ m),
          tri (fun i => (K : ℝ)⁻¹ • b₀ i) s₀ (fun i => (K : ℝ)⁻¹ • b₁ i) s₁
            (fun i => (K : ℝ)⁻¹ • b₂ i) s₂ ((1 + K + 1) / K) p := by
      rw [pow_succ, mul_comm _ (K : ℝ), lintegral_cube_smul hK0 _ (measurable_tri _ _ _ _ _ _ _)]
      congr 1
      refine setLIntegral_congr_fun (measurableSet_cube _ _) fun p _ => ?_
      simp only [tri, cnt_smul hK0]
    have hR : (1 + (K : ℝ) + 1) / K ≤ 2 := by
      rw [div_le_iff₀ hK0]
      have : (2 : ℝ) ≤ K := by exact_mod_cast hK
      linarith
    -- cover by unit cylinders
    have hcov : ∫⁻ p in cube 0 ((K : ℝ) ^ m),
          tri (fun i => (K : ℝ)⁻¹ • b₀ i) s₀ (fun i => (K : ℝ)⁻¹ • b₁ i) s₁
            (fun i => (K : ℝ)⁻¹ • b₂ i) s₂ ((1 + K + 1) / K) p ≤
        ∫⁻ p in cube 0 ((K : ℝ) ^ m),
          tri (fun x : ι₀ × (Bool × Bool) => (K : ℝ)⁻¹ • b₀ x.1 + shift x.2) (fun x => s₀ x.1)
            (fun x : ι₁ × (Bool × Bool) => (K : ℝ)⁻¹ • b₁ x.1 + shift x.2) (fun x => s₁ x.1)
            (fun x : ι₂ × (Bool × Bool) => (K : ℝ)⁻¹ • b₂ x.1 + shift x.2) (fun x => s₂ x.1)
            1 p := by
      apply lintegral_mono
      intro p
      unfold tri
      gcongr
      · exact cnt_le_cnt_shift 0 (fun i => (K : ℝ)⁻¹ • b₀ i) s₀ hR p
      · exact cnt_le_cnt_shift 1 (fun i => (K : ℝ)⁻¹ • b₁ i) s₁ hR p
      · exact cnt_le_cnt_shift 2 (fun i => (K : ℝ)⁻¹ • b₂ i) s₂ hR p
    have hih := ih (fun x : ι₀ × (Bool × Bool) => (K : ℝ)⁻¹ • b₀ x.1 + shift x.2)
      (fun x => s₀ x.1) (fun x : ι₁ × (Bool × Bool) => (K : ℝ)⁻¹ • b₁ x.1 + shift x.2)
      (fun x => s₁ x.1) (fun x : ι₂ × (Bool × Bool) => (K : ℝ)⁻¹ • b₂ x.1 + shift x.2)
      (fun x => s₂ x.1) (fun x => hs₀ x.1) (fun x => hs₁ x.1) (fun x => hs₂ x.1)
    simp only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul] at hih
    have hK3 : ENNReal.ofReal K ^ 3 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hK0).ne'
    have hK3' : ENNReal.ofReal K ^ 3 ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    calc ∫⁻ p in cube 0 ((K : ℝ) ^ (m + 1)), tri b₀ s₀ b₁ s₁ b₂ s₂ 1 p
        ≤ ENNReal.ofReal (2 * (1 + 1)) ^ 3 / ENNReal.ofReal K ^ 3 *
            (ENNReal.ofReal K ^ 3 * (512 ^ m *
              ((Fintype.card ι₀ : ℝ≥0∞) * ((2 : ℕ) * (2 : ℕ))) ^ (1/2:ℝ) *
              ((Fintype.card ι₁ : ℝ≥0∞) * ((2 : ℕ) * (2 : ℕ))) ^ (1/2:ℝ) *
              ((Fintype.card ι₂ : ℝ≥0∞) * ((2 : ℕ) * (2 : ℕ))) ^ (1/2:ℝ))) := by
          refine step.trans ?_
          rw [hscale]
          gcongr
          exact hcov.trans hih
      _ = 512 ^ (m + 1) * (Fintype.card ι₀ : ℝ≥0∞) ^ (1/2:ℝ) *
            (Fintype.card ι₁ : ℝ≥0∞) ^ (1/2:ℝ) * (Fintype.card ι₂ : ℝ≥0∞) ^ (1/2:ℝ) := by
          rw [← mul_assoc, ENNReal.div_mul_cancel hK3 hK3']
          simp only [sqrt_mul_four]
          rw [show (2 : ℝ) * (1 + 1) = 4 by norm_num, pow_succ]
          rw [show ENNReal.ofReal 4 = 4 by norm_num]
          ring

end WangZahlLot.Obl.wz_extremal_lipschitz_grains.MK
