-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.TransversalKakeya.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NearAxisKakeya

/-!
# Trilinear Kakeya for transversal families of line neighbourhoods

Reduction of the trilinear estimate for three families of `δ`-neighbourhoods of lines (in the sup
norm of `Fin 3 → ℝ`), whose directions become nearly axis-parallel after an invertible linear map
`A`, to `nearAxis`: rescale by `1 / (2 Λ δ)` where `Λ` bounds `A`, change variables and choose the
scale `m` with `K^m > 1/δ`.  The loss is `δ^(-ε)` for any `ε > 0`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains.MK

lemma tr_add (j : Fin 3) (p q : Fin 3 → ℝ) : tr j (p + q) = tr j p + tr j q := by
  simp [tr]

lemma tr_sub (j : Fin 3) (p q : Fin 3 → ℝ) : tr j (p - q) = tr j p - tr j q := by
  simp [tr]

lemma tr_smul' (j : Fin 3) (a : ℝ) (p : Fin 3 → ℝ) : tr j (a • p) = a • tr j p := by
  simp [tr]

lemma norm_tr_le (j : Fin 3) (p : Fin 3 → ℝ) : ‖tr j p‖ ≤ ‖p‖ := by
  rw [tr, Prod.norm_def, max_le_iff]
  exact ⟨norm_le_pi_norm p _, norm_le_pi_norm p _⟩

lemma add_mem_cyl_iff (j : Fin 3) (b s : ℝ × ℝ) (r : ℝ) (q c : Fin 3 → ℝ) :
    q + c ∈ cyl j b s r ↔ q ∈ cyl j (b - tr j c + c j • s) s r := by
  simp only [cyl, mem_ofPred_eq]
  have : dist (tr j (q + c)) (b + (q + c) j • s) = dist (tr j q) (b - tr j c + c j • s + q j • s) := by
    rw [dist_eq_norm, dist_eq_norm, tr_add]
    congr 1
    simp only [Pi.add_apply, add_smul]
    abel
  rw [this]

lemma cnt_add {ι : Type*} [Fintype ι] (j : Fin 3) (b s : ι → ℝ × ℝ) (r : ℝ)
    (q c : Fin 3 → ℝ) :
    cnt j b s r (q + c) = cnt j (fun i => b i - tr j c + c j • s i) s r q := by
  unfold cnt
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : q ∈ cyl j (b i - tr j c + c j • s i) (s i) r
  · rw [indicator_of_mem ((add_mem_cyl_iff j _ _ _ q c).2 h), indicator_of_mem h]; rfl
  · rw [indicator_of_notMem (fun h' => h ((add_mem_cyl_iff j _ _ _ q c).1 h')),
      indicator_of_notMem h]

lemma add_mem_cube_iff (c : Fin 3 → ℝ) (L : ℝ) (q : Fin 3 → ℝ) :
    q + c ∈ cube c L ↔ q ∈ cube 0 L := by
  simp only [cube, mem_pi, mem_univ, true_implies, mem_Ico, Pi.add_apply, Pi.zero_apply,
    zero_add]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

lemma lintegral_cube_translate (c : Fin 3 → ℝ) (L : ℝ) {F : (Fin 3 → ℝ) → ℝ≥0∞} :
    ∫⁻ q in cube c L, F q = ∫⁻ q in cube 0 L, F (q + c) := by
  rw [← lintegral_indicator (measurableSet_cube _ _),
    ← lintegral_indicator (measurableSet_cube _ _),
    ← lintegral_add_right_eq_self (μ := (volume : Measure (Fin 3 → ℝ)))
      ((cube c L).indicator F) c]
  congr 1; ext q
  by_cases hq : q ∈ cube 0 L
  · rw [indicator_of_mem ((add_mem_cube_iff c L q).2 hq), indicator_of_mem hq]
  · rw [indicator_of_notMem (fun h => hq ((add_mem_cube_iff c L q).1 h)), indicator_of_notMem hq]

/-- `nearAxis` on a box with an arbitrary corner. -/
theorem nearAxis_corner (K : ℕ) (hK : 2 ≤ K) (m : ℕ) (c : Fin 3 → ℝ)
    {ι₀ ι₁ ι₂ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
    (b₀ s₀ : ι₀ → ℝ × ℝ) (b₁ s₁ : ι₁ → ℝ × ℝ) (b₂ s₂ : ι₂ → ℝ × ℝ)
    (hs₀ : ∀ i, ‖s₀ i‖ ≤ 1 / K) (hs₁ : ∀ i, ‖s₁ i‖ ≤ 1 / K) (hs₂ : ∀ i, ‖s₂ i‖ ≤ 1 / K) :
    ∫⁻ p in cube c ((K : ℝ) ^ m), tri b₀ s₀ b₁ s₁ b₂ s₂ 1 p ≤
      512 ^ m * (Fintype.card ι₀ : ℝ≥0∞) ^ (1/2:ℝ) * (Fintype.card ι₁ : ℝ≥0∞) ^ (1/2:ℝ) *
        (Fintype.card ι₂ : ℝ≥0∞) ^ (1/2:ℝ) := by
  rw [lintegral_cube_translate]
  have := nearAxis K hK m (fun i => b₀ i - tr 0 c + c 0 • s₀ i) s₀
    (fun i => b₁ i - tr 1 c + c 1 • s₁ i) s₁ (fun i => b₂ i - tr 2 c + c 2 • s₂ i) s₂ hs₀ hs₁ hs₂
  refine le_trans (le_of_eq ?_) this
  congr 1; ext q
  simp only [tri, cnt_add]

/-- Slope of a direction `w` relative to the axis `j`. -/
noncomputable def slope (j : Fin 3) (w : Fin 3 → ℝ) : ℝ × ℝ := (w j)⁻¹ • tr j w

lemma norm_slope_le {j : Fin 3} {w : Fin 3 → ℝ} {K : ℝ} (hK : 0 < K)
    (hw : ‖tr j w‖ * K ≤ |w j|) (hwj : w j ≠ 0) : ‖slope j w‖ ≤ 1 / K := by
  rw [slope, norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ (abs_pos.2 hwj)]
  rw [mul_one_div, le_div_iff₀ hK]
  exact hw

/-- A point within sup-distance `δ` of the line `x + ℝ v` is mapped by a linear map `L` into the
cylinder around the image line, of radius `2 Λ δ`, when `L v` has slope at most `1` relative to
axis `j`. -/
lemma mem_cyl_of_near (L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) {Λ : ℝ}
    (hL : ∀ q, ‖L q‖ ≤ Λ * ‖q‖) (j : Fin 3) {x v q : Fin 3 → ℝ} {t δ : ℝ}
    (hv : ‖tr j (L v)‖ ≤ |L v j|) (hvj : L v j ≠ 0) (hq : ‖q - (x + t • v)‖ < δ) :
    L q ∈ cyl j (tr j (L x) - L x j • slope j (L v)) (slope j (L v)) (2 * Λ * δ) := by
  set d := q - (x + t • v) with hd
  have hq' : q = x + t • v + d := by rw [hd]; abel
  have hs : ‖slope j (L v)‖ ≤ 1 := by
    have := norm_slope_le (K := 1) one_pos (by simpa using hv) hvj
    simpa using this
  have hΛ : 0 ≤ Λ := by
    by_contra hneg
    push Not at hneg
    have h1 := hL (Pi.single 0 1)
    have : 0 < ‖(Pi.single 0 1 : Fin 3 → ℝ)‖ := by simp
    nlinarith [norm_nonneg (L (Pi.single 0 1))]
  have htr : tr j (L v) = L v j • slope j (L v) := by
    rw [slope, smul_smul, mul_inv_cancel₀ hvj, one_smul]
  show dist (tr j (L q)) (tr j (L x) - L x j • slope j (L v) + L q j • slope j (L v)) ≤ 2 * Λ * δ
  have key : tr j (L q) - (tr j (L x) - L x j • slope j (L v) + L q j • slope j (L v)) =
      tr j (L d) - L d j • slope j (L v) := by
    rw [hq', map_add, map_add, map_smul, tr_add, tr_add, tr_smul', htr]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, smul_smul]
    abel
  rw [dist_eq_norm, key]
  calc ‖tr j (L d) - L d j • slope j (L v)‖ ≤ ‖tr j (L d)‖ + ‖L d j • slope j (L v)‖ :=
        norm_sub_le _ _
    _ ≤ ‖L d‖ + ‖L d‖ * 1 := by
        refine add_le_add (norm_tr_le j _) ?_
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm _ _) hs (norm_nonneg _) (norm_nonneg _)
    _ = 2 * ‖L d‖ := by ring
    _ ≤ 2 * (Λ * δ) := by
        have := hL d
        have h2 : Λ * ‖d‖ ≤ Λ * δ := mul_le_mul_of_nonneg_left hq.le hΛ
        linarith
    _ = 2 * Λ * δ := by ring

/-- Points within sup-distance `δ` of the line `x + ℝ v`. -/
def nearLine (δ : ℝ) (x v : Fin 3 → ℝ) : Set (Fin 3 → ℝ) := {q | ∃ t : ℝ, ‖q - (x + t • v)‖ < δ}

lemma isOpen_nearLine (δ : ℝ) (x v : Fin 3 → ℝ) : IsOpen (nearLine δ x v) := by
  have : nearLine δ x v = ⋃ t : ℝ, Metric.ball (x + t • v) δ := by
    ext q; simp [nearLine, dist_eq_norm]
  rw [this]
  exact isOpen_iUnion fun _ => Metric.isOpen_ball

/-- Multiplicity of a family of line neighbourhoods. -/
noncomputable def ncount {ι : Type*} [Fintype ι] (δ : ℝ) (x v : ι → Fin 3 → ℝ)
    (q : Fin 3 → ℝ) : ℝ≥0∞ :=
  ∑ i, (nearLine δ (x i) (v i)).indicator 1 q

lemma measurable_ncount {ι : Type*} [Fintype ι] (δ : ℝ) (x v : ι → Fin 3 → ℝ) :
    Measurable (ncount δ x v) := by
  unfold ncount
  exact Finset.measurable_sum _ fun i _ =>
    measurable_one.indicator (isOpen_nearLine _ _ _).measurableSet

lemma slope_smul (j : Fin 3) {a : ℝ} (ha : a ≠ 0) (w : Fin 3 → ℝ) :
    slope j (a • w) = slope j w := by
  rw [slope, slope, tr_smul', Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ ha, mul_one]

lemma ncount_le_cnt {ι : Type*} [Fintype ι] (L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) {δ : ℝ}
    (hL : ∀ q, ‖L q‖ ≤ (1 / (2 * δ)) * ‖q‖) (hδ : 0 < δ) (j : Fin 3) (x v : ι → Fin 3 → ℝ)
    (hv : ∀ i, ‖tr j (L (v i))‖ ≤ |L (v i) j|) (hvj : ∀ i, L (v i) j ≠ 0) (q : Fin 3 → ℝ) :
    ncount δ x v q ≤ cnt j (fun i => tr j (L (x i)) - L (x i) j • slope j (L (v i)))
      (fun i => slope j (L (v i))) 1 (L q) := by
  unfold ncount cnt
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : q ∈ nearLine δ (x i) (v i)
  · obtain ⟨t, ht⟩ := h
    have hmem := mem_cyl_of_near L hL j (hv i) (hvj i) ht
    have h1 : 2 * (1 / (2 * δ)) * δ = 1 := by field_simp
    rw [h1] at hmem
    have hq : q ∈ nearLine δ (x i) (v i) := ⟨t, ht⟩
    rw [indicator_of_mem hq, indicator_of_mem hmem]
    simp
  · rw [indicator_of_notMem h]; exact zero_le

/-- The trilinear estimate for three families of line neighbourhoods whose directions become
nearly axis-parallel after the linear map `A`. -/
theorem capTriple (ε : ℝ) (hε : 0 < ε) : ∃ (K : ℕ) (C : ℝ), 2 ≤ K ∧ 0 < C ∧
    ∀ (A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (Λ : ℝ), 0 < Λ → (∀ q, ‖A q‖ ≤ Λ * ‖q‖) →
      A.det ≠ 0 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ {ι₀ ι₁ ι₂ : Type} [Fintype ι₀] [Fintype ι₁] [Fintype ι₂]
        (x₀ v₀ : ι₀ → Fin 3 → ℝ) (x₁ v₁ : ι₁ → Fin 3 → ℝ) (x₂ v₂ : ι₂ → Fin 3 → ℝ),
        (∀ i, ‖tr 0 (A (v₀ i))‖ * K ≤ |A (v₀ i) 0|) → (∀ i, A (v₀ i) 0 ≠ 0) →
        (∀ i, ‖tr 1 (A (v₁ i))‖ * K ≤ |A (v₁ i) 1|) → (∀ i, A (v₁ i) 1 ≠ 0) →
        (∀ i, ‖tr 2 (A (v₂ i))‖ * K ≤ |A (v₂ i) 2|) → (∀ i, A (v₂ i) 2 ≠ 0) →
        ∫⁻ q in Metric.closedBall 0 1, ncount δ x₀ v₀ q ^ (1/2:ℝ) * ncount δ x₁ v₁ q ^ (1/2:ℝ) *
            ncount δ x₂ v₂ q ^ (1/2:ℝ)
          ≤ ENNReal.ofReal (C * Λ ^ 3 * |A.det|⁻¹ * δ ^ (3 - ε)) *
            (Fintype.card ι₀ : ℝ≥0∞) ^ (1/2:ℝ) * (Fintype.card ι₁ : ℝ≥0∞) ^ (1/2:ℝ) *
              (Fintype.card ι₂ : ℝ≥0∞) ^ (1/2:ℝ) := by
  obtain ⟨N, hN1, hNε⟩ : ∃ N : ℕ, 1 ≤ N ∧ (1 : ℝ) / N ≤ ε := by
    refine ⟨⌈1 / ε⌉₊ + 1, by omega, ?_⟩
    have h1 := Nat.le_ceil (1 / ε)
    have h2 : 1 ≤ ε * ⌈1 / ε⌉₊ := by
      have := mul_le_mul_of_nonneg_left h1 hε.le
      rwa [mul_one_div_cancel hε.ne'] at this
    rw [div_le_iff₀ (by positivity)]
    push_cast
    linarith
  refine ⟨512 ^ N, 8 * ((512 ^ N : ℕ) : ℝ) ^ ε, ?_, by positivity, ?_⟩
  · calc 2 ≤ 512 := by norm_num
      _ ≤ 512 ^ N := Nat.le_self_pow (by omega) _
  intro A Λ hΛ hA hdet δ hδ hδ1 ι₀ ι₁ ι₂ _ _ _ x₀ v₀ x₁ v₁ x₂ v₂ hs₀ hn₀ hs₁ hn₁ hs₂ hn₂
  set K : ℕ := 512 ^ N with hKdef
  have hK2 : 2 ≤ K := by
    calc 2 ≤ 512 := by norm_num
      _ ≤ 512 ^ N := Nat.le_self_pow (by omega) _
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  -- the rescaled map
  set lam : ℝ := 1 / (2 * Λ * δ) with hlam
  have hlam0 : 0 < lam := by positivity
  set L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) := lam • A with hLdef
  have hL : ∀ q, ‖L q‖ ≤ (1 / (2 * δ)) * ‖q‖ := by
    intro q
    rw [hLdef, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
    calc lam * ‖A q‖ ≤ lam * (Λ * ‖q‖) := mul_le_mul_of_nonneg_left (hA q) hlam0.le
      _ = (1 / (2 * δ)) * ‖q‖ := by rw [hlam]; field_simp
  have hsl : ∀ (j : Fin 3) (w : Fin 3 → ℝ), ‖tr j (A w)‖ * K ≤ |A w j| →
      ‖tr j (L w)‖ ≤ |L w j| := by
    intro j w h
    rw [hLdef, ContinuousLinearMap.smul_apply, tr_smul', norm_smul, Pi.smul_apply, smul_eq_mul,
      abs_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    nlinarith [norm_nonneg (tr j (A w))]
  have hnz : ∀ (j : Fin 3) (w : Fin 3 → ℝ), A w j ≠ 0 → L w j ≠ 0 := by
    intro j w h
    rw [hLdef, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hlam0.ne' h
  have hslopeK : ∀ (j : Fin 3) (w : Fin 3 → ℝ), ‖tr j (A w)‖ * K ≤ |A w j| → A w j ≠ 0 →
      ‖slope j (L w)‖ ≤ 1 / K := by
    intro j w h hj
    rw [hLdef, ContinuousLinearMap.smul_apply, slope_smul j hlam0.ne']
    exact norm_slope_le hK0 h hj
  -- the scale `m`
  classical
  have hex : ∃ m : ℕ, 1 / δ < (K : ℝ) ^ m :=
    pow_unbounded_of_one_lt _ (by exact_mod_cast (by omega : 1 < K))
  set m := Nat.find hex with hmdef
  have hm : 1 / δ < (K : ℝ) ^ m := Nat.find_spec hex
  have hδinv : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hm1 : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    rw [h0, pow_zero] at hm
    linarith
  have hm2 : (K : ℝ) ^ (m - 1) ≤ 1 / δ := by
    have := Nat.find_min hex (show m - 1 < m by omega)
    exact le_of_not_gt this
  have hKm : (K : ℝ) ^ m ≤ K / δ := by
    calc (K : ℝ) ^ m = K * (K : ℝ) ^ (m - 1) := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ K * (1 / δ) := mul_le_mul_of_nonneg_left hm2 hK0.le
      _ = K / δ := by ring
  -- the box
  set c : Fin 3 → ℝ := fun _ => -(1 / (2 * δ)) with hc
  have hbox : ∀ q ∈ Metric.closedBall (0 : Fin 3 → ℝ) 1, L q ∈ cube c ((K : ℝ) ^ m) := by
    intro q hq k _
    have h1 : ‖L q‖ ≤ 1 / (2 * δ) := by
      rw [mem_closedBall_zero_iff] at hq
      calc ‖L q‖ ≤ 1 / (2 * δ) * ‖q‖ := hL q
        _ ≤ 1 / (2 * δ) * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
        _ = _ := mul_one _
    have h2 := (norm_le_pi_norm (L q) k).trans h1
    rw [Real.norm_eq_abs, abs_le] at h2
    simp only [mem_Ico, hc]
    have h3 : 1 / (2 * δ) + 1 / (2 * δ) = 1 / δ := by field_simp; ring
    constructor <;> linarith
  -- pointwise domination
  have hpt : ∀ q ∈ Metric.closedBall (0 : Fin 3 → ℝ) 1,
      ncount δ x₀ v₀ q ^ (1/2:ℝ) * ncount δ x₁ v₁ q ^ (1/2:ℝ) * ncount δ x₂ v₂ q ^ (1/2:ℝ) ≤
        (cube c ((K : ℝ) ^ m)).indicator
          (tri (fun i => tr 0 (L (x₀ i)) - L (x₀ i) 0 • slope 0 (L (v₀ i)))
            (fun i => slope 0 (L (v₀ i)))
            (fun i => tr 1 (L (x₁ i)) - L (x₁ i) 1 • slope 1 (L (v₁ i)))
            (fun i => slope 1 (L (v₁ i)))
            (fun i => tr 2 (L (x₂ i)) - L (x₂ i) 2 • slope 2 (L (v₂ i)))
            (fun i => slope 2 (L (v₂ i))) 1) (L q) := by
    intro q hq
    rw [indicator_of_mem (hbox q hq)]
    unfold tri
    have h0 := ncount_le_cnt L hL hδ 0 x₀ v₀ (fun i => hsl 0 _ (hs₀ i))
      (fun i => hnz 0 _ (hn₀ i)) q
    have h1 := ncount_le_cnt L hL hδ 1 x₁ v₁ (fun i => hsl 1 _ (hs₁ i))
      (fun i => hnz 1 _ (hn₁ i)) q
    have h2 := ncount_le_cnt L hL hδ 2 x₂ v₂ (fun i => hsl 2 _ (hs₂ i))
      (fun i => hnz 2 _ (hn₂ i)) q
    gcongr
  -- change of variables
  have hdetL : L.det = lam ^ 3 * A.det := by
    rw [hLdef]
    show LinearMap.det (((lam • A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))) :
        (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = lam ^ 3 * LinearMap.det (A : (Fin 3 → ℝ) →ₗ[ℝ] _)
    rw [ContinuousLinearMap.coe_smul, LinearMap.det_smul, Module.finrank_fin_fun]
  have hdetL0 : L.det ≠ 0 := by rw [hdetL]; exact mul_ne_zero (pow_ne_zero _ hlam0.ne') hdet
  set G := (cube c ((K : ℝ) ^ m)).indicator
          (tri (fun i => tr 0 (L (x₀ i)) - L (x₀ i) 0 • slope 0 (L (v₀ i)))
            (fun i => slope 0 (L (v₀ i)))
            (fun i => tr 1 (L (x₁ i)) - L (x₁ i) 1 • slope 1 (L (v₁ i)))
            (fun i => slope 1 (L (v₁ i)))
            (fun i => tr 2 (L (x₂ i)) - L (x₂ i) 2 • slope 2 (L (v₂ i)))
            (fun i => slope 2 (L (v₂ i))) 1) with hG
  have hGm : Measurable G := (measurable_tri _ _ _ _ _ _ _).indicator (measurableSet_cube _ _)
  have hcv : ∫⁻ q, G (L q) = ENNReal.ofReal |L.det⁻¹| * ∫⁻ q, G q := by
    have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin 3 → ℝ))
      (f := (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))) hdetL0
    have h1 := lintegral_map (μ := (volume : Measure (Fin 3 → ℝ))) hGm L.continuous.measurable
    rw [show ((L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) : (Fin 3 → ℝ) → (Fin 3 → ℝ)) = L from rfl]
      at hmap
    rw [hmap, lintegral_smul_measure, smul_eq_mul] at h1
    exact h1.symm
  have hna := nearAxis_corner K hK2 m c
    (fun i => tr 0 (L (x₀ i)) - L (x₀ i) 0 • slope 0 (L (v₀ i))) (fun i => slope 0 (L (v₀ i)))
    (fun i => tr 1 (L (x₁ i)) - L (x₁ i) 1 • slope 1 (L (v₁ i))) (fun i => slope 1 (L (v₁ i)))
    (fun i => tr 2 (L (x₂ i)) - L (x₂ i) 2 • slope 2 (L (v₂ i))) (fun i => slope 2 (L (v₂ i)))
    (fun i => hslopeK 0 _ (hs₀ i) (hn₀ i)) (fun i => hslopeK 1 _ (hs₁ i) (hn₁ i))
    (fun i => hslopeK 2 _ (hs₂ i) (hn₂ i))
  -- arithmetic
  have harith : |L.det⁻¹| * (512 : ℝ) ^ m ≤
      8 * ((512 ^ N : ℕ) : ℝ) ^ ε * Λ ^ 3 * |A.det|⁻¹ * δ ^ (3 - ε) := by
    have hdl : |L.det⁻¹| = 8 * Λ ^ 3 * δ ^ 3 * |A.det|⁻¹ := by
      rw [hdetL, abs_inv, abs_mul, abs_pow, abs_of_pos hlam0, hlam]
      field_simp
      ring
    have h512 : (512 : ℝ) ^ m = ((K : ℝ) ^ m) ^ ((1 : ℝ) / N) := by
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      rw [hKdef]
      push_cast
      rw [← pow_mul, show ((512 : ℝ) ^ (N * m)) = (512 : ℝ) ^ (((N * m : ℕ)) : ℝ) from
        (Real.rpow_natCast _ _).symm, ← Real.rpow_mul (by norm_num),
        show (((N * m : ℕ)) : ℝ) * (1 / N) = (m : ℝ) by push_cast; field_simp,
        Real.rpow_natCast]
    have hKδ : 1 ≤ (K : ℝ) / δ := by
      rw [le_div_iff₀ hδ]; linarith
    have h512' : (512 : ℝ) ^ m ≤ (K : ℝ) ^ ε * δ ^ (-ε) := by
      rw [h512]
      calc ((K : ℝ) ^ m) ^ ((1 : ℝ) / N) ≤ ((K : ℝ) / δ) ^ ((1 : ℝ) / N) :=
            Real.rpow_le_rpow (by positivity) hKm (by positivity)
        _ ≤ ((K : ℝ) / δ) ^ ε := Real.rpow_le_rpow_of_exponent_le hKδ hNε
        _ = (K : ℝ) ^ ε * δ ^ (-ε) := by
            rw [Real.div_rpow hK0.le hδ.le, Real.rpow_neg hδ.le, div_eq_mul_inv]
    have hδ3 : δ ^ 3 * δ ^ (-ε) = δ ^ (3 - ε) := by
      rw [show (3 : ℝ) - ε = (3 : ℕ) + (-ε) by push_cast; ring, Real.rpow_add hδ,
        Real.rpow_natCast]
    rw [hdl]
    calc 8 * Λ ^ 3 * δ ^ 3 * |A.det|⁻¹ * (512 : ℝ) ^ m
        ≤ 8 * Λ ^ 3 * δ ^ 3 * |A.det|⁻¹ * ((K : ℝ) ^ ε * δ ^ (-ε)) :=
          mul_le_mul_of_nonneg_left h512' (by positivity)
      _ = 8 * (K : ℝ) ^ ε * Λ ^ 3 * |A.det|⁻¹ * (δ ^ 3 * δ ^ (-ε)) := by ring
      _ = _ := by rw [hδ3, hKdef]
  calc ∫⁻ q in Metric.closedBall 0 1, ncount δ x₀ v₀ q ^ (1/2:ℝ) * ncount δ x₁ v₁ q ^ (1/2:ℝ) *
          ncount δ x₂ v₂ q ^ (1/2:ℝ)
      ≤ ∫⁻ q in Metric.closedBall 0 1, G (L q) :=
        setLIntegral_mono (hGm.comp L.continuous.measurable) hpt
    _ ≤ ∫⁻ q, G (L q) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal |L.det⁻¹| * ∫⁻ q in cube c ((K : ℝ) ^ m),
          tri (fun i => tr 0 (L (x₀ i)) - L (x₀ i) 0 • slope 0 (L (v₀ i)))
            (fun i => slope 0 (L (v₀ i)))
            (fun i => tr 1 (L (x₁ i)) - L (x₁ i) 1 • slope 1 (L (v₁ i)))
            (fun i => slope 1 (L (v₁ i)))
            (fun i => tr 2 (L (x₂ i)) - L (x₂ i) 2 • slope 2 (L (v₂ i)))
            (fun i => slope 2 (L (v₂ i))) 1 q := by
        rw [hcv, hG, lintegral_indicator (measurableSet_cube _ _)]
    _ ≤ ENNReal.ofReal |L.det⁻¹| * (512 ^ m * (Fintype.card ι₀ : ℝ≥0∞) ^ (1/2:ℝ) *
          (Fintype.card ι₁ : ℝ≥0∞) ^ (1/2:ℝ) * (Fintype.card ι₂ : ℝ≥0∞) ^ (1/2:ℝ)) := by
        gcongr
    _ = ENNReal.ofReal (|L.det⁻¹| * (512 : ℝ) ^ m) * (Fintype.card ι₀ : ℝ≥0∞) ^ (1/2:ℝ) *
          (Fintype.card ι₁ : ℝ≥0∞) ^ (1/2:ℝ) * (Fintype.card ι₂ : ℝ≥0∞) ^ (1/2:ℝ) := by
        rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (by norm_num)]
        simp only [ENNReal.ofReal_ofNat]
        ring
    _ ≤ _ := by
        gcongr

end WangZahlLot.Obl.wz_extremal_lipschitz_grains.MK
