import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphRows
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.FiniteScaleGrid

/-!
# Numerical tools for the velocity-graph stage

Polynomial form of the Kakeya contradiction hypothesis, subpower comparison, and covering of
windows and coarse cubes by frozen bins and cells.
-/

set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- Polynomial form of the Kakeya contradiction hypothesis of `graph_world`. -/
lemma hcontr_of_poly {S₀ P Hb Hτ β p : ℝ} (hS₀ : 0 ≤ S₀) (hP : 0 ≤ P) (hHb : 0 ≤ Hb)
    (hHτ : 0 ≤ Hτ) (hβp : 0 < β * p)
    (h : S₀ * P ^ 2 * Hb ^ 3 * Hτ ^ 3 ≤ β * p / 8) :
    S₀ ^ ((1 : ℝ) / (((3 : ℕ) : ℝ) - 1)) *
        (P * Hb ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1)) / (β * p) ^ ((1 : ℝ) / (((3 : ℕ) : ℝ) - 1)) *
          Hτ ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1))) ≤
      (1 / 2) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1)) := by
  have e1 : (1 : ℝ) / (((3 : ℕ) : ℝ) - 1) = 1 / 2 := by norm_num
  have e3 : ((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1) = 3 / 2 := by norm_num
  rw [e1, e3]
  have k1 : ∀ a : ℝ, 0 ≤ a → (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    intro a ha
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  have k3 : ∀ a : ℝ, 0 ≤ a → (a ^ (3 / 2 : ℝ)) ^ 2 = a ^ 3 := by
    intro a ha
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  have hβp' : 0 ≤ β * p := hβp.le
  have hx0 : 0 ≤ S₀ ^ (1 / 2 : ℝ) * (P * Hb ^ (3 / 2 : ℝ) / (β * p) ^ (1 / 2 : ℝ) *
      Hτ ^ (3 / 2 : ℝ)) := by positivity
  have hy0 : 0 ≤ (1 / 2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
  rw [← pow_le_pow_iff_left₀ hx0 hy0 two_ne_zero, mul_pow, mul_pow, div_pow, mul_pow,
    k1 S₀ hS₀, k1 (β * p) hβp', k3 Hb hHb, k3 Hτ hHτ, k3 (1 / 2) (by norm_num)]
  have : S₀ * (P ^ 2 * Hb ^ 3 / (β * p) * Hτ ^ 3) = (S₀ * P ^ 2 * Hb ^ 3 * Hτ ^ 3) / (β * p) := by
    field_simp
  rw [this, div_le_iff₀ hβp]
  calc S₀ * P ^ 2 * Hb ^ 3 * Hτ ^ 3 ≤ β * p / 8 := h
    _ = (1 / 2) ^ 3 * (β * p) := by ring

/-- A constant times a power of a subpower sequence is eventually below any fixed power of `N`. -/
lemma eventually_const_mul_pow_le {N U : ℕ → ℝ} (hNt : Tendsto N atTop atTop)
    (hN1 : ∀ k, 1 ≤ N k) (hU1 : ∀ k, 1 ≤ U k)
    (hU : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, U k ≤ N k ^ ε) (C : ℝ) (p : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k in atTop, C * U k ^ p ≤ N k ^ a := by
  have hC : ∀ᶠ k in atTop, max C 1 ≤ N k ^ (a / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < a / 2)).comp hNt).eventually_ge_atTop _
  have hp1 : (0 : ℝ) < 2 * ((p : ℝ) + 1) := by positivity
  filter_upwards [hC, hU (a / (2 * ((p : ℝ) + 1))) (by positivity)] with k hk hUk
  have hNk : 0 < N k := lt_of_lt_of_le one_pos (hN1 k)
  have hU0 : 0 ≤ U k := le_trans zero_le_one (hU1 k)
  have h1 : U k ^ p ≤ N k ^ (a / 2) := by
    calc U k ^ p ≤ (N k ^ (a / (2 * ((p : ℝ) + 1)))) ^ p := pow_le_pow_left₀ hU0 hUk p
      _ = N k ^ (a / (2 * ((p : ℝ) + 1)) * p) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNk.le]
      _ ≤ N k ^ (a / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le (hN1 k)
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hp1 (by norm_num)]
          nlinarith
  calc C * U k ^ p ≤ max C 1 * U k ^ p :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hU0 _)
    _ ≤ N k ^ (a / 2) * N k ^ (a / 2) :=
        mul_le_mul hk h1 (pow_nonneg hU0 _) (by positivity)
    _ = N k ^ a := by rw [← Real.rpow_add hNk]; ring_nf

/-- An interval of length `ℓ` meets at most `ℓ / W + 2` bins of width `W`. -/
lemma measure_Ico_le_bins (π : Measure ℝ) {W cap a ℓ : ℝ} (hW : 0 < W) (hℓ : 0 ≤ ℓ)
    (hcap : ∀ c : ℤ, π {v : ℝ | ⌊v / W⌋ = c} ≤ ENNReal.ofReal cap) (hcap0 : 0 ≤ cap) :
    π (Set.Ico a (a + ℓ)) ≤ ENNReal.ofReal ((ℓ / W + 2) * cap) := by
  classical
  set I : Finset ℤ := Finset.Icc ⌊a / W⌋ ⌊(a + ℓ) / W⌋ with hI
  have hsub : Set.Ico a (a + ℓ) ⊆ ⋃ c ∈ I, {v : ℝ | ⌊v / W⌋ = c} := by
    intro v hv
    refine Set.mem_biUnion (x := ⌊v / W⌋) ?_ rfl
    rw [Finset.mem_coe, hI, Finset.mem_Icc]
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hv.1 hW.le),
      Int.floor_mono (div_le_div_of_nonneg_right hv.2.le hW.le)⟩
  have hcard : (I.card : ℝ) ≤ ℓ / W + 2 := by
    have := card_Icc_floor_le (yh := a + ℓ / 2) (e := ℓ / 2) hW (by positivity)
    have e1 : a + ℓ / 2 - ℓ / 2 = a := by ring
    have e2 : a + ℓ / 2 + ℓ / 2 = a + ℓ := by ring
    rw [e1, e2] at this
    have e3 : 2 * (ℓ / 2) / W = ℓ / W := by ring
    rw [hI]; linarith
  calc π (Set.Ico a (a + ℓ)) ≤ π (⋃ c ∈ I, {v : ℝ | ⌊v / W⌋ = c}) := measure_mono hsub
    _ ≤ ∑ c ∈ I, π {v : ℝ | ⌊v / W⌋ = c} := measure_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ I, ENNReal.ofReal cap := Finset.sum_le_sum fun c _ => hcap c
    _ = ENNReal.ofReal (I.card * cap) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((ℓ / W + 2) * cap) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hcap0)

/-- A velocity window of half-width `δ` inside a set `F` meets at most `2 δ / W + 2` velocity
bins of width `W`. -/
lemma measure_window_le (μ : Measure Inc) (F : Set Inc) {W δ capW v₀ : ℝ} (hW : 0 < W)
    (hδ : 0 ≤ δ) (hcap : ∀ c : ℤ, μ (F ∩ {p | ⌊p.1.2 1 / W⌋ = c}) ≤ ENNReal.ofReal capW)
    (hcap0 : 0 ≤ capW) :
    μ {p | p ∈ F ∧ |p.1.2 1 - v₀| < δ} ≤ ENNReal.ofReal ((2 * δ / W + 2) * capW) := by
  classical
  set I : Finset ℤ := Finset.Icc ⌊(v₀ - δ) / W⌋ ⌊(v₀ + δ) / W⌋ with hI
  have hsub : {p | p ∈ F ∧ |p.1.2 1 - v₀| < δ} ⊆ ⋃ c ∈ I, (F ∩ {p | ⌊p.1.2 1 / W⌋ = c}) := by
    intro p hp
    refine Set.mem_biUnion (x := ⌊p.1.2 1 / W⌋) ?_ ⟨hp.1, rfl⟩
    rw [Finset.mem_coe, hI]
    exact floor_mem_Icc_of_close hW hp.2.le
  have hcard : (I.card : ℝ) ≤ 2 * δ / W + 2 := card_Icc_floor_le hW hδ
  calc μ {p | p ∈ F ∧ |p.1.2 1 - v₀| < δ} ≤ μ (⋃ c ∈ I, (F ∩ {p | ⌊p.1.2 1 / W⌋ = c})) :=
        measure_mono hsub
    _ ≤ ∑ c ∈ I, μ (F ∩ {p | ⌊p.1.2 1 / W⌋ = c}) := measure_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ I, ENNReal.ofReal capW := Finset.sum_le_sum fun c _ => hcap c
    _ = ENNReal.ofReal (I.card * capW) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((2 * δ / W + 2) * capW) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hcap0)

/-- A cube of side `w ≤ w₁` meets at most `27` cubes of side `w₁`. -/
lemma measure_cellSet_le_of_coarser (μ : Measure Inc) {w w₁ cap : ℝ} (hw : 0 < w) (hw₁ : 0 < w₁)
    (hww : w ≤ w₁) (hcap : ∀ q, μ (physOf ⁻¹' cellSet w₁ q) ≤ ENNReal.ofReal cap)
    (hcap0 : 0 ≤ cap) (Q : Fin 3 → ℤ) :
    μ (physOf ⁻¹' cellSet w Q) ≤ ENNReal.ofReal (27 * cap) := by
  classical
  set I : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun e => Finset.Icc
    ⌊(((Q e : ℝ) + 1 / 2) * w - w / 2) / w₁⌋ ⌊(((Q e : ℝ) + 1 / 2) * w + w / 2) / w₁⌋) with hI
  have hsub : physOf ⁻¹' cellSet w Q ⊆ ⋃ q ∈ I, physOf ⁻¹' cellSet w₁ q := by
    intro p hp
    refine Set.mem_biUnion (x := cellIdx w₁ (physOf p)) ?_ rfl
    rw [Finset.mem_coe, hI, Fintype.mem_piFinset]
    intro e
    have h := (mem_cellSet_iff hw).mp hp e
    apply floor_mem_Icc_of_close hw₁
    rw [abs_le]; constructor <;> nlinarith [h.1, h.2]
  have hcard : (I.card : ℝ) ≤ 27 := by
    rw [hI, Fintype.card_piFinset]
    push_cast
    rw [Fin.prod_univ_three]
    have h : ∀ e : Fin 3, ((Finset.Icc ⌊(((Q e : ℝ) + 1 / 2) * w - w / 2) / w₁⌋
        ⌊(((Q e : ℝ) + 1 / 2) * w + w / 2) / w₁⌋).card : ℝ) ≤ 3 := by
      intro e
      have := card_Icc_floor_le (yh := ((Q e : ℝ) + 1 / 2) * w) hw₁ (by positivity : 0 ≤ w / 2)
      have e2 : 2 * (w / 2) / w₁ ≤ 1 := by rw [div_le_one hw₁]; linarith
      linarith
    calc _ ≤ (3 : ℝ) * 3 * 3 := by
          apply mul_le_mul (mul_le_mul (h 0) (h 1) (Nat.cast_nonneg _) (by norm_num)) (h 2)
            (Nat.cast_nonneg _) (by norm_num)
      _ = 27 := by norm_num
  calc μ (physOf ⁻¹' cellSet w Q) ≤ μ (⋃ q ∈ I, physOf ⁻¹' cellSet w₁ q) := measure_mono hsub
    _ ≤ ∑ q ∈ I, μ (physOf ⁻¹' cellSet w₁ q) := measure_biUnion_finset_le _ _
    _ ≤ ∑ q ∈ I, ENNReal.ofReal cap := Finset.sum_le_sum fun q _ => hcap q
    _ = ENNReal.ofReal (I.card * cap) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (27 * cap) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hcap0)

/-- Consecutive palette bins of width `w'` sum to at most the palette mass of their union, an
interval of length `(2 m + 1) w'`. -/
lemma sum_bins_le_Ico (π : Measure ℝ) {w' : ℝ} (hw' : 0 < w') (c : ℤ) (m : ℕ) :
    ∑ c' ∈ Finset.Icc (c - m) (c + m), π {v : ℝ | ⌊v / w'⌋ = c'} ≤
      π (Set.Ico (((c : ℝ) - m) * w') (((c : ℝ) - m) * w' + (2 * m + 1) * w')) := by
  classical
  have hm : ∀ c : ℤ, MeasurableSet {v : ℝ | ⌊v / w'⌋ = c} := fun c =>
    (measurable_id.div_const w').floor (measurableSet_singleton c)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc (c - m) (c + m)))
      (fun c : ℤ => {v : ℝ | ⌊v / w'⌋ = c}) := by
    intro a _ a' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro v h1 h2
    exact hne (h1.symm.trans h2)
  rw [← measure_biUnion_finset hdisj (fun c _ => hm c)]
  apply measure_mono
  intro v hv
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_Icc, exists_prop] at hv
  obtain ⟨c', ⟨h1, h2⟩, hc'⟩ := hv
  have ha := Int.floor_le (v / w'); have hb := Int.lt_floor_add_one (v / w')
  rw [hc', le_div_iff₀ hw'] at ha
  rw [hc', div_lt_iff₀ hw'] at hb
  have h1' : (c : ℝ) - m ≤ c' := by exact_mod_cast h1
  have h2' : (c' : ℝ) ≤ c + m := by exact_mod_cast h2
  constructor <;> nlinarith

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
