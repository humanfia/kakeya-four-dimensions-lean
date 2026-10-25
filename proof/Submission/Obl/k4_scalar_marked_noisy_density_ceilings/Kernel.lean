import Mathlib

/-!
# Kernel for `k4_scalar_marked_noisy_density_ceilings`

Adapted from: here:o062 (session x0215's smoothing kernel, branch x0215,
`Submission/Lib/K4ScalarMeshSmoothing.lean`), restated in this obligation's namespace, with
the hidden bin width only required to be at least `σ`.
-/

namespace Submission.Obl.k4_scalar_marked_noisy_density_ceilings

open MeasureTheory Set

/-- The affine base trace `b₀ + t b₁` of a coefficient vector. -/
def yTrace (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 0 + t * b 1

/-- The quadratic hidden trace `b₂ + t b₃ + t² b₄` of a coefficient vector. -/
def xTrace (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 2 + t * b 3 + t ^ 2 * b 4

/-- The closed coefficient box `[β, β + σ]⁵`. -/
def box (β : Fin 5 → ℝ) (σ : ℝ) : Set (Fin 5 → ℝ) := Set.pi univ (fun i => Icc (β i) (β i + σ))

theorem measurable_yTrace : Measurable (fun q : (Fin 5 → ℝ) × ℝ => yTrace q.1 q.2) := by
  unfold yTrace; fun_prop

theorem measurable_xTrace : Measurable (fun q : (Fin 5 → ℝ) × ℝ => xTrace q.1 q.2) := by
  unfold xTrace; fun_prop

theorem volume_pi_Icc_add (n : ℕ) (β : Fin n → ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    volume (Set.pi univ (fun j => Icc (β j) (β j + σ))) = ENNReal.ofReal (σ ^ n) := by
  rw [volume_pi, Measure.pi_pi]
  simp only [Real.volume_Icc, add_sub_cancel_left, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.ofReal_pow hσ]

theorem volume_box (β : Fin 5 → ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    volume (box β σ) = ENNReal.ofReal (σ ^ 5) :=
  volume_pi_Icc_add 5 β hσ

theorem measurePreserving_split :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) 0)
      (volume : Measure (Fin 5 → ℝ))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 4 → ℝ))) := by
  have := measurePreserving_piFinSuccAbove (fun _ : Fin 5 => (volume : Measure ℝ)) 0
  simpa only [volume_pi] using this

/-- On a coefficient box the base trace lies in a window of length `2σ`. -/
theorem yTrace_mem_window {β u : Fin 5 → ℝ} {σ t : ℝ} (hu : u ∈ box β σ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : yTrace u t ∈ Icc (yTrace β t) (yTrace β t + 2 * σ) := by
  have h0 := hu 0 (mem_univ _)
  have h1 := hu 1 (mem_univ _)
  simp only [mem_Icc] at h0 h1
  simp only [yTrace, mem_Icc]
  constructor <;> nlinarith

/-- On a coefficient box the hidden trace moves by at most `3σ`. -/
theorem abs_xTrace_sub_le {β u : Fin 5 → ℝ} {σ t : ℝ} (hu : u ∈ box β σ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |xTrace u t - xTrace β t| ≤ 3 * σ := by
  have h2 := hu 2 (mem_univ _)
  have h3 := hu 3 (mem_univ _)
  have h4 := hu 4 (mem_univ _)
  simp only [mem_Icc] at h2 h3 h4
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have ht2' : 0 ≤ t ^ 2 := by positivity
  rw [abs_le]
  simp only [xTrace]
  constructor <;> nlinarith

/-- Slices with a slope restriction: coefficients in a box whose slope lies in `V` and whose
base trace lies in `A` have volume at most `σ³ |[β₁, β₁ + σ] ∩ V|` times the part of `A` in
the window of the box. -/
theorem volume_box_slope_yTrace_le (β : Fin 5 → ℝ) {σ t : ℝ} (hσ : 0 ≤ σ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {A V : Set ℝ} (hA : MeasurableSet A) (hV : MeasurableSet V) :
    volume {u : Fin 5 → ℝ | u ∈ box β σ ∧ u 1 ∈ V ∧ yTrace u t ∈ A} ≤
      ENNReal.ofReal (σ ^ 3) * volume (Icc (β 1) (β 1 + σ) ∩ V) *
        volume (A ∩ Icc (yTrace β t) (yTrace β t + 2 * σ)) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) 0
  set B4 : Set (Fin 4 → ℝ) := Set.pi univ (fun j : Fin 4 =>
    if j = 0 then Icc (β 1) (β 1 + σ) ∩ V else Icc (β j.succ) (β j.succ + σ))
  set S' : Set (ℝ × (Fin 4 → ℝ)) :=
    {p | p.1 ∈ Icc (β 0) (β 0 + σ) ∧ p.2 ∈ B4 ∧ p.1 + t * p.2 0 ∈ A}
  have hB4 : MeasurableSet B4 := by
    refine MeasurableSet.univ_pi (fun j => ?_)
    split_ifs
    · exact measurableSet_Icc.inter hV
    · exact measurableSet_Icc
  have hS'm : MeasurableSet S' := by
    refine (measurableSet_Icc.preimage measurable_fst).inter
      ((hB4.preimage measurable_snd).inter (hA.preimage ?_))
    fun_prop
  have hS : {u : Fin 5 → ℝ | u ∈ box β σ ∧ u 1 ∈ V ∧ yTrace u t ∈ A} = e ⁻¹' S' := by
    ext u
    simp only [box, yTrace, mem_ofPred_eq, mem_preimage, S', B4, mem_pi, mem_univ,
      true_implies]
    constructor
    · rintro ⟨hu, hv, hy⟩
      refine ⟨hu 0, fun j => ?_, ?_⟩
      · split_ifs with hj
        · subst hj
          exact ⟨by simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.tail] using hu 1,
            by simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.tail] using hv⟩
        · simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.tail] using hu j.succ
      · simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.tail] using hy
    · rintro ⟨h0, hj, hy⟩
      have h1 := hj 0
      simp only [↓reduceIte] at h1
      refine ⟨fun i => ?_, ?_, ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) i
        · simpa [e, MeasurableEquiv.piFinSuccAbove] using h0
        · by_cases hj0 : j = 0
          · subst hj0
            simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.tail] using h1.1
          · have := hj j
            simp only [hj0, ↓reduceIte] at this
            simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.tail] using this
      · simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.tail] using h1.2
      · simpa [e, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.tail] using hy
  rw [hS, measurePreserving_split.measure_preimage hS'm.nullMeasurableSet,
    Measure.prod_apply_symm hS'm]
  set W := A ∩ Icc (yTrace β t) (yTrace β t + 2 * σ)
  calc ∫⁻ w, volume ((fun x => (x, w)) ⁻¹' S')
      ≤ ∫⁻ w, B4.indicator (fun _ => volume W) w := by
        refine lintegral_mono fun w => ?_
        by_cases hw : w ∈ B4
        · rw [indicator_of_mem hw]
          have hsub : (fun x => (x, w)) ⁻¹' S' ⊆
              (fun x => x + t * w 0) ⁻¹' (A ∩ Icc (β 0 + t * w 0) (β 0 + t * w 0 + σ)) := by
            rintro x ⟨hx, -, hxA⟩
            refine ⟨hxA, ?_, ?_⟩ <;> simp only at hx ⊢ <;> linarith [hx.1, hx.2]
          refine (measure_mono hsub).trans ?_
          rw [measure_preimage_add_right]
          refine measure_mono (inter_subset_inter_right _ ?_)
          have hw0 := hw 0 (mem_univ _)
          simp only [↓reduceIte, mem_inter_iff, mem_Icc] at hw0
          intro y hy
          simp only [mem_Icc, yTrace] at hy ⊢
          constructor <;> nlinarith [hw0.1.1, hw0.1.2, hy.1, hy.2]
        · rw [indicator_of_notMem hw]
          have : (fun x => (x, w)) ⁻¹' S' = ∅ := by
            ext x
            simp only [mem_preimage, mem_empty_iff_false, iff_false, S', mem_ofPred_eq]
            exact fun h => hw h.2.1
          rw [this, measure_empty]
    _ = volume W * volume B4 := lintegral_indicator_const hB4 _
    _ = ENNReal.ofReal (σ ^ 3) * volume (Icc (β 1) (β 1 + σ) ∩ V) * volume W := by
        rw [volume_pi, Measure.pi_pi, Fin.prod_univ_succ]
        simp only [↓reduceIte, Fin.succ_ne_zero]
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_one]
        simp only [Real.volume_Icc, add_sub_cancel_left]
        rw [show ENNReal.ofReal (σ ^ 3) = ENNReal.ofReal σ * ENNReal.ofReal σ * ENNReal.ofReal σ by
          rw [← ENNReal.ofReal_mul hσ, ← ENNReal.ofReal_mul (by positivity)]; ring_nf]
        ring

/-- The slope-restricted slice bound with a hidden bin. -/
theorem volume_box_slope_slice_le (β : Fin 5 → ℝ) {σ t p : ℝ} (n : ℤ) (hσ : 0 ≤ σ) (hp : 0 < p)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) {V : Set ℝ}
    (hV : MeasurableSet V) :
    volume {u : Fin 5 → ℝ | u ∈ box β σ ∧ u 1 ∈ V ∧ (t, yTrace u t) ∈ A ∧
        ⌊xTrace u t / p⌋ = n} ≤
      ENNReal.ofReal (σ ^ 3) * volume (Icc (β 1) (β 1 + σ) ∩ V) * volume {y | (t, y) ∈ A ∧
        y ∈ Icc (yTrace β t) (yTrace β t + 2 * σ) ∧
        xTrace β t ∈ Icc (n * p - 3 * σ) ((n + 1) * p + 3 * σ)} := by
  by_cases hrel : xTrace β t ∈ Icc (n * p - 3 * σ) ((n + 1) * p + 3 * σ)
  · have hAt : MeasurableSet {y : ℝ | (t, y) ∈ A} := measurable_prodMk_left hA
    have h := volume_box_slope_yTrace_le β hσ ht0 ht1 hAt hV
    refine (measure_mono ?_).trans (h.trans_eq ?_)
    · rintro u ⟨hu, hv, hy, -⟩; exact ⟨hu, hv, hy⟩
    · congr 2
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq]
      tauto
  · have : {u : Fin 5 → ℝ | u ∈ box β σ ∧ u 1 ∈ V ∧ (t, yTrace u t) ∈ A ∧
        ⌊xTrace u t / p⌋ = n} = ∅ := by
      ext u
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro hu _ _ hn
      apply hrel
      have hx := abs_le.mp (abs_xTrace_sub_le hu ht0 ht1)
      have h1 := Int.floor_le (xTrace u t / p)
      have h2 := Int.lt_floor_add_one (xTrace u t / p)
      rw [hn, le_div_iff₀ hp] at h1
      rw [hn, div_lt_iff₀ hp] at h2
      constructor <;> linarith
    rw [this, measure_empty]
    exact zero_le

/-- Original incidences of a rounded tag near a noisy incidence stay in nearby cells. -/
theorem original_near {b β : Fin 5 → ℝ} {σ σ' B t t' : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσ' : 0 ≤ σ') (hσ'σ : σ' ≤ σ)
    (hb : ∀ i, |b i| ≤ B) (hround : ∀ i, |b i - β i| ≤ σ')
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htt' : |t' - t| ≤ σ) :
    |yTrace b t' - yTrace β t| ≤ (B + 4) * σ ∧
      |xTrace b t' - xTrace β t| ≤ (4 * B + 11) * σ := by
  have hβ : ∀ i, |β i| ≤ B + σ' := fun i => by
    have := hround i; have := hb i
    calc |β i| = |b i - (b i - β i)| := by ring_nf
      _ ≤ |b i| + |b i - β i| := abs_sub _ _
      _ ≤ B + σ' := by linarith
  have hd := fun i => abs_le.mp (hround i)
  have htt := abs_le.mp htt'
  have ht'0 : -σ ≤ t' := by linarith [htt.1]
  have ht'1 : t' ≤ 1 + σ := by linarith [htt.2]
  have ht'a : |t'| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  constructor
  · rw [abs_le]
    simp only [yTrace]
    have e : b 0 + t' * b 1 - (β 0 + t * β 1) =
        (b 0 - β 0) + t' * (b 1 - β 1) + (t' - t) * β 1 := by ring
    rw [e]
    have h1 : |t' * (b 1 - β 1)| ≤ 2 * σ' := by
      rw [abs_mul]
      nlinarith [abs_nonneg t', abs_nonneg (b 1 - β 1), hround 1]
    have h2 : |(t' - t) * β 1| ≤ σ * (B + σ') := by
      rw [abs_mul]; exact mul_le_mul htt' (hβ 1) (abs_nonneg _) hσ.le
    have h1' := abs_le.mp h1
    have h2' := abs_le.mp h2
    constructor <;> nlinarith [hd 0]
  · rw [abs_le]
    simp only [xTrace]
    have e : b 2 + t' * b 3 + t' ^ 2 * b 4 - (β 2 + t * β 3 + t ^ 2 * β 4) =
        (b 2 - β 2) + t' * (b 3 - β 3) + t' ^ 2 * (b 4 - β 4) + (t' - t) * β 3 +
          ((t' - t) * (t' + t)) * β 4 := by ring
    rw [e]
    have h1 : |t' * (b 3 - β 3)| ≤ 2 * σ' := by
      rw [abs_mul]; nlinarith [abs_nonneg t', abs_nonneg (b 3 - β 3), hround 3]
    have h2 : |t' ^ 2 * (b 4 - β 4)| ≤ 4 * σ' := by
      rw [abs_mul, abs_pow]
      have : |t'| ^ 2 ≤ 4 := by nlinarith [abs_nonneg t']
      nlinarith [abs_nonneg (b 4 - β 4), hround 4, sq_nonneg |t'|]
    have h3 : |(t' - t) * β 3| ≤ σ * (B + σ') := by
      rw [abs_mul]; exact mul_le_mul htt' (hβ 3) (abs_nonneg _) hσ.le
    have h4 : |((t' - t) * (t' + t)) * β 4| ≤ σ * 3 * (B + σ') := by
      rw [abs_mul, abs_mul]
      have : |t' + t| ≤ 3 := by rw [abs_le]; constructor <;> linarith
      have := mul_le_mul htt' this (abs_nonneg _) hσ.le
      exact mul_le_mul this (hβ 4) (abs_nonneg _) (by positivity)
    have h1' := abs_le.mp h1
    have h2' := abs_le.mp h2
    have h3' := abs_le.mp h3
    have h4' := abs_le.mp h4
    constructor <;> nlinarith [hd 2]

theorem card_Icc_floor_le (y w : ℝ) (hw : 0 ≤ w) :
    ((Finset.Icc ⌊y - w⌋ ⌊y + w⌋).card : ℝ) ≤ 2 * w + 2 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le (y + w)
  have h2 := Int.lt_floor_add_one (y - w)
  have hle : ⌊y - w⌋ ≤ ⌊y + w⌋ + 1 := by
    have := Int.floor_le_floor (show y - w ≤ y + w by linarith); omega
  have e : (((⌊y + w⌋ + 1 - ⌊y - w⌋).toNat : ℕ) : ℝ) =
      ((⌊y + w⌋ + 1 - ⌊y - w⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [e]
  push_cast
  linarith

theorem floor_mem_three {x p : ℝ} {n : ℤ} (hp : 0 < p) (h1 : ((n : ℝ) - 1) * p ≤ x)
    (h2 : x < ((n : ℝ) + 2) * p) : ⌊x / p⌋ ∈ ({n - 1, n, n + 1} : Finset ℤ) := by
  have hlo : ((n - 1 : ℤ) : ℝ) ≤ x / p := by
    rw [le_div_iff₀ hp]; push_cast; linarith
  have hhi : x / p < ((n + 2 : ℤ) : ℝ) := by
    rw [div_lt_iff₀ hp]; push_cast; linarith
  have a := Int.le_floor.mpr hlo
  have b := Int.floor_lt.mpr hhi
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem floor_mem_three' {x c : ℝ} {k : ℤ} (hc : 0 < c) (h : |x - k * c - c / 2| < 3 * c / 2) :
    ⌊x / c⌋ ∈ ({k - 1, k, k + 1} : Finset ℤ) := by
  have := abs_lt.mp h
  apply floor_mem_three hc <;> linarith [this.1, this.2]

open Classical in
/-- Prior weights of marked tags whose noisy incidences reach a point `(t, y)` in a hidden bin
`n`, for tags in `Fin H`, time bins `[z/J, (z+1)/J)` of width at most `σ`, a tag filter `P`
and an original-label filter `F` containing every label of a tag satisfying `P`. -/
theorem tag_weight_sum_le_fin {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (b : α → Fin 5 → ℝ) {H J : ℕ} (tag : α → Fin H) (b₀ : Fin H → Fin 5 → ℝ)
    (w : Fin H → ENNReal) (mark : Fin H → Fin J → Bool) (P : Fin H → Prop) (F : Set α)
    {σ σ' B K₁ Q p t y : ℝ} (n : ℤ)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσ' : 0 ≤ σ') (hσ'σ : σ' ≤ σ) (hB : 0 ≤ B) (hK₁ : 0 < K₁)
    (hJ : 1 ≤ (J : ℝ) * σ) (hp : σ ≤ p)
    (htag : ∀ j, MeasurableSet (tag ⁻¹' {j}))
    (hb : ∀ l i, |b l i| ≤ B) (hround : ∀ l i, |b l i - b₀ (tag l) i| ≤ σ')
    (hmark : ∀ j z, mark j z = true → ENNReal.ofReal (1 / ((J : ℝ) * K₁)) * w j ≤
      μ {r | tag r.1 = j ∧ r.2 ∈ Ico ((z : ℝ) / J) (((z : ℝ) + 1) / J)})
    (hF : ∀ l, P (tag l) → l ∈ F)
    (hcap : ∀ (q : Fin 2 → ℤ) (m : ℤ), μ {r | r.1 ∈ F ∧
      (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = q ∧
      ⌊xTrace (b r.1) r.2 / p⌋ = m} ≤ ENNReal.ofReal Q)
    (z : Fin J) (ht : t ∈ Ico ((z : ℝ) / J) (((z : ℝ) + 1) / J)) :
    ∑ j, (if P j ∧ mark j z = true ∧ y ∈ Icc (yTrace (b₀ j) t) (yTrace (b₀ j) t + 2 * σ) ∧
        xTrace (b₀ j) t ∈ Icc (n * p - 3 * σ) ((n + 1) * p + 3 * σ) then w j else 0) ≤
      ENNReal.ofReal ((J : ℝ) * K₁) *
        ENNReal.ofReal (3 * (2 * (B + 6) + 2) * (2 * ((⌈4 * B⌉ + 15 : ℤ) : ℝ) + 1) * Q) := by
  set G := Finset.univ.filter (fun j => P j ∧ mark j z = true ∧
    y ∈ Icc (yTrace (b₀ j) t) (yTrace (b₀ j) t + 2 * σ) ∧
    xTrace (b₀ j) t ∈ Icc (n * p - 3 * σ) ((n + 1) * p + 3 * σ)) with hG
  rw [← Finset.sum_filter]
  have hp0 : 0 < p := lt_of_lt_of_le hσ hp
  have hJpos : (0 : ℝ) < J := by
    by_contra h; push Not at h
    have : (J : ℝ) * σ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hσ.le
    linarith
  have hz1 : ((z : ℕ) : ℝ) + 1 ≤ J := by exact_mod_cast z.2
  have hbinlen : 1 / (J : ℝ) ≤ σ := by
    rw [div_le_iff₀ hJpos]; linarith
  have ht0 : 0 ≤ t := le_trans (by positivity) ht.1
  have ht1 : t ≤ 1 := by
    have := ht.2.le
    calc t ≤ ((z : ℝ) + 1) / J := this
      _ ≤ 1 := by rw [div_le_one hJpos]; exact hz1
  set k : ℤ := ⌊t / σ⌋ with hk
  have hkt : (k : ℝ) * σ ≤ t ∧ t < (k + 1) * σ := by
    have h1 := Int.floor_le (t / σ)
    have h2 := Int.lt_floor_add_one (t / σ)
    rw [← hk] at h1 h2
    exact ⟨by rwa [le_div_iff₀ hσ] at h1, by rwa [div_lt_iff₀ hσ] at h2⟩
  set Tset : Finset ℤ := {k - 1, k, k + 1}
  set Y := Finset.Icc ⌊y / σ - (B + 6)⌋ ⌊y / σ + (B + 6)⌋
  set E : ℤ := ⌈4 * B⌉ + 15 with hE
  set Mset : Finset ℤ := Finset.Icc (n - E) (n + E)
  set cell : ℤ → ℤ → ℤ → Set (α × ℝ) := fun a c m => {r | r.1 ∈ F ∧
      (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = ![a, c] ∧
      ⌊xTrace (b r.1) r.2 / p⌋ = m}
  set bin : Set ℝ := Ico ((z : ℝ) / J) (((z : ℝ) + 1) / J)
  have hsub : (⋃ j ∈ G, {r : α × ℝ | tag r.1 = j ∧ r.2 ∈ bin}) ⊆
      ⋃ a ∈ Tset, ⋃ c ∈ Y, ⋃ m ∈ Mset, cell a c m := by
    intro r hr
    simp only [mem_iUnion, mem_ofPred_eq] at hr
    obtain ⟨j, hjG, hτj, hrbin⟩ := hr
    obtain ⟨hPj, -, hyw, hxw⟩ := (Finset.mem_filter.mp hjG).2
    have htt'' : |r.2 - t| < σ := by
      have h1 : (z : ℝ) / J ≤ r.2 := hrbin.1
      have h2 : r.2 < ((z : ℝ) + 1) / J := hrbin.2
      have h3 : (z : ℝ) / J ≤ t := ht.1
      have h4 : t < ((z : ℝ) + 1) / J := ht.2
      have e : ((z : ℝ) + 1) / J = (z : ℝ) / J + 1 / J := by ring
      rw [abs_lt]; constructor <;> linarith
    have htt' : |r.2 - t| ≤ σ := htt''.le
    have hnear := original_near (b := b r.1) (β := b₀ j) hσ hσ1 hσ' hσ'σ (hb r.1)
      (by rw [← hτj]; exact hround r.1) ht0 ht1 htt'
    have hy1 := abs_le.mp hnear.1
    have hx1 := abs_le.mp hnear.2
    simp only [mem_Icc] at hyw hxw
    simp only [mem_iUnion]
    refine ⟨⌊r.2 / σ⌋, ?_, ⌊yTrace (b r.1) r.2 / σ⌋, ?_, ⌊xTrace (b r.1) r.2 / p⌋, ?_, ?_⟩
    · apply floor_mem_three' hσ
      have := abs_lt.mp htt''
      rw [abs_lt]; constructor <;> linarith [hkt.1, hkt.2]
    · rw [Finset.mem_Icc]
      constructor
      · apply Int.floor_le_floor
        rw [le_div_iff₀ hσ]
        have : (y / σ - (B + 6)) * σ = y - (B + 6) * σ := by field_simp
        rw [this]; linarith
      · apply Int.floor_le_floor
        rw [div_le_iff₀ hσ]
        have : (y / σ + (B + 6)) * σ = y + (B + 6) * σ := by field_simp
        rw [this]; linarith
    · have hEr : (4 * B + 14) * σ < (E : ℝ) * p := by
        have hc := Int.le_ceil (4 * B)
        have : (4 * B + 14) * σ < ((⌈4 * B⌉ + 15 : ℤ) : ℝ) * σ := by
          push_cast; nlinarith
        calc (4 * B + 14) * σ < ((⌈4 * B⌉ + 15 : ℤ) : ℝ) * σ := this
          _ ≤ (E : ℝ) * p := by
            rw [hE]; exact mul_le_mul_of_nonneg_left hp (by push_cast; linarith)
      rw [Finset.mem_Icc]
      constructor
      · apply Int.le_floor.mpr
        rw [le_div_iff₀ hp0]; push_cast; nlinarith
      · have : xTrace (b r.1) r.2 / p < ((n + E : ℤ) : ℝ) + 1 := by
          rw [div_lt_iff₀ hp0]; push_cast; nlinarith
        exact Int.lt_add_one_iff.mp (Int.floor_lt.mpr (by push_cast at this ⊢; linarith))
    · exact ⟨hF r.1 (by rw [hτj]; exact hPj), rfl, rfl⟩
  have hdisj : (↑G : Set (Fin H)).PairwiseDisjoint
      (fun j => {r : α × ℝ | tag r.1 = j ∧ r.2 ∈ bin}) := by
    intro i _ j _ hij
    refine Set.disjoint_left.mpr ?_
    rintro r ⟨hi, -⟩ ⟨hj, -⟩
    exact hij (hi.symm.trans hj)
  have hmeas : ∀ j ∈ G, MeasurableSet {r : α × ℝ | tag r.1 = j ∧ r.2 ∈ bin} := by
    intro j _
    exact ((htag j).preimage measurable_fst).inter (measurableSet_Ico.preimage measurable_snd)
  have hYc : (Y.card : ℝ) ≤ 2 * (B + 6) + 2 := card_Icc_floor_le _ _ (by linarith)
  have hMc : (Mset.card : ℝ) ≤ 2 * (E : ℝ) + 1 := by
    have hE0 : (0 : ℤ) ≤ E := by
      have := Int.le_ceil (4 * B); have : (0 : ℤ) ≤ ⌈4 * B⌉ := Int.ceil_nonneg (by linarith)
      omega
    rw [Int.card_Icc, show n + E + 1 - (n - E) = 2 * E + 1 by ring,
      show (((2 * E + 1).toNat : ℕ) : ℝ) = ((2 * E + 1 : ℤ) : ℝ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]
    push_cast; linarith
  have hTc : Tset.card ≤ 3 := Finset.card_le_three
  have key : ENNReal.ofReal (1 / ((J : ℝ) * K₁)) * ∑ j ∈ G, w j ≤
      ENNReal.ofReal (3 * (2 * (B + 6) + 2) * (2 * ((⌈4 * B⌉ + 15 : ℤ) : ℝ) + 1) * Q) := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ G, ENNReal.ofReal (1 / ((J : ℝ) * K₁)) * w j
        ≤ ∑ j ∈ G, μ {r : α × ℝ | tag r.1 = j ∧ r.2 ∈ bin} :=
          Finset.sum_le_sum fun j hj => hmark j z (Finset.mem_filter.mp hj).2.2.1
      _ = μ (⋃ j ∈ G, {r : α × ℝ | tag r.1 = j ∧ r.2 ∈ bin}) :=
          (measure_biUnion_finset hdisj hmeas).symm
      _ ≤ μ (⋃ a ∈ Tset, ⋃ c ∈ Y, ⋃ m ∈ Mset, cell a c m) := measure_mono hsub
      _ ≤ ∑ a ∈ Tset, ∑ c ∈ Y, ∑ m ∈ Mset, μ (cell a c m) := by
          refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
          exact measure_biUnion_finset_le _ _
      _ ≤ ∑ a ∈ Tset, ∑ c ∈ Y, ∑ m ∈ Mset, ENNReal.ofReal Q :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ =>
            Finset.sum_le_sum fun m _ => hcap ![a, c] m
      _ = ((Tset.card * (Y.card * Mset.card) : ℕ) : ENNReal) * ENNReal.ofReal Q := by
          simp only [Finset.sum_const, nsmul_eq_mul]; push_cast; ring
      _ ≤ ENNReal.ofReal (3 * (2 * (B + 6) + 2) * (2 * ((⌈4 * B⌉ + 15 : ℤ) : ℝ) + 1) * Q) := by
          rcases le_or_gt Q 0 with hQ | hQ
          · rw [ENNReal.ofReal_of_nonpos hQ, mul_zero]; exact zero_le
          · rw [ENNReal.ofReal_mul (by
              have := Int.le_ceil (4 * B); have : (0 : ℤ) ≤ ⌈4 * B⌉ := Int.ceil_nonneg (by linarith)
              have : (0 : ℝ) ≤ ((⌈4 * B⌉ + 15 : ℤ) : ℝ) := by exact_mod_cast (by omega : (0:ℤ) ≤ ⌈4 * B⌉ + 15)
              positivity)]
            gcongr
            rw [← ENNReal.ofReal_natCast]
            apply ENNReal.ofReal_le_ofReal
            push_cast
            have hT' : (Tset.card : ℝ) ≤ 3 := by exact_mod_cast hTc
            calc (Tset.card : ℝ) * (Y.card * Mset.card) ≤
                3 * ((2 * (B + 6) + 2) * (2 * (E : ℝ) + 1)) := by
                  have hY0 : (0 : ℝ) ≤ Y.card := Nat.cast_nonneg _
                  have hM0 : (0 : ℝ) ≤ Mset.card := Nat.cast_nonneg _
                  gcongr
              _ = 3 * (2 * (B + 6) + 2) * (2 * ((⌈4 * B⌉ : ℝ) + 15) + 1) := by
                  rw [hE]; push_cast; ring
  calc ∑ j ∈ G, w j = ENNReal.ofReal ((J : ℝ) * K₁) *
        (ENNReal.ofReal (1 / ((J : ℝ) * K₁)) * ∑ j ∈ G, w j) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          show (J : ℝ) * K₁ * (1 / ((J : ℝ) * K₁)) = 1 by field_simp]
        simp
    _ ≤ ENNReal.ofReal ((J : ℝ) * K₁) *
        ENNReal.ofReal (3 * (2 * (B + 6) + 2) * (2 * ((⌈4 * B⌉ + 15 : ℤ) : ℝ) + 1) * Q) := by
        gcongr

/-- The coefficient noise of o099: five independent normalized uniform laws on `[0, σ]`. -/
noncomputable def noise (σ : ℝ) : Measure (Fin 5 → ℝ) :=
  Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • volume.restrict (Icc (0 : ℝ) σ))

/-- The marked prior of o099: tag `j` carries weight `w j` and noisy coefficients `b₀ j + u`. -/
noncomputable def markedPrior (σ : ℝ) (H : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) :
    Measure (ℕ × (Fin 5 → ℝ)) :=
  ∑ j, ENNReal.ofReal (w j) • Measure.map (fun u : Fin 5 → ℝ => ((j : ℕ), b₀ j + u)) (noise σ)

/-- The marked event of o099: marked time bins `[z/J, (z+1)/J)` of each tag. -/
def markedEvent (H J : ℕ) (mark : Fin H → Fin J → Bool) : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  {p | ∃ j : Fin H, p.1.1 = (j : ℕ) ∧ ∃ z : Fin J, mark j z = true ∧
    p.2 ∈ Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))}

/-- The marked law of o099. -/
noncomputable def markedLaw (σ : ℝ) (H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
  ((markedPrior σ H b₀ w).prod volume).restrict (markedEvent H J mark)

theorem box_zero (σ : ℝ) : box 0 σ = Set.pi univ (fun _ : Fin 5 => Icc (0 : ℝ) σ) := by
  ext u; simp [box]

theorem isFiniteMeasure_unif (σ : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal (σ⁻¹) • volume.restrict (Icc (0 : ℝ) σ)) :=
  ⟨by rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

theorem noise_eq {σ : ℝ} :
    noise σ = ENNReal.ofReal (σ⁻¹) ^ 5 • volume.restrict (box 0 σ) := by
  have := isFiniteMeasure_unif σ
  unfold noise
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    box_zero, ← Set.pi_inter_distrib, volume_pi, Measure.pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hs _)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem markedPrior_apply (σ : ℝ) (H : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ)
    {X : Set (ℕ × (Fin 5 → ℝ))} (hX : MeasurableSet X) :
    markedPrior σ H b₀ w X = ∑ j, ENNReal.ofReal (w j) * (ENNReal.ofReal (σ⁻¹) ^ 5 *
      volume ({v | ((j : ℕ), v) ∈ X} ∩ box (b₀ j) σ)) := by
  unfold markedPrior
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (by fun_prop) hX, noise_eq,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (by
      exact hX.preimage (by fun_prop))]
  congr 2
  have hXj : MeasurableSet {v : Fin 5 → ℝ | ((j : ℕ), v) ∈ X} := measurable_prodMk_left hX
  have : (fun u : Fin 5 → ℝ => ((j : ℕ), b₀ j + u)) ⁻¹' X ∩ box 0 σ =
      (fun u => b₀ j + u) ⁻¹' ({v | ((j : ℕ), v) ∈ X} ∩ box (b₀ j) σ) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, box, mem_pi, mem_univ,
      true_implies, mem_Icc, Pi.add_apply, Pi.zero_apply, zero_add]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i => ⟨by linarith [(h2 i).1], by linarith [(h2 i).2]⟩⟩
  rw [this, measure_preimage_add]

theorem isFiniteMeasure_markedPrior (σ : ℝ) (H : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) :
    IsFiniteMeasure (markedPrior σ H b₀ w) := by
  refine ⟨?_⟩
  rw [markedPrior_apply σ H b₀ w MeasurableSet.univ]
  refine ENNReal.sum_lt_top.mpr fun j _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ?_)
  refine (measure_mono inter_subset_right).trans_lt ?_
  rcases le_or_gt 0 σ with hσ | hσ
  · rw [volume_box _ hσ]; exact ENNReal.ofReal_lt_top
  · have : box (b₀ j) σ = ∅ := by
      ext u; simp only [box, mem_pi, mem_univ, true_implies, mem_Icc, mem_empty_iff_false,
        iff_false, not_forall]
      exact ⟨0, fun h => by linarith [h.1, h.2]⟩
    rw [this, measure_empty]; exact ENNReal.zero_lt_top

theorem measurableSet_markedEvent (H J : ℕ) (mark : Fin H → Fin J → Bool) :
    MeasurableSet (markedEvent H J mark) := by
  have : markedEvent H J mark = ⋃ j : Fin H, ⋃ z : Fin J,
      if mark j z = true then {p : (ℕ × (Fin 5 → ℝ)) × ℝ | p.1.1 = (j : ℕ)} ∩
        {p | p.2 ∈ Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))} else ∅ := by
    ext p
    simp only [markedEvent, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨j, hj, z, hm, ht⟩; exact ⟨j, z, by simp only [hm, ite_true]; exact ⟨hj, ht⟩⟩
    · rintro ⟨j, z, h⟩
      split_ifs at h with hm
      · exact ⟨j, h.1, z, hm, h.2⟩
      · exact absurd h (notMem_empty _)
  rw [this]
  refine MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun z => ?_
  split_ifs
  · exact ((measurableSet_singleton _).preimage (measurable_fst.comp measurable_fst)).inter
      (measurableSet_Ico.preimage measurable_snd)
  · exact MeasurableSet.empty

theorem bin_unique {J : ℕ} {t : ℝ} {z z' : Fin J}
    (h : t ∈ Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ)))
    (h' : t ∈ Ico ((z' : ℝ) / (J : ℝ)) (((z' : ℝ) + 1) / (J : ℝ))) : z = z' := by
  have hJ : (0 : ℝ) < J := by
    have := z.2; exact_mod_cast (show 0 < J by omega)
  have key : ∀ y : Fin J, t ∈ Ico ((y : ℝ) / (J : ℝ)) (((y : ℝ) + 1) / (J : ℝ)) →
      ⌊t * J⌋ = (y : ℤ) := by
    intro y hy
    apply Int.floor_eq_iff.mpr
    have h1 := hy.1; have h2 := hy.2
    rw [div_le_iff₀ hJ] at h1
    rw [lt_div_iff₀ hJ] at h2
    push_cast; constructor <;> linarith
  have := (key z h).symm.trans (key z' h')
  exact Fin.ext (by exact_mod_cast this)

theorem bin_subset {J : ℕ} (z : Fin J) :
    Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ)) ⊆ Ico (0 : ℝ) 1 := by
  have hJ : (0 : ℝ) < J := by
    have := z.2; exact_mod_cast (show 0 < J by omega)
  have hz : ((z : ℕ) : ℝ) + 1 ≤ J := by exact_mod_cast z.2
  intro t ht
  refine ⟨le_trans (by positivity) ht.1, lt_of_lt_of_le ht.2 ?_⟩
  rw [div_le_one hJ]; exact hz

/-- **Exact-base ceiling of the marked law (o099 vocabulary).** For incidences of the marked law
whose base point `(t, y)` lies in `A`, whose hidden trace lies in the `p`-bin `n` and whose
noisy slope lies in `V`, the mass is at most `(L/σ²) (J K₁) C(B) Q |A|`, when every tag's slope
interval meets `V` in length at most `L`, marks carry `w j/(J K₁)` of original active mass, and
original `(σ, σ, p)`-cells restricted to `F` have mass at most `Q`. -/
theorem markedLaw_ceiling_gen {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (b : α → Fin 5 → ℝ) {H J : ℕ} (tag : α → Fin H) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) (V : Set ℝ) (F : Set α) {σ σ' B K₁ Q p L : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσ' : 0 ≤ σ') (hσ'σ : σ' ≤ σ) (hB : 0 ≤ B) (hK₁ : 0 < K₁)
    (hJ : 1 ≤ (J : ℝ) * σ) (hp : σ ≤ p) (hV : MeasurableSet V)
    (hVL : ∀ j, volume (Icc (b₀ j 1) (b₀ j 1 + σ) ∩ V) ≤ ENNReal.ofReal L)
    (htag : ∀ j, MeasurableSet (tag ⁻¹' {j}))
    (hb : ∀ l i, |b l i| ≤ B) (hround : ∀ l i, |b l i - b₀ (tag l) i| ≤ σ')
    (hmark : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K₁)) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))})
    (hF : ∀ l, (Icc (b₀ (tag l) 1) (b₀ (tag l) 1 + σ) ∩ V).Nonempty → l ∈ F)
    (hcap : ∀ (q : Fin 2 → ℤ) (m : ℤ), μ {r | r.1 ∈ F ∧
      (![⌊r.2 / σ⌋, ⌊yTrace (b r.1) r.2 / σ⌋] : Fin 2 → ℤ) = q ∧
      ⌊xTrace (b r.1) r.2 / p⌋ = m} ≤ ENNReal.ofReal Q)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) (n : ℤ) :
    markedLaw σ H J b₀ w mark {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧
        ⌊xTrace q.1.2 q.2 / p⌋ = n ∧ q.1.2 1 ∈ V} ≤
      ENNReal.ofReal (L / σ ^ 2) * (ENNReal.ofReal ((J : ℝ) * K₁) *
        ENNReal.ofReal (3 * (2 * (B + 6) + 2) * (2 * ((⌈4 * B⌉ + 15 : ℤ) : ℝ) + 1) * Q)) *
          volume A := by
  classical
  have := isFiniteMeasure_markedPrior σ H b₀ w
  have hp0 : 0 < p := lt_of_lt_of_le hσ hp
  set S : Set ((ℕ × (Fin 5 → ℝ)) × ℝ) :=
    {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧ ⌊xTrace q.1.2 q.2 / p⌋ = n ∧ q.1.2 1 ∈ V}
  have hS : MeasurableSet S := by
    refine (hA.preimage ?_).inter (MeasurableSet.inter ?_ (hV.preimage ?_))
    · exact measurable_snd.prodMk (measurable_yTrace.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    · refine (measurableSet_singleton n).preimage ?_
      exact Int.measurable_floor.comp ((measurable_xTrace.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).div_const p)
    · exact (measurable_pi_apply 1).comp (measurable_snd.comp measurable_fst)
  set W : ENNReal := ENNReal.ofReal ((J : ℝ) * K₁) *
    ENNReal.ofReal (3 * (2 * (B + 6) + 2) * (2 * ((⌈4 * B⌉ + 15 : ℤ) : ℝ) + 1) * Q)
  set E := markedEvent H J mark
  have hE := measurableSet_markedEvent H J mark
  unfold markedLaw
  rw [Measure.restrict_apply hS, Measure.prod_apply_symm (hS.inter hE)]
  have hslice : ∀ t : ℝ, markedPrior σ H b₀ w ((fun x => (x, t)) ⁻¹' (S ∩ E)) ≤
      ENNReal.ofReal (L / σ ^ 2) * W * volume {y | (t, y) ∈ A} := by
    intro t
    have hXm : MeasurableSet ((fun x => (x, t)) ⁻¹' (S ∩ E)) :=
      measurable_prodMk_right (hS.inter hE)
    rw [markedPrior_apply σ H b₀ w hXm]
    by_cases ht : ∃ z : Fin J, t ∈ Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))
    swap
    · have : ∀ j : Fin H, {v | ((j : ℕ), v) ∈ (fun x => (x, t)) ⁻¹' (S ∩ E)} ∩
          box (b₀ j) σ = ∅ := by
        intro j
        ext u
        simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, j', -, z, -, hz⟩, -⟩
        exact ht ⟨z, hz⟩
      rw [Finset.sum_congr rfl (fun j _ => by rw [this j, measure_empty, mul_zero, mul_zero]),
        Finset.sum_const_zero]
      exact zero_le
    obtain ⟨z₀, hz₀⟩ := ht
    have ht01 := bin_subset z₀ hz₀
    set At : Set ℝ := {y | (t, y) ∈ A}
    set G' : Fin H → Set ℝ := fun j => {y | (Icc (b₀ j 1) (b₀ j 1 + σ) ∩ V).Nonempty ∧
      mark j z₀ = true ∧ y ∈ Icc (yTrace (b₀ j) t) (yTrace (b₀ j) t + 2 * σ) ∧
      xTrace (b₀ j) t ∈ Icc (n * p - 3 * σ) ((n + 1) * p + 3 * σ)}
    have hG' : ∀ j, MeasurableSet (G' j) := by
      intro j
      by_cases h : (Icc (b₀ j 1) (b₀ j 1 + σ) ∩ V).Nonempty ∧ mark j z₀ = true ∧
          xTrace (b₀ j) t ∈ Icc (n * p - 3 * σ) ((n + 1) * p + 3 * σ)
      · have : G' j = Icc (yTrace (b₀ j) t) (yTrace (b₀ j) t + 2 * σ) := by
          ext y; simp only [G', mem_ofPred_eq]; tauto
        rw [this]; exact measurableSet_Icc
      · have : G' j = ∅ := by
          ext y; simp only [G', mem_ofPred_eq, mem_empty_iff_false, iff_false]; tauto
        rw [this]; exact MeasurableSet.empty
    have hterm : ∀ j : Fin H, ENNReal.ofReal (w j) * (ENNReal.ofReal (σ⁻¹) ^ 5 *
        volume ({v | ((j : ℕ), v) ∈ (fun x => (x, t)) ⁻¹' (S ∩ E)} ∩ box (b₀ j) σ)) ≤
          ENNReal.ofReal (L / σ ^ 2) * (ENNReal.ofReal (w j) * volume (G' j ∩ At)) := by
      intro j
      by_cases hjk : (Icc (b₀ j 1) (b₀ j 1 + σ) ∩ V).Nonempty ∧ mark j z₀ = true
      · have hset : {v | ((j : ℕ), v) ∈ (fun x => (x, t)) ⁻¹' (S ∩ E)} ∩ box (b₀ j) σ =
            {u | u ∈ box (b₀ j) σ ∧ u 1 ∈ V ∧ (t, yTrace u t) ∈ A ∧
              ⌊xTrace u t / p⌋ = n} := by
          ext u
          simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, S, E, markedEvent]
          constructor
          · rintro ⟨⟨⟨h1, h2, hv⟩, -⟩, h3⟩; exact ⟨h3, hv, h1, h2⟩
          · rintro ⟨h3, hv, h1, h2⟩; exact ⟨⟨⟨h1, h2, hv⟩, j, rfl, z₀, hjk.2, hz₀⟩, h3⟩
        rw [hset]
        have hsl := volume_box_slope_slice_le (b₀ j) n hσ.le hp0 ht01.1 ht01.2.le hA hV
        have hG'eq : {y | (t, y) ∈ A ∧ y ∈ Icc (yTrace (b₀ j) t) (yTrace (b₀ j) t + 2 * σ) ∧
            xTrace (b₀ j) t ∈ Icc (n * p - 3 * σ) ((n + 1) * p + 3 * σ)} = G' j ∩ At := by
          ext y; simp only [G', At, mem_inter_iff, mem_ofPred_eq]
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨⟨hjk.1, hjk.2, h2, h3⟩, h1⟩
          · rintro ⟨⟨-, -, h2, h3⟩, h1⟩; exact ⟨h1, h2, h3⟩
        rw [hG'eq] at hsl
        calc ENNReal.ofReal (w j) * (ENNReal.ofReal (σ⁻¹) ^ 5 * volume {u | u ∈ box (b₀ j) σ ∧
              u 1 ∈ V ∧ (t, yTrace u t) ∈ A ∧ ⌊xTrace u t / p⌋ = n})
            ≤ ENNReal.ofReal (w j) * (ENNReal.ofReal (σ⁻¹) ^ 5 * (ENNReal.ofReal (σ ^ 3) *
                ENNReal.ofReal L * volume (G' j ∩ At))) := by
              gcongr
              exact hsl.trans (by gcongr; exact hVL j)
          _ = ENNReal.ofReal (L / σ ^ 2) * (ENNReal.ofReal (w j) * volume (G' j ∩ At)) := by
              rw [← ENNReal.ofReal_pow (by positivity)]
              rw [show ENNReal.ofReal (w j) * (ENNReal.ofReal ((σ⁻¹) ^ 5) * (ENNReal.ofReal (σ ^ 3) *
                ENNReal.ofReal L * volume (G' j ∩ At))) = (ENNReal.ofReal ((σ⁻¹) ^ 5) *
                ENNReal.ofReal (σ ^ 3) * ENNReal.ofReal L) * (ENNReal.ofReal (w j) *
                volume (G' j ∩ At)) by ring]
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
              congr 2
              field_simp
      · have : {v | ((j : ℕ), v) ∈ (fun x => (x, t)) ⁻¹' (S ∩ E)} ∩ box (b₀ j) σ = ∅ := by
          ext u
          simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_empty_iff_false,
            iff_false, S, E, markedEvent]
          rintro ⟨⟨⟨-, -, hv⟩, j', hj', z, hm, hz⟩, hu⟩
          have hjj : j = j' := Fin.ext hj'
          subst hjj
          have hzz := bin_unique hz hz₀
          subst hzz
          exact hjk ⟨⟨u 1, hu 1 (mem_univ _), hv⟩, hm⟩
        rw [this, measure_empty, mul_zero, mul_zero]; exact zero_le
    have hsum : ∑ j, ENNReal.ofReal (w j) * volume (G' j ∩ At) ≤ W * volume At := by
      have h1 : ∑ j, ENNReal.ofReal (w j) * volume (G' j ∩ At) =
          ∫⁻ y in At, ∑ j, (G' j).indicator (fun _ => ENNReal.ofReal (w j)) y := by
        rw [lintegral_finsetSum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_indicator_const (hG' j), Measure.restrict_apply (hG' j)]
        · intro j _
          exact measurable_const.indicator (hG' j)
      rw [h1]
      calc ∫⁻ y in At, ∑ j, (G' j).indicator (fun _ => ENNReal.ofReal (w j)) y
          ≤ ∫⁻ y in At, W := by
            refine lintegral_mono fun y => ?_
            have := tag_weight_sum_le_fin μ b tag b₀ (fun j => ENNReal.ofReal (w j)) mark
              (fun j => (Icc (b₀ j 1) (b₀ j 1 + σ) ∩ V).Nonempty) F (y := y) n
              hσ hσ1 hσ' hσ'σ hB hK₁ hJ hp htag hb hround
              (fun j z hm => by
                rw [← ENNReal.ofReal_mul (by positivity [hJ])]
                rw [show 1 / ((J : ℝ) * K₁) * w j = w j / ((J : ℝ) * K₁) by ring]
                exact hmark j z hm) hF hcap z₀ hz₀
            refine le_trans (le_of_eq ?_) this
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [indicator, G', mem_ofPred_eq]
        _ = W * volume At := by rw [setLIntegral_const]
    calc ∑ j, ENNReal.ofReal (w j) * (ENNReal.ofReal (σ⁻¹) ^ 5 *
          volume ({v | ((j : ℕ), v) ∈ (fun x => (x, t)) ⁻¹' (S ∩ E)} ∩ box (b₀ j) σ))
        ≤ ∑ j, ENNReal.ofReal (L / σ ^ 2) * (ENNReal.ofReal (w j) * volume (G' j ∩ At)) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = ENNReal.ofReal (L / σ ^ 2) * ∑ j, ENNReal.ofReal (w j) * volume (G' j ∩ At) := by
          rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal (L / σ ^ 2) * (W * volume At) := by gcongr
      _ = ENNReal.ofReal (L / σ ^ 2) * W * volume {y | (t, y) ∈ A} := by rw [← mul_assoc]
  calc ∫⁻ t, markedPrior σ H b₀ w ((fun x => (x, t)) ⁻¹' (S ∩ E))
      ≤ ∫⁻ t, ENNReal.ofReal (L / σ ^ 2) * W * volume {y | (t, y) ∈ A} := lintegral_mono hslice
    _ = ENNReal.ofReal (L / σ ^ 2) * W * ∫⁻ t, volume {y | (t, y) ∈ A} := by
        rw [lintegral_const_mul]
        exact measurable_measure_prodMk_left hA
    _ = ENNReal.ofReal (L / σ ^ 2) * W * volume A := by
        rw [Measure.volume_eq_prod, Measure.prod_apply hA]
        rfl

theorem noise_univ {σ : ℝ} (hσ : 0 < σ) : noise σ univ = 1 := by
  rw [noise_eq, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, volume_box _ hσ.le, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  rw [show (σ⁻¹) ^ 5 * σ ^ 5 = 1 by field_simp]
  simp

theorem markedEvent_subset (H J : ℕ) (mark : Fin H → Fin J → Bool) :
    markedEvent H J mark ⊆ univ ×ˢ Ico (0 : ℝ) 1 := by
  rintro p ⟨j, -, z, -, hz⟩
  exact ⟨mem_univ _, bin_subset z hz⟩

theorem isFiniteMeasure_markedLaw (σ : ℝ) (H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ)
    (mark : Fin H → Fin J → Bool) : IsFiniteMeasure (markedLaw σ H J b₀ w mark) := by
  have := isFiniteMeasure_markedPrior σ H b₀ w
  refine ⟨?_⟩
  unfold markedLaw
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  refine (measure_mono (markedEvent_subset H J mark)).trans_lt ?_
  rw [Measure.prod_prod, Real.volume_Ico]
  exact ENNReal.mul_lt_top (measure_lt_top _ _) ENNReal.ofReal_lt_top

/-- A measure on `Y × ℤ` bounded by `c ρ` on every slab `A × {n}` is bounded by
`c (ρ ⊗ count)`. -/
theorem le_smul_prod_count {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y) [SFinite ρ]
    (ν : Measure (Y × ℤ)) (c : ENNReal)
    (h : ∀ A, MeasurableSet A → ∀ n : ℤ, ν (A ×ˢ {n}) ≤ c * ρ A) :
    ν ≤ c • ρ.prod Measure.count := by
  refine Measure.le_iff.mpr fun S hS => ?_
  have hSn : ∀ n : ℤ, MeasurableSet {y | (y, n) ∈ S} := fun n => measurable_prodMk_right hS
  have hdec : S = ⋃ n : ℤ, {y | (y, n) ∈ S} ×ˢ {n} := by
    ext ⟨y, n⟩
    simp only [mem_iUnion, mem_prod, mem_ofPred_eq, mem_singleton_iff]
    exact ⟨fun h => ⟨n, h, rfl⟩, fun ⟨m, h, hm⟩ => hm ▸ h⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℤ => {y | (y, n) ∈ S} ×ˢ ({n} : Set ℤ)) := by
    intro m n hmn
    refine Set.disjoint_left.mpr ?_
    rintro ⟨y, k⟩ ⟨-, hk⟩ ⟨-, hk'⟩
    simp only [mem_singleton_iff] at hk hk'
    exact hmn (hk.symm.trans hk')
  calc ν S = ∑' n : ℤ, ν ({y | (y, n) ∈ S} ×ˢ {n}) := by
        conv_lhs => rw [hdec]
        exact measure_iUnion hdisj (fun n => (hSn n).prod (measurableSet_singleton n))
    _ ≤ ∑' n : ℤ, c * ρ {y | (y, n) ∈ S} := ENNReal.tsum_le_tsum fun n => h _ (hSn n) n
    _ = c * ∑' n : ℤ, ρ {y | (y, n) ∈ S} := ENNReal.tsum_mul_left
    _ = (c • ρ.prod Measure.count) S := by
        rw [Measure.smul_apply, smul_eq_mul, Measure.prod_apply_symm hS, lintegral_count]
        rfl

/-- A measure dominated by a finite multiple of a σ-finite reference measure has a density
bounded by the multiple. -/
theorem exists_density_le {Z : Type*} [MeasurableSpace Z] (ν ref : Measure Z)
    [SigmaFinite ref] [IsFiniteMeasure ν] {c : ENNReal} (h : ν ≤ c • ref) :
    ∃ g : Z → ENNReal, Measurable g ∧ ν = ref.withDensity g ∧ ∀ᵐ z ∂ref, g z ≤ c := by
  have hac : ν ≪ ref := by
    intro s hs
    have := h s
    rw [Measure.smul_apply, smul_eq_mul, hs, mul_zero] at this
    exact le_antisymm this zero_le
  refine ⟨ν.rnDeriv ref, Measure.measurable_rnDeriv ν ref,
    (Measure.withDensity_rnDeriv_eq ν ref hac).symm, ?_⟩
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν ref)
    fun s hs _ => ?_
  calc ∫⁻ x in s, ν.rnDeriv ref x ∂ref ≤ ν s := Measure.setLIntegral_rnDeriv_le s
    _ ≤ (c • ref) s := h s
    _ = ∫⁻ _ in s, c ∂ref := by
        rw [Measure.smul_apply, smul_eq_mul, setLIntegral_const, mul_comm]

/-- The observation `(t, y(t), ⌊x(t)/p⌋)` of a labelled incidence. -/
noncomputable def obs (p : ℝ) (q : (ℕ × (Fin 5 → ℝ)) × ℝ) : (Fin 2 → ℝ) × ℤ :=
  ((![q.2, yTrace q.1.2 q.2] : Fin 2 → ℝ), ⌊xTrace q.1.2 q.2 / p⌋)

theorem measurable_obs (p : ℝ) : Measurable (obs p) := by
  unfold obs
  refine Measurable.prodMk ?_ ?_
  · refine measurable_pi_iff.mpr fun i => ?_
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]; exact measurable_snd
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact measurable_yTrace.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  · exact Int.measurable_floor.comp ((measurable_xTrace.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).div_const p)

theorem volume_finTwo_preimage {A : Set (Fin 2 → ℝ)} (hA : MeasurableSet A) :
    volume {z : ℝ × ℝ | (![z.1, z.2] : Fin 2 → ℝ) ∈ A} = volume A := by
  have hmp := (volume_preserving_finTwoArrow ℝ).symm
  have : {z : ℝ × ℝ | (![z.1, z.2] : Fin 2 → ℝ) ∈ A} = (MeasurableEquiv.finTwoArrow.symm) ⁻¹' A := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage]
    have : MeasurableEquiv.finTwoArrow.symm z = (![z.1, z.2] : Fin 2 → ℝ) := by
      ext i; fin_cases i <;> rfl
    rw [this]
  rw [this, hmp.measure_preimage hA.nullMeasurableSet]

/-- **Pure density form.** Slab bounds for a finite law on labelled incidences give an
exact-base density of its observation, bounded by the slab constant. -/
theorem exists_obs_density_le (M : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) [IsFiniteMeasure M]
    (p : ℝ) (C : ENNReal)
    (h : ∀ A : Set (ℝ × ℝ), MeasurableSet A → ∀ n : ℤ,
      M {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧ ⌊xTrace q.1.2 q.2 / p⌋ = n} ≤ C * volume A) :
    ∃ g : (Fin 2 → ℝ) × ℤ → ENNReal, Measurable g ∧
      M.map (obs p) = (volume.prod Measure.count).withDensity g ∧
      ∀ᵐ z ∂(volume.prod Measure.count), g z ≤ C := by
  refine exists_density_le _ _ (le_smul_prod_count _ _ C fun A hA n => ?_)
  rw [Measure.map_apply (measurable_obs p) (hA.prod (measurableSet_singleton n))]
  have := h {z : ℝ × ℝ | (![z.1, z.2] : Fin 2 → ℝ) ∈ A}
    (hA.preimage (MeasurableEquiv.finTwoArrow.symm.measurable)) n
  rw [volume_finTwo_preimage hA] at this
  refine le_trans (le_of_eq ?_) this
  congr 1

/-- **Joint density form** with a slope bin of width `ρ`. -/
theorem exists_obs_slope_density_le (M : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) [IsFiniteMeasure M]
    (p : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (C : ENNReal)
    (h : ∀ A : Set (ℝ × ℝ), MeasurableSet A → ∀ n m : ℤ,
      M {q | (q.2, yTrace q.1.2 q.2) ∈ A ∧ ⌊xTrace q.1.2 q.2 / p⌋ = n ∧
        q.1.2 1 ∈ Ico (m * ρ) ((m + 1) * ρ)} ≤ C * volume A) :
    ∃ G : ((Fin 2 → ℝ) × ℤ) × ℤ → ENNReal, Measurable G ∧
      M.map (fun q => (obs p q, ⌊q.1.2 1 / ρ⌋)) =
        ((volume.prod Measure.count).prod Measure.count).withDensity G ∧
      ∀ᵐ z ∂((volume.prod Measure.count).prod Measure.count), G z ≤ C := by
  have h1 : Measurable (fun q : (ℕ × (Fin 5 → ℝ)) × ℝ => q.1.2 1) := by fun_prop
  have hmeas : Measurable (fun q : (ℕ × (Fin 5 → ℝ)) × ℝ => (obs p q, ⌊q.1.2 1 / ρ⌋)) :=
    (measurable_obs p).prodMk (Int.measurable_floor.comp (h1.div_const ρ))
  have hbin : ∀ (m : ℤ) (u : ℝ), ⌊u / ρ⌋ = m ↔ u ∈ Ico (m * ρ) ((m + 1) * ρ) := by
    intro m u
    rw [Int.floor_eq_iff, mem_Ico, le_div_iff₀ hρ, div_lt_iff₀ hρ]
  refine exists_density_le _ _ (le_smul_prod_count _ _ C fun A' hA' m => ?_)
  -- inner decomposition over the hidden bin
  set ν' : Measure ((Fin 2 → ℝ) × ℤ) :=
    Measure.map Prod.fst ((M.map (fun q => (obs p q, ⌊q.1.2 1 / ρ⌋))).restrict
      (univ ×ˢ {m}))
  have hν' : ∀ B, MeasurableSet B →
      ν' B = M.map (fun q => (obs p q, ⌊q.1.2 1 / ρ⌋)) (B ×ˢ {m}) := by
    intro B hB
    rw [Measure.map_apply measurable_fst hB,
      Measure.restrict_apply (hB.preimage measurable_fst)]
    congr 1
    ext z; simp
  rw [← hν' A' hA']
  have hle : ν' ≤ C • (volume.prod Measure.count) := by
    refine le_smul_prod_count _ _ C fun A hA n => ?_
    rw [hν' _ (hA.prod (measurableSet_singleton n)),
      Measure.map_apply hmeas ((hA.prod (measurableSet_singleton n)).prod
        (measurableSet_singleton m))]
    have := h {z : ℝ × ℝ | (![z.1, z.2] : Fin 2 → ℝ) ∈ A}
      (hA.preimage (MeasurableEquiv.finTwoArrow.symm.measurable)) n m
    rw [volume_finTwo_preimage hA] at this
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext q
    simp only [mem_preimage, mem_prod, mem_singleton_iff, obs, mem_ofPred_eq, hbin]
    tauto
  exact (hle A').trans (by rw [Measure.smul_apply, smul_eq_mul])

end Submission.Obl.k4_scalar_marked_noisy_density_ceilings
