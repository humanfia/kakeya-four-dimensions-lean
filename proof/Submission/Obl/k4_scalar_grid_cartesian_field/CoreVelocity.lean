-- From this LOT obligation o230, session x0803, commit 872bba82,
-- Submission/Obl/k4_scalar_grid_cartesian_field/CoreVelocity.lean.
import Mathlib

/-!
# Two separated narrow velocity bins carried by many states

Each state (a countable label, in practice the fine physical cube) has its
velocities spread at the separation width, and its narrow velocity bins are
dominated by a palette `π`. Averaging the product palette over the states
fixes one pair of separated narrow bins both of which are charged by states
of total mass at least `μ univ / (4 Λ²)`.
-/

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open MeasureTheory Set
open scoped ENNReal

section VelocityBins

variable {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [Countable ι]

/-- A measurable countable label splits every measurable set into its classes. -/
theorem tsum_measure_inter_label {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    [Countable β] (μ : Measure Ω) (f : Ω → β) (hf : Measurable f) (s : Set Ω)
    (hs : MeasurableSet s) :
    ∑' b : β, μ (s ∩ {ω | f ω = b}) = μ s := by
  have hdisj : Pairwise (Function.onFun Disjoint fun b : β => s ∩ {ω | f ω = b}) := by
    intro b b' hbb'
    refine Set.disjoint_left.mpr ?_
    intro ω hω hω'
    exact hbb' (hω.2.symm.trans hω'.2)
  have hmeas : ∀ b : β, MeasurableSet (s ∩ {ω | f ω = b}) := fun b =>
    hs.inter (hf (measurableSet_singleton b))
  rw [← measure_iUnion hdisj hmeas]
  congr 1
  ext ω
  simp

/-- The state classes and the narrow bins of one state. -/
theorem tsum_state_bin (μ : Measure Ω) (state : Ω → ι) (hstate : Measurable state)
    (bin : Ω → ℤ) (hbin : Measurable bin) (q : ι) :
    ∑' b : ℤ, μ {ω | state ω = q ∧ bin ω = b} = μ {ω | state ω = q} := by
  have h := tsum_measure_inter_label μ bin hbin {ω | state ω = q}
    (hstate (measurableSet_singleton q))
  simpa [Set.ofPred_and] using h

theorem tsum_state (μ : Measure Ω) (state : Ω → ι) (hstate : Measurable state) :
    ∑' q : ι, μ {ω | state ω = q} = μ univ := by
  simpa using tsum_measure_inter_label μ state hstate univ MeasurableSet.univ

/-- Velocity breadth at the separation width: the narrow bins close to one
narrow bin carry at most `5/16` of the state. -/
theorem nonseparated_bins_le (μ : Measure Ω) (state : Ω → ι) (hstate : Measurable state)
    (bin sbin : Ω → ℤ) (hbin : Measurable bin) (hsbin : Measurable sbin) (m : ℤ)
    (hgeom : ∀ b₁ : ℤ, ∃ s₀ : ℤ, ∀ ω, |bin ω - b₁| < m → s₀ ≤ sbin ω ∧ sbin ω ≤ s₀ + 4)
    (hsep : ∀ q c, 16 * μ {ω | state ω = q ∧ sbin ω = c} ≤ μ {ω | state ω = q})
    (q : ι) (b₁ : ℤ) :
    16 * ∑' b₂ : ℤ, (if |b₂ - b₁| < m then μ {ω | state ω = q ∧ bin ω = b₂} else 0) ≤
      5 * μ {ω | state ω = q} := by
  classical
  obtain ⟨s₀, hs₀⟩ := hgeom b₁
  have hq : MeasurableSet {ω | state ω = q} := hstate (measurableSet_singleton q)
  -- the close narrow bins form one measurable event
  have hclose : ∑' b₂ : ℤ, (if |b₂ - b₁| < m then μ {ω | state ω = q ∧ bin ω = b₂} else 0) =
      μ ({ω | state ω = q} ∩ {ω | |bin ω - b₁| < m}) := by
    have h := tsum_measure_inter_label μ bin hbin ({ω | state ω = q} ∩ {ω | |bin ω - b₁| < m})
      (hq.inter (measurableSet_lt (hbin.sub_const b₁).abs measurable_const))
    rw [← h]
    congr 1
    ext b₂
    split_ifs with hb
    · congr 1
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by rw [h2]; exact hb⟩, h2⟩
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
    · symm
      have hempty : {ω | state ω = q} ∩ {ω | |bin ω - b₁| < m} ∩ {ω | bin ω = b₂} = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        rintro ⟨_, hlt⟩ heq
        exact hb (heq ▸ hlt)
      rw [hempty, measure_empty]
  rw [hclose]
  -- the event lies in five consecutive separation bins
  have hsub : {ω | state ω = q} ∩ {ω | |bin ω - b₁| < m} ⊆
      ⋃ c ∈ Finset.Icc s₀ (s₀ + 4), {ω | state ω = q ∧ sbin ω = c} := by
    intro ω hω
    obtain ⟨h1, h2⟩ := hs₀ ω hω.2
    simp only [mem_iUnion, Finset.mem_Icc, mem_ofPred_eq, exists_prop]
    exact ⟨sbin ω, ⟨h1, h2⟩, hω.1, rfl⟩
  have hcard : (Finset.Icc s₀ (s₀ + 4)).card = 5 := by
    rw [Int.card_Icc]
    omega
  calc
    16 * μ ({ω | state ω = q} ∩ {ω | |bin ω - b₁| < m})
        ≤ 16 * ∑ c ∈ Finset.Icc s₀ (s₀ + 4), μ {ω | state ω = q ∧ sbin ω = c} := by
          gcongr
          exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ = ∑ c ∈ Finset.Icc s₀ (s₀ + 4), 16 * μ {ω | state ω = q ∧ sbin ω = c} := by
          rw [Finset.mul_sum]
    _ ≤ ∑ _c ∈ Finset.Icc s₀ (s₀ + 4), μ {ω | state ω = q} :=
          Finset.sum_le_sum fun c _ => hsep q c
    _ = 5 * μ {ω | state ω = q} := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          norm_num


/-- Pairs of narrow bins: the product palette sums to at most one. -/
theorem tsum_tsum_mul_le_one (π : ℤ → ℝ≥0∞) (hπ : ∑' b, π b ≤ 1) :
    ∑' b₁ : ℤ, ∑' b₂ : ℤ, π b₁ * π b₂ ≤ 1 := by
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  calc (∑' b, π b) * (∑' b, π b) ≤ 1 * 1 := mul_le_mul' hπ hπ
    _ = 1 := one_mul 1

/-- Two separated narrow bins, both charged by states of mass `≥ μ univ / (4 Λ²)`. -/
theorem exists_separated_bin_pair (μ : Measure Ω) [IsFiniteMeasure μ]
    (state : Ω → ι) (hstate : Measurable state)
    (bin sbin : Ω → ℤ) (hbin : Measurable bin) (hsbin : Measurable sbin) (m : ℤ)
    (hgeom : ∀ b₁ : ℤ, ∃ s₀ : ℤ, ∀ ω, |bin ω - b₁| < m → s₀ ≤ sbin ω ∧ sbin ω ≤ s₀ + 4)
    (hsep : ∀ q c, 16 * μ {ω | state ω = q ∧ sbin ω = c} ≤ μ {ω | state ω = q})
    (π : ℤ → ℝ≥0∞) (hπ : ∑' b, π b ≤ 1) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hpal : ∀ q b, μ {ω | state ω = q ∧ bin ω = b} ≤
      ENNReal.ofReal Λ * μ {ω | state ω = q} * π b)
    (hpos : μ univ ≠ 0) :
    ∃ b₁ b₂ : ℤ, m ≤ |b₁ - b₂| ∧
      ENNReal.ofReal (1 / (4 * Λ ^ 2)) * μ univ ≤
        μ {ω | μ {ω' | state ω' = state ω ∧ bin ω' = b₁} ≠ 0 ∧
          μ {ω' | state ω' = state ω ∧ bin ω' = b₂} ≠ 0} := by
  classical
  set mq : ι → ℝ≥0∞ := fun q => μ {ω | state ω = q} with hmq_def
  set mb : ι → ℤ → ℝ≥0∞ := fun q b => μ {ω | state ω = q ∧ bin ω = b} with hmb_def
  have hmq_fin : ∀ q, mq q ≠ ⊤ := fun q => measure_ne_top μ _
  -- the product-palette weight of the separated positive pairs of one state
  set T : ι → ℝ≥0∞ := fun q => ∑' b₁ : ℤ, ∑' b₂ : ℤ,
    (if m ≤ |b₁ - b₂| ∧ mb q b₁ ≠ 0 ∧ mb q b₂ ≠ 0 then π b₁ * π b₂ else 0) with hT_def
  -- (a) separated narrow bins carry `11/16` of the state, squared
  have hsepmass : ∀ q, 11 * mq q ^ 2 ≤
      16 * ∑' b₁ : ℤ, ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₁ * mb q b₂ else 0) := by
    intro q
    have hrow : ∀ b₁, 11 * mq q ≤
        16 * ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₂ else 0) := by
      intro b₁
      have hsplit : ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₂ else 0) +
          ∑' b₂ : ℤ, (if |b₂ - b₁| < m then mb q b₂ else 0) = mq q := by
        rw [← ENNReal.tsum_add]
        refine Eq.trans ?_ (tsum_state_bin μ state hstate bin hbin q)
        refine tsum_congr fun b₂ => ?_
        rw [abs_sub_comm b₁ b₂]
        by_cases h : m ≤ |b₂ - b₁|
        · simp [h, not_lt.mpr h, hmb_def]
        · simp [h, lt_of_not_ge h, hmb_def]
      have hnon := nonseparated_bins_le μ state hstate bin sbin hbin hsbin m hgeom hsep q b₁
      have h16 : 16 * mq q = 16 * ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₂ else 0) +
          16 * ∑' b₂ : ℤ, (if |b₂ - b₁| < m then mb q b₂ else 0) := by
        rw [← mul_add, hsplit]
      have hfin5 : (5 : ℝ≥0∞) * mq q ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (hmq_fin q)
      have : 11 * mq q + 5 * mq q ≤
          16 * ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₂ else 0) + 5 * mq q := by
        calc 11 * mq q + 5 * mq q = 16 * mq q := by rw [← add_mul]; norm_num
          _ = _ := h16
          _ ≤ _ := add_le_add le_rfl hnon
      exact (ENNReal.add_le_add_iff_right hfin5).mp this
    calc 11 * mq q ^ 2 = ∑' b₁ : ℤ, mb q b₁ * (11 * mq q) := by
          rw [ENNReal.tsum_mul_right, tsum_state_bin μ state hstate bin hbin q]; ring
      _ ≤ ∑' b₁ : ℤ, mb q b₁ *
            (16 * ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₂ else 0)) :=
          ENNReal.tsum_le_tsum fun b₁ => mul_le_mul' le_rfl (hrow b₁)
      _ = 16 * ∑' b₁ : ℤ, ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₁ * mb q b₂ else 0) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun b₁ => ?_
          calc mb q b₁ * (16 * ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₂ else 0))
              = ∑' b₂ : ℤ, mb q b₁ * (16 * (if m ≤ |b₁ - b₂| then mb q b₂ else 0)) := by
                rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
            _ = 16 * ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₁ * mb q b₂ else 0) := by
                rw [← ENNReal.tsum_mul_left]
                exact tsum_congr fun b₂ => by split_ifs <;> ring
  -- (b) palette domination turns this into product-palette weight
  have hpair : ∀ q, 11 * mq q ≤ 16 * ENNReal.ofReal (Λ ^ 2) * (T q * mq q) := by
    intro q
    by_cases hq0 : mq q = 0
    · simp [hq0]
    have hdom : ∑' b₁ : ℤ, ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then mb q b₁ * mb q b₂ else 0) ≤
        (ENNReal.ofReal Λ * mq q) ^ 2 * T q := by
      rw [hT_def]
      simp only
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun b₁ => ?_
      rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun b₂ => ?_
      by_cases hs : m ≤ |b₁ - b₂|
      · by_cases h1 : mb q b₁ = 0
        · simp [hs, h1]
        by_cases h2 : mb q b₂ = 0
        · simp [hs, h2]
        simp only [hs, h1, h2, ne_eq, not_false_eq_true, and_self, if_true]
        calc mb q b₁ * mb q b₂ ≤ (ENNReal.ofReal Λ * mq q * π b₁) *
              (ENNReal.ofReal Λ * mq q * π b₂) := mul_le_mul' (hpal q b₁) (hpal q b₂)
          _ = (ENNReal.ofReal Λ * mq q) ^ 2 * (π b₁ * π b₂) := by ring
      · simp [hs]
    have h2 : 11 * mq q ^ 2 ≤ 16 * ((ENNReal.ofReal Λ * mq q) ^ 2 * T q) :=
      (hsepmass q).trans (mul_le_mul' le_rfl hdom)
    have hΛsq : (ENNReal.ofReal Λ) ^ 2 = ENNReal.ofReal (Λ ^ 2) := by
      rw [ENNReal.ofReal_pow (by linarith)]
    -- cancel one factor `mq q`
    have h3 : mq q * (11 * mq q) ≤ mq q * (16 * ENNReal.ofReal (Λ ^ 2) * (T q * mq q)) := by
      calc mq q * (11 * mq q) = 11 * mq q ^ 2 := by ring
        _ ≤ 16 * ((ENNReal.ofReal Λ * mq q) ^ 2 * T q) := h2
        _ = mq q * (16 * ENNReal.ofReal (Λ ^ 2) * (T q * mq q)) := by
          rw [← hΛsq]; ring
    exact (ENNReal.mul_le_mul_iff_right hq0 (hmq_fin q)).mp h3
  -- the mass of the states charging both bins of a pair
  set good : ℤ → ℤ → Set Ω := fun b₁ b₂ =>
    {ω | mb (state ω) b₁ ≠ 0 ∧ mb (state ω) b₂ ≠ 0} with hgood_def
  have hgood_mass : ∀ b₁ b₂, μ (good b₁ b₂) =
      ∑' q : ι, (if mb q b₁ ≠ 0 ∧ mb q b₂ ≠ 0 then mq q else 0) := by
    intro b₁ b₂
    have hmeas : MeasurableSet (good b₁ b₂) := by
      have : good b₁ b₂ = state ⁻¹' {q | mb q b₁ ≠ 0 ∧ mb q b₂ ≠ 0} := rfl
      rw [this]
      exact hstate (Set.to_countable _).measurableSet
    rw [← tsum_measure_inter_label μ state hstate (good b₁ b₂) hmeas]
    refine tsum_congr fun q => ?_
    split_ifs with hq
    · congr 1
      ext ω
      simp only [hgood_def, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨h ▸ hq, h⟩
    · have hempty : good b₁ b₂ ∩ {ω | state ω = q} = ∅ := by
        ext ω
        simp only [hgood_def, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false,
          not_and]
        intro hω heq
        exact hq (heq ▸ hω)
      rw [hempty, measure_empty]
  -- (c) summing over the states
  have hsum : 11 * μ univ ≤ 16 * ENNReal.ofReal (Λ ^ 2) *
      ∑' b₁ : ℤ, ∑' b₂ : ℤ, (if m ≤ |b₁ - b₂| then π b₁ * π b₂ * μ (good b₁ b₂) else 0) := by
    calc 11 * μ univ = ∑' q : ι, 11 * mq q := by
          rw [ENNReal.tsum_mul_left, tsum_state μ state hstate]
      _ ≤ ∑' q : ι, 16 * ENNReal.ofReal (Λ ^ 2) * (T q * mq q) :=
          ENNReal.tsum_le_tsum hpair
      _ = 16 * ENNReal.ofReal (Λ ^ 2) * ∑' q : ι, T q * mq q := ENNReal.tsum_mul_left
      _ = _ := by
          congr 1
          simp_rw [hgood_mass, hT_def]
          calc ∑' q : ι, (∑' b₁ : ℤ, ∑' b₂ : ℤ,
                (if m ≤ |b₁ - b₂| ∧ mb q b₁ ≠ 0 ∧ mb q b₂ ≠ 0 then π b₁ * π b₂ else 0)) * mq q
              = ∑' q : ι, ∑' b₁ : ℤ, ∑' b₂ : ℤ,
                (if m ≤ |b₁ - b₂| ∧ mb q b₁ ≠ 0 ∧ mb q b₂ ≠ 0 then π b₁ * π b₂ else 0) * mq q := by
                refine tsum_congr fun q => ?_
                rw [← ENNReal.tsum_mul_right]
                exact tsum_congr fun b₁ => by rw [← ENNReal.tsum_mul_right]
            _ = ∑' b₁ : ℤ, ∑' b₂ : ℤ, ∑' q : ι,
                (if m ≤ |b₁ - b₂| ∧ mb q b₁ ≠ 0 ∧ mb q b₂ ≠ 0 then π b₁ * π b₂ else 0) * mq q := by
                rw [ENNReal.tsum_comm]
                exact tsum_congr fun b₁ => by rw [ENNReal.tsum_comm]
            _ = _ := by
                refine tsum_congr fun b₁ => tsum_congr fun b₂ => ?_
                by_cases hs : m ≤ |b₁ - b₂|
                · simp only [hs, if_true, true_and]
                  rw [← ENNReal.tsum_mul_left]
                  refine tsum_congr fun q => ?_
                  split_ifs <;> simp
                · simp [hs]
  -- (d) a heavy separated pair exists
  by_contra hno
  simp only [not_exists, not_and, not_le] at hno
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / (4 * Λ ^ 2)) * μ univ with hc_def
  have hbound : ∑' b₁ : ℤ, ∑' b₂ : ℤ,
      (if m ≤ |b₁ - b₂| then π b₁ * π b₂ * μ (good b₁ b₂) else 0) ≤ c := by
    calc _ ≤ ∑' b₁ : ℤ, ∑' b₂ : ℤ, π b₁ * π b₂ * c := by
          refine ENNReal.tsum_le_tsum fun b₁ => ENNReal.tsum_le_tsum fun b₂ => ?_
          split_ifs with hs
          · exact mul_le_mul' le_rfl (hno b₁ b₂ hs).le
          · exact zero_le
      _ = (∑' b₁ : ℤ, ∑' b₂ : ℤ, π b₁ * π b₂) * c := by
          simp_rw [ENNReal.tsum_mul_right]
      _ ≤ 1 * c := mul_le_mul' (tsum_tsum_mul_le_one π hπ) le_rfl
      _ = c := one_mul c
  have hΛpos : 0 < Λ := by linarith
  have hkey : 16 * ENNReal.ofReal (Λ ^ 2) * c = 4 * μ univ := by
    have h4 : (16 : ℝ≥0∞) * ENNReal.ofReal (Λ ^ 2) * ENNReal.ofReal (1 / (4 * Λ ^ 2)) = 4 := by
      rw [show (16 : ℝ≥0∞) = ENNReal.ofReal 16 by simp, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      rw [show (16 : ℝ) * Λ ^ 2 * (1 / (4 * Λ ^ 2)) = 4 by field_simp; ring]
      simp
    rw [hc_def, ← mul_assoc, h4]
  have h11 : 11 * μ univ ≤ 4 * μ univ := by
    calc 11 * μ univ ≤ _ := hsum
      _ ≤ 16 * ENNReal.ofReal (Λ ^ 2) * c := mul_le_mul' le_rfl hbound
      _ = 4 * μ univ := hkey
  have hfin : μ univ ≠ ⊤ := measure_ne_top μ univ
  have : (11 : ℝ≥0∞) ≤ 4 := (ENNReal.mul_le_mul_iff_left hpos hfin).mp h11
  norm_num at this

end VelocityBins

end Submission.Obl.k4_scalar_grid_cartesian_field
