import Mathlib

/-!
# Comparing densities of two discrete refinements of one observation

Two observations share a continuous coordinate `z` and carry countable labels
`ℓ₁`, `ℓ₂`. Their label slices have densities `g₁`, `g₂`. When every point has
compatible labels for a relation `R`, and every `ℓ₂`-label is compatible with at
most `D` labels `ℓ₁`, the first density falls below `ε` times the second only
on a set of mass at most `ε * D` times the total mass.

No common refinement density is needed. This is the comparison used for the
non-nested bins `⌊x / N ^ (-r)⌋` at two different depths.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_grid_density_extension

open MeasureTheory Set
open scoped ENNReal

open Classical in
/-- The low-density comparison for two label refinements of a common observation. -/
theorem relation_low_density_mass {Ω Z L₁ L₂ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] [Countable L₁] [Countable L₂]
    (μ : Measure Ω) (ρ : Measure Z) (z : Ω → Z) (ℓ₁ : Ω → L₁) (ℓ₂ : Ω → L₂)
    (hℓ₂ : ∀ b, MeasurableSet {p | ℓ₂ p = b})
    (g₁ : Z → L₁ → ℝ≥0∞) (g₂ : Z → L₂ → ℝ≥0∞)
    (hg₁ : ∀ a, Measurable (fun x => g₁ x a)) (hg₂ : ∀ b, Measurable (fun x => g₂ x b))
    (h₁ : ∀ a S, MeasurableSet S → μ {p | ℓ₁ p = a ∧ z p ∈ S} = ∫⁻ x in S, g₁ x a ∂ρ)
    (h₂ : ∀ b S, MeasurableSet S → μ {p | ℓ₂ p = b ∧ z p ∈ S} = ∫⁻ x in S, g₂ x b ∂ρ)
    (R : L₁ → L₂ → Prop) (hR : ∀ᵐ p ∂μ, R (ℓ₁ p) (ℓ₂ p))
    (D : ℝ≥0∞) (hD : ∀ b, ∑' a, (if R a b then (1 : ℝ≥0∞) else 0) ≤ D)
    (ε : ℝ≥0∞) :
    μ {p | g₁ (z p) (ℓ₁ p) < ε * g₂ (z p) (ℓ₂ p)} ≤ ε * D * μ univ := by
  classical
  let S : L₁ → L₂ → Set Z := fun a b => {x | g₁ x a < ε * g₂ x b}
  have hS (a : L₁) (b : L₂) : MeasurableSet (S a b) :=
    measurableSet_lt (hg₁ a) (measurable_const.mul (hg₂ b))
  let T : L₁ × L₂ → Set Ω := fun ab =>
    if R ab.1 ab.2 then {p | ℓ₁ p = ab.1 ∧ z p ∈ S ab.1 ab.2} ∩ {p | ℓ₂ p = ab.2} else ∅
  have hsub : {p | g₁ (z p) (ℓ₁ p) < ε * g₂ (z p) (ℓ₂ p)} ≤ᵐ[μ] ⋃ ab, T ab := by
    filter_upwards [hR] with p hp hbad
    refine mem_iUnion.mpr ⟨(ℓ₁ p, ℓ₂ p), ?_⟩
    simp only [T, hp, ite_true]
    exact ⟨⟨rfl, hbad⟩, rfl⟩
  have hslice (b : L₂) : μ {p | ℓ₂ p = b} = ∫⁻ x, g₂ x b ∂ρ := by
    have h := h₂ b univ MeasurableSet.univ
    simp only [mem_univ, and_true, Measure.restrict_univ] at h
    exact h
  have hT (ab : L₁ × L₂) :
      μ (T ab) ≤ if R ab.1 ab.2 then ε * μ {p | ℓ₂ p = ab.2} else 0 := by
    obtain ⟨a, b⟩ := ab
    by_cases hab : R a b
    · simp only [T, hab, ite_true]
      calc
        μ ({p | ℓ₁ p = a ∧ z p ∈ S a b} ∩ {p | ℓ₂ p = b}) ≤
            μ {p | ℓ₁ p = a ∧ z p ∈ S a b} := measure_mono inter_subset_left
        _ = ∫⁻ x in S a b, g₁ x a ∂ρ := h₁ a _ (hS a b)
        _ ≤ ∫⁻ x in S a b, ε * g₂ x b ∂ρ := setLIntegral_mono' (hS a b) (fun x hx => hx.le)
        _ = ε * ∫⁻ x in S a b, g₂ x b ∂ρ := lintegral_const_mul _ (hg₂ b)
        _ ≤ ε * ∫⁻ x, g₂ x b ∂ρ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
        _ = ε * μ {p | ℓ₂ p = b} := by rw [hslice b]
    · simp [T, hab]
  have hdisj : Pairwise (Function.onFun Disjoint (fun b : L₂ => {p : Ω | ℓ₂ p = b})) := by
    intro b b' hbb'
    refine Set.disjoint_left.mpr ?_
    intro p hp hp'
    exact hbb' (hp.symm.trans hp')
  have htotal : ∑' b, μ {p | ℓ₂ p = b} = μ univ := by
    rw [← measure_iUnion hdisj hℓ₂]
    congr 1
    ext p
    simp
  calc
    μ {p | g₁ (z p) (ℓ₁ p) < ε * g₂ (z p) (ℓ₂ p)} ≤ μ (⋃ ab, T ab) := measure_mono_ae hsub
    _ ≤ ∑' ab, μ (T ab) := measure_iUnion_le _
    _ ≤ ∑' ab : L₁ × L₂, (if R ab.1 ab.2 then ε * μ {p | ℓ₂ p = ab.2} else 0) :=
      ENNReal.tsum_le_tsum hT
    _ = ∑' b, ∑' a, (if R a b then ε * μ {p | ℓ₂ p = b} else 0) := by
      rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ = ∑' b, (∑' a, (if R a b then (1 : ℝ≥0∞) else 0)) * (ε * μ {p | ℓ₂ p = b}) := by
      apply tsum_congr
      intro b
      rw [← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro a
      split_ifs <;> simp
    _ ≤ ∑' b, D * (ε * μ {p | ℓ₂ p = b}) :=
      ENNReal.tsum_le_tsum fun b => mul_le_mul' (hD b) le_rfl
    _ = ε * D * μ univ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, htotal]
      ring

open Classical in
/-- A sum of indicator ones is bounded by the size of any finite set containing
the indicated set. -/
theorem tsum_ite_one_le_card {L : Type*} (P : L → Prop) (F : Finset L)
    (hF : ∀ a, P a → a ∈ F) :
    ∑' a, (if P a then (1 : ℝ≥0∞) else 0) ≤ F.card := by
  classical
  calc
    ∑' a, (if P a then (1 : ℝ≥0∞) else 0) ≤ ∑' a, (if a ∈ F then (1 : ℝ≥0∞) else 0) := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : P a
      · simp [ha, hF a ha]
      · simp [ha]
    _ = ∑ a ∈ F, (if a ∈ F then (1 : ℝ≥0∞) else 0) := by
      apply tsum_eq_sum
      intro a ha
      simp [ha]
    _ = F.card := by
      rw [Finset.sum_ite_mem, Finset.inter_self]
      simp

/-- Two floors of the same real number at a coarse width `w` and a finer width
`w'` are compatible. -/
def FloorCompatible (w w' : ℝ) (a b : ℤ) : Prop :=
  ∃ x : ℝ, ⌊x / w⌋ = a ∧ ⌊x / w'⌋ = b

/-- Pairs of label pairs compatible coordinatewise. -/
def PairCompatible (w w' v v' : ℝ) (a b : ℤ × ℤ) : Prop :=
  FloorCompatible w w' a.1 b.1 ∧ FloorCompatible v v' a.2 b.2

/-- A fine bin meets at most two coarse bins. -/
theorem floorCompatible_coarse_mem {w w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w) (b : ℤ) :
    ∀ a, FloorCompatible w w' a b →
      a ∈ ({⌊(b : ℝ) * w' / w⌋, ⌊(b : ℝ) * w' / w⌋ + 1} : Finset ℤ) := by
  intro a ⟨x, hxa, hxb⟩
  have hw : 0 < w := hw'.trans_le hww'
  have hb₁ : (b : ℝ) ≤ x / w' := by rw [← hxb]; exact Int.floor_le _
  have hb₂ : x / w' < (b : ℝ) + 1 := by rw [← hxb]; exact Int.lt_floor_add_one _
  have hx₁ : (b : ℝ) * w' ≤ x := by rwa [le_div_iff₀ hw'] at hb₁
  have hx₂ : x < ((b : ℝ) + 1) * w' := by rwa [div_lt_iff₀ hw'] at hb₂
  have hlo : (b : ℝ) * w' / w ≤ x / w := div_le_div_of_nonneg_right hx₁ hw.le
  have hhi : x / w < (b : ℝ) * w' / w + 1 := by
    rw [div_lt_iff₀ hw, add_mul, div_mul_cancel₀ _ hw.ne', one_mul]
    nlinarith
  have h₁ : ⌊(b : ℝ) * w' / w⌋ ≤ a := by rw [← hxa]; exact Int.floor_mono hlo
  have h₂ : a ≤ ⌊(b : ℝ) * w' / w⌋ + 1 := by
    rw [← hxa]
    have h := Int.floor_mono hhi.le
    rwa [Int.floor_add_one] at h
  have : a = ⌊(b : ℝ) * w' / w⌋ ∨ a = ⌊(b : ℝ) * w' / w⌋ + 1 := by omega
  rcases this with h | h <;> simp [h]

/-- A coarse bin meets at most `w / w' + 2` fine bins. -/
theorem floorCompatible_fine_mem {w w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w) (a : ℤ) :
    ∀ b, FloorCompatible w w' a b →
      b ∈ Finset.Icc ⌊(a : ℝ) * w / w'⌋ ⌊((a : ℝ) + 1) * w / w'⌋ := by
  intro b ⟨x, hxa, hxb⟩
  have hw : 0 < w := hw'.trans_le hww'
  have ha₁ : (a : ℝ) ≤ x / w := by rw [← hxa]; exact Int.floor_le _
  have ha₂ : x / w < (a : ℝ) + 1 := by rw [← hxa]; exact Int.lt_floor_add_one _
  have hx₁ : (a : ℝ) * w ≤ x := by rwa [le_div_iff₀ hw] at ha₁
  have hx₂ : x < ((a : ℝ) + 1) * w := by rwa [div_lt_iff₀ hw] at ha₂
  rw [Finset.mem_Icc, ← hxb]
  exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hx₁ hw'.le),
    Int.floor_mono (div_le_div_of_nonneg_right hx₂.le hw'.le)⟩

theorem card_fine_window_le {w w' : ℝ} (hw' : 0 < w') (hww' : w' ≤ w) (a : ℤ) :
    ((Finset.Icc ⌊(a : ℝ) * w / w'⌋ ⌊((a : ℝ) + 1) * w / w'⌋).card : ℝ) ≤ w / w' + 2 := by
  have hw : 0 < w := hw'.trans_le hww'
  rw [Int.card_Icc]
  set lo := ⌊(a : ℝ) * w / w'⌋
  set hi := ⌊((a : ℝ) + 1) * w / w'⌋
  have hlo : (a : ℝ) * w / w' - 1 < lo := Int.sub_one_lt_floor _
  have hhi : (hi : ℝ) ≤ ((a : ℝ) + 1) * w / w' := Int.floor_le _
  have hdiff : ((a : ℝ) + 1) * w / w' = (a : ℝ) * w / w' + w / w' := by
    rw [add_mul, one_mul, add_div]
  have hmono : (a : ℝ) * w / w' ≤ ((a : ℝ) + 1) * w / w' := by
    rw [hdiff]; linarith [div_pos hw hw']
  have hle : lo ≤ hi := Int.floor_mono hmono
  have hnat : ((hi + 1 - lo).toNat : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) := by
    have : 0 ≤ hi + 1 - lo := by omega
    exact_mod_cast Int.toNat_of_nonneg this
  rw [hnat]
  push_cast
  linarith

end Submission.Obl.k4_scalar_grid_density_extension
