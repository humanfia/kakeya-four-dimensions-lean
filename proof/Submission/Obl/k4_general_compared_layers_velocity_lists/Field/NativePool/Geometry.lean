-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.NativePool.Geometry; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Adapted from files of this checkout:
   * `physRegion` and its lemmas are the physical analogue (no frame time map) of
     `ListFrame.region`, `measurableSet_region`, `region_disjoint` in `Lists/PoolSetup.lean`;
   * `loss_numeric_half` is `loss_numeric` of `Confine/Numerics.lean` with target `ϑ / 2`, and
     `base_numeric` follows the proof of `osc_numeric` there;
   * `Valid.physBad_parent_le` is the parent-block part of the proof of
     `ListFrame.law_physBad_le` (`Confine/Loss.lean`), stated for the original incidence measure
     on one original true block instead of the law of a list frame. -/
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.NativePool.Abstract
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Setup
import Submission.Obl.k4_general_compared_layers_velocity_lists.Confine.Deep

/-!
# Geometry of native fine states on deep original labels

* Physical regions of true labels (trajectory class times the half-open time piece).
* The normalized block coordinates `(τ, ζ, U)` of an original block vary by at most
  `3 K D / blockWidth` when the original base coordinates vary by at most `D`; together with a
  signal variation of at most `δs`, two incidences then have native states within one step
  of each other in each coordinate.
* The physical bad set of the native-signal groups at an intermediate depth has original
  mass at most `K η` times the reference of an original block, inside that block.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_wide_velocity_lists_scalar_preparation (floor_div_near dyadic_Ico_disjoint)
open Submission.Obl.k4_general_parent_projected_layers (parentFilling)

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α]

/-- The physical region of a true label: its trajectory class, at times in the half-open
piece of its dyadic block. -/
def physRegion (p : Parent α) (k : ℕ) (s : ℝ) (i : Fin (p.n k s)) : Set (α × ℝ) :=
  {ω | ω.1 ∈ p.B k s i ∧ ω.2 ∈ Ico (((p.j k s i : ℕ) : ℝ) / 2 ^ p.T k s)
      ((((p.j k s i : ℕ) : ℝ) + 1) / 2 ^ p.T k s)}

theorem measurableSet_physRegion {p : Parent α} {k : ℕ} {s : ℝ}
    (hB : ∀ i, MeasurableSet (p.B k s i)) (i : Fin (p.n k s)) :
    MeasurableSet (p.physRegion k s i) :=
  ((hB i).preimage measurable_fst).inter (measurableSet_Ico.preimage measurable_snd)

theorem physRegion_disjoint {p : Parent α} {k : ℕ} {s : ℝ}
    (hBA : ∀ i, p.B k s i ⊆ p.A k s i)
    (hdisj : ∀ i i', i ≠ i' → p.j k s i = p.j k s i' → Disjoint (p.A k s i) (p.A k s i')) :
    Pairwise (fun i i' => Disjoint (p.physRegion k s i) (p.physRegion k s i')) := by
  intro i i' hii'
  rw [Set.disjoint_left]
  intro ω hω hω'
  by_cases hj : p.j k s i = p.j k s i'
  · exact Set.disjoint_left.mp (hdisj i i' hii' hj) (hBA i hω.1) (hBA i' hω'.1)
  · exact Set.disjoint_left.mp (dyadic_Ico_disjoint (fun h => hj (Fin.ext h))) hω.2 hω'.2

theorem physRegion_subset {p : Parent α} {k : ℕ} {s : ℝ} (i : Fin (p.n k s)) :
    p.physRegion k s i ⊆ p.B k s i ×ˢ block (p.T k s) (p.j k s i) :=
  fun _ hω => ⟨hω.1, Ico_subset_Icc_self hω.2⟩

theorem mem_physRegion {p : Parent α} {k : ℕ} {s : ℝ} {i : Fin (p.n k s)} {ω : α × ℝ}
    (hB : ω.1 ∈ p.B k s i) (hI : ω.2 ∈ block (p.T k s) (p.j k s i))
    (hD : ω.2 ∉ dyadicTimes (p.T k s)) : ω ∈ p.physRegion k s i :=
  ⟨hB, mem_Ico_of_mem_block hI hD⟩

/-- The normalized block coordinates of an original block vary by at most `3 K D` transverse
widths when the original base coordinates vary by at most `D`. -/
theorem normalized_diff_le (p : Parent α) (k : ℕ) (r : ℝ) (Q : Fin (p.n k r))
    (hK : 1 ≤ p.K k) (hc : ∀ e, |p.c k r Q e| ≤ p.K k)
    (hq : 0 < p.blockLen k r) (hg : 0 < p.N k ^ (-p.ℓ * r))
    (hg1 : p.N k ^ (-p.ℓ * r) ≤ 1)
    {ω ω₀ : α × ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hbase : ∀ e : Fin 3, |p.base k ω.1 ω.2 e - p.base k ω₀.1 ω₀.2 e| ≤ D) :
    |p.tauN k r Q ω - p.tauN k r Q ω₀| ≤ 3 * p.K k * D / p.blockWidth k r ∧
    |p.zetaN k r Q ω - p.zetaN k r Q ω₀| ≤ 3 * p.K k * D / p.blockWidth k r ∧
    |p.uN k r Q ω - p.uN k r Q ω₀| ≤ 3 * p.K k * D / p.blockWidth k r := by
  have h0 : |ω.2 - ω₀.2| ≤ D := hbase 0
  have h1 : |p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1| ≤ D := hbase 1
  have h2 : |p.x k ω.1 ω.2 2 - p.x k ω₀.1 ω₀.2 2| ≤ D := hbase 2
  have hw : p.blockWidth k r = p.blockLen k r * p.N k ^ (-p.ℓ * r) := rfl
  have hK0 : 0 ≤ p.K k := by linarith
  have hqg : 0 < p.blockLen k r * p.N k ^ (-p.ℓ * r) := mul_pos hq hg
  have h3KD : 0 ≤ 3 * p.K k * D := mul_nonneg (by linarith) hD
  have hD3 : D ≤ 3 * p.K k * D := by nlinarith
  have hover_q : ∀ X : ℝ, |X| ≤ 3 * p.K k * D →
      |X / p.blockLen k r| ≤ 3 * p.K k * D / p.blockWidth k r := by
    intro X hX
    rw [abs_div, abs_of_pos hq, hw]
    calc |X| / p.blockLen k r ≤ 3 * p.K k * D / p.blockLen k r :=
          div_le_div_of_nonneg_right hX hq.le
      _ ≤ 3 * p.K k * D / (p.blockLen k r * p.N k ^ (-p.ℓ * r)) := by
          apply div_le_div_of_nonneg_left h3KD hqg
          calc p.blockLen k r * p.N k ^ (-p.ℓ * r) ≤ p.blockLen k r * 1 :=
                mul_le_mul_of_nonneg_left hg1 hq.le
            _ = p.blockLen k r := mul_one _
  have hover_w : ∀ X : ℝ, |X| ≤ 3 * p.K k * D →
      |X / p.blockWidth k r| ≤ 3 * p.K k * D / p.blockWidth k r := by
    intro X hX
    rw [hw, abs_div, abs_of_pos hqg]
    exact div_le_div_of_nonneg_right hX hqg.le
  refine ⟨?_, ?_, ?_⟩
  · have he : p.tauN k r Q ω - p.tauN k r Q ω₀ = (ω.2 - ω₀.2) / p.blockLen k r := by
      unfold tauN
      ring
    rw [he]
    exact hover_q _ (h0.trans hD3)
  · have he : p.zetaN k r Q ω - p.zetaN k r Q ω₀ =
        ((p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1) - p.c k r Q 1 * (ω.2 - ω₀.2)) /
          p.blockLen k r := by
      unfold zetaN
      ring
    rw [he]
    apply hover_q
    have hc1 : |p.c k r Q 1 * (ω.2 - ω₀.2)| ≤ p.K k * D := by
      rw [abs_mul]
      exact mul_le_mul (hc 1) h0 (abs_nonneg _) hK0
    calc _ ≤ |p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1| + |p.c k r Q 1 * (ω.2 - ω₀.2)| :=
          abs_sub _ _
      _ ≤ D + p.K k * D := add_le_add h1 hc1
      _ ≤ 3 * p.K k * D := by nlinarith
  · have he : p.uN k r Q ω - p.uN k r Q ω₀ =
        ((p.x k ω.1 ω.2 2 - p.x k ω₀.1 ω₀.2 2) - p.c k r Q 3 * (ω.2 - ω₀.2) -
          p.c k r Q 4 * (p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1)) / p.blockWidth k r := by
      unfold uN tiltY
      ring
    rw [he]
    apply hover_w
    have hc3 : |p.c k r Q 3 * (ω.2 - ω₀.2)| ≤ p.K k * D := by
      rw [abs_mul]
      exact mul_le_mul (hc 3) h0 (abs_nonneg _) hK0
    have hc4 : |p.c k r Q 4 * (p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1)| ≤ p.K k * D := by
      rw [abs_mul]
      exact mul_le_mul (hc 4) h1 (abs_nonneg _) hK0
    calc _ ≤ |(p.x k ω.1 ω.2 2 - p.x k ω₀.1 ω₀.2 2) - p.c k r Q 3 * (ω.2 - ω₀.2)| +
          |p.c k r Q 4 * (p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1)| := abs_sub _ _
      _ ≤ (|p.x k ω.1 ω.2 2 - p.x k ω₀.1 ω₀.2 2| + |p.c k r Q 3 * (ω.2 - ω₀.2)|) +
          |p.c k r Q 4 * (p.x k ω.1 ω.2 1 - p.x k ω₀.1 ω₀.2 1)| := by
          gcongr
          exact abs_sub _ _
      _ ≤ (D + p.K k * D) + p.K k * D := add_le_add (add_le_add h2 hc3) hc4
      _ ≤ 3 * p.K k * D := by nlinarith

/-- Two incidences whose normalized block coordinates differ by at most `δb` and whose native
signals differ by at most `δs` have native states within one step in each coordinate. -/
theorem nativeState_mem_nativeBox (p : Parent α) (k : ℕ) (r : ℝ) (Q : Fin (p.n k r))
    {δb δs : ℝ} (hδb : 0 < δb) (hδs : 0 < δs) {ω ω₀ : α × ℝ}
    (hτ : |p.tauN k r Q ω - p.tauN k r Q ω₀| ≤ δb)
    (hζ : |p.zetaN k r Q ω - p.zetaN k r Q ω₀| ≤ δb)
    (hu : |p.uN k r Q ω - p.uN k r Q ω₀| ≤ δb)
    (hs : |p.signal k ω.1 ω.2 - p.signal k ω₀.1 ω₀.2| ≤ δs) :
    p.nativeState k r Q δb δs ω ∈ NativePool.nativeBox (p.nativeState k r Q δb δs ω₀) := by
  apply NativePool.mem_nativeBox
  intro e
  fin_cases e
  · exact floor_div_near hδb hτ
  · exact floor_div_near hδb hζ
  · exact floor_div_near hδb hu
  · exact floor_div_near hδs hs

end Parent

/-- The loss of the two groups at depth `s` is at most `ϑ / 2` once `N ^ (-s) ≤ ϑ / 2`.
(`loss_numeric` of `Confine/Numerics.lean` with target `ϑ / 2`.) -/
theorem loss_numeric_half {N K s ϑ : ℝ} (hN : 0 < N) (hK : 1 ≤ K) (h : N ^ (-s) ≤ ϑ / 2) :
    ENNReal.ofReal K * ENNReal.ofReal ((parentFilling K (N ^ (-s)))⁻¹) ≤
      ENNReal.ofReal (ϑ / 2) := by
  have hK0 : 0 < K := by linarith
  rw [← ENNReal.ofReal_mul hK0.le]
  apply ENNReal.ofReal_le_ofReal
  have hNs : 0 < N ^ (-s) := Real.rpow_pos_of_pos hN _
  have hpf : (parentFilling K (N ^ (-s)))⁻¹ = N ^ (-s) / (3000000 * K ^ 20) := by
    unfold parentFilling
    rw [inv_div]
  rw [hpf]
  have hK20 : K ≤ 3000000 * K ^ 20 := by
    have : 1 ≤ K ^ 19 := one_le_pow₀ hK
    nlinarith
  have h1 : K * (N ^ (-s) / (3000000 * K ^ 20)) ≤ N ^ (-s) := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hK20 hNs.le]
  linarith

/-- Deep labels at depth `t` resolve the normalized base cells of mesh `N ^ (-βb)` of an
original block at depth `r`. -/
theorem base_numeric {N K Qr Qt κ ℓ r t βb : ℝ} (hN : 0 < N) (hK : 1 ≤ K)
    (hQr0 : 0 < Qr) (hQr : Qr ≤ K * N ^ (κ * r)) (hQt : N ^ (κ * t) / K ≤ Qt)
    (h : 18 * K ^ 5 * N ^ (κ * r + ℓ * r - κ * t) < N ^ (-βb)) :
    3 * K * (6 * K ^ 2 * Qt⁻¹) / (Qr⁻¹ * N ^ (-ℓ * r)) ≤ N ^ (-βb) := by
  have hK0 : 0 < K := by linarith
  have hNkt : 0 < N ^ (κ * t) := Real.rpow_pos_of_pos hN _
  have hQt0 : 0 < Qt := lt_of_lt_of_le (by positivity) hQt
  have hQtinv : Qt⁻¹ ≤ K * N ^ (-(κ * t)) := by
    have h1 := inv_anti₀ (by positivity) hQt
    rw [inv_div] at h1
    rw [Real.rpow_neg hN.le]
    calc Qt⁻¹ ≤ K / N ^ (κ * t) := h1
      _ = K * (N ^ (κ * t))⁻¹ := div_eq_mul_inv _ _
  have hNl : 0 < N ^ (ℓ * r) := Real.rpow_pos_of_pos hN _
  have hfrac : 3 * K * (6 * K ^ 2 * Qt⁻¹) / (Qr⁻¹ * N ^ (-ℓ * r)) =
      18 * K ^ 3 * Qr * Qt⁻¹ * N ^ (ℓ * r) := by
    rw [neg_mul, Real.rpow_neg hN.le]
    field_simp
    ring
  have hpow : N ^ (κ * r) * N ^ (-(κ * t)) * N ^ (ℓ * r) = N ^ (κ * r + ℓ * r - κ * t) := by
    rw [← Real.rpow_add hN, ← Real.rpow_add hN]
    congr 1
    ring
  rw [hfrac]
  calc 18 * K ^ 3 * Qr * Qt⁻¹ * N ^ (ℓ * r) ≤
      18 * K ^ 3 * (K * N ^ (κ * r)) * (K * N ^ (-(κ * t))) * N ^ (ℓ * r) := by
        gcongr
    _ = 18 * K ^ 5 * (N ^ (κ * r) * N ^ (-(κ * t)) * N ^ (ℓ * r)) := by ring
    _ = 18 * K ^ 5 * N ^ (κ * r + ℓ * r - κ * t) := by rw [hpow]
    _ ≤ N ^ (-βb) := h.le

namespace Parent

variable {α : Type} [MeasurableSpace α]

/-- **The physical bad set inside one original block.** If every true block at depth `s`
loses at most an `η` proportion of its incidence mass, the physical bad set of its groups has
original mass at most `K η` times the reference `2^(-T) ν(A_Q)` inside an original block `Q`
at a shallower depth `r`. (Parent-block part of the proof of `ListFrame.law_physBad_le`,
`Confine/Loss.lean`.) -/
theorem Valid.physBad_parent_le {p : Parent α} (h : p.Valid) {k : ℕ} {r s R : ℝ}
    (hat_r : p.AtDepth k r R) (hat_s : p.AtDepth k s R)
    (hnest : ∀ i : Fin (p.n k s), ∃ h : Fin (p.n k r), p.A k s i ⊆ p.A k r h ∧
      block (p.T k s) (p.j k s i) ⊆ block (p.T k r) (p.j k r h))
    {E : Fin (p.n k s) → Fin 2 → Set (α × ℝ)} {η : ℝ≥0∞}
    (hEloss : ∀ i, p.μ k ((p.B k s i ×ˢ block (p.T k s) (p.j k s i)) \ ⋃ e, E i e) ≤
      p.μ k (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) * η)
    (Q : Fin (p.n k r)) :
    p.μ k (p.physBad k s E ∩ (p.B k r Q ×ˢ block (p.T k r) (p.j k r Q))) ≤
      ENNReal.ofReal (p.K k) *
        (ENNReal.ofReal ((2 : ℝ) ^ p.T k r)⁻¹ * p.ν k (p.A k r Q)) * η := by
  classical
  have hνprob : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  have hmeas_r := hat_r.2.2.1
  have hdisj_r := hat_r.2.2.2.1
  have hmeas_s := hat_s.2.2.1
  have hdisj_s := hat_s.2.2.2.1
  set Par : Set (α × ℝ) := p.B k r Q ×ˢ block (p.T k r) (p.j k r Q) with hParDef
  set L : Fin (p.n k s) → Set (α × ℝ) := fun i =>
    (p.B k s i ×ˢ block (p.T k s) (p.j k s i)) \ ⋃ e, E i e with hLdef
  set S : Finset (Fin (p.n k s)) := Finset.univ.filter (fun i =>
    p.A k s i ⊆ p.A k r Q ∧ block (p.T k s) (p.j k s i) ⊆ block (p.T k r) (p.j k r Q))
    with hSdef
  set Z : Set (α × ℝ) := ({z | z.2 ∈ dyadicTimes (p.T k s)} ∪
    (⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i))ᶜ) ∪ {z | z.2 ∈ dyadicTimes (p.T k r)}
    with hZdef
  have hZ : p.μ k Z = 0 := by
    apply le_antisymm _ zero_le
    calc p.μ k Z ≤ p.μ k ({z : α × ℝ | z.2 ∈ dyadicTimes (p.T k s)} ∪
          (⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i))ᶜ) +
          p.μ k {z : α × ℝ | z.2 ∈ dyadicTimes (p.T k r)} := measure_union_le _ _
      _ ≤ (p.μ k {z : α × ℝ | z.2 ∈ dyadicTimes (p.T k s)} +
          p.μ k (⋃ i, p.B k s i ×ˢ block (p.T k s) (p.j k s i))ᶜ) +
          p.μ k {z : α × ℝ | z.2 ∈ dyadicTimes (p.T k r)} := by
          gcongr
          exact measure_union_le _ _
      _ = 0 := by rw [h.dyadic_null, h.dyadic_null, hat_s.uncovered_null]; simp
  have hsub : p.physBad k s E ∩ Par ⊆ Z ∪ ⋃ i ∈ S, L i := by
    rintro z ⟨hz, hzP⟩
    rcases hz with hz | hz
    · exact Or.inl (Or.inl hz)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      by_cases hDr : z.2 ∈ dyadicTimes (p.T k r)
      · exact Or.inl (Or.inr hDr)
      · obtain ⟨h', hA', hI'⟩ := hnest i
        have hzA : z.1 ∈ p.A k s i := (hmeas_s i).2.2 hi.1.1
        have hh' : h' = Q :=
          block_eq_of_mem hdisj_r (hA' hzA) ((hmeas_r Q).2.2 hzP.1) (hI' hi.1.2) hzP.2 hDr
        rw [hh'] at hA' hI'
        refine Or.inr (mem_iUnion₂.mpr ⟨i, ?_, hi⟩)
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hA', hI'⟩
  have hphys : p.μ k (p.physBad k s E ∩ Par) ≤ ∑ i ∈ S, p.μ k (L i) := by
    calc p.μ k (p.physBad k s E ∩ Par) ≤ p.μ k (Z ∪ ⋃ i ∈ S, L i) := measure_mono hsub
      _ ≤ p.μ k Z + p.μ k (⋃ i ∈ S, L i) := measure_union_le _ _
      _ = p.μ k (⋃ i ∈ S, L i) := by rw [hZ, zero_add]
      _ ≤ ∑ i ∈ S, p.μ k (L i) := measure_biUnion_finset_le _ _
  have hpack : ∑ i ∈ S, ENNReal.ofReal ((2 : ℝ) ^ p.T k s)⁻¹ * p.ν k (p.A k s i) ≤
      ENNReal.ofReal ((2 : ℝ) ^ p.T k r)⁻¹ * p.ν k (p.A k r Q) := by
    have h1 := nested_packing (p.ν k) (fun i => (hmeas_s i).1) hdisj_s
      (P := p.A k r Q) (I := block (p.T k r) (p.j k r Q)) S (by
        intro i hi
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi)
    rwa [volume_block] at h1
  calc p.μ k (p.physBad k s E ∩ Par) ≤ ∑ i ∈ S, p.μ k (L i) := hphys
    _ ≤ ∑ i ∈ S, ENNReal.ofReal (p.K k) *
          (ENNReal.ofReal ((2 : ℝ) ^ p.T k s)⁻¹ * p.ν k (p.A k s i)) * η := by
        apply Finset.sum_le_sum
        intro i _
        refine (hEloss i).trans ?_
        gcongr
        exact h.block_mass_le i (hmeas_s i).2.2
    _ = ENNReal.ofReal (p.K k) * (∑ i ∈ S,
          ENNReal.ofReal ((2 : ℝ) ^ p.T k s)⁻¹ * p.ν k (p.A k s i)) * η := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := by gcongr

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
