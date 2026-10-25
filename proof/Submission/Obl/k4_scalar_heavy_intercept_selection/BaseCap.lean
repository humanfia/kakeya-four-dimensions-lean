/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/BaseCap.lean.
Earlier source credits are retained below. -/

import Mathlib
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open MeasureTheory Set
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- A rectangular floor cap controls a box with arbitrary center.  The
observation need not be injective and the tested event need not be measurable. -/
theorem coordinate_box_cap {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) (x : Ω → ι → ℝ) (a L c : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hL : ∀ i, 0 ≤ L i) (M : ENNReal)
    (hcap : ∀ q : ι → ℤ, μ {p | (fun i => (⌊x p i / a i⌋ : ℤ)) = q} ≤ M)
    (E : Set Ω) (hE : ∀ p ∈ E, ∀ i, |x p i - c i| ≤ L i * a i) :
    μ E ≤ ENNReal.ofReal (∏ i, (2 * L i + 5)) * M := by
  classical
  let V : ι → Finset ℤ := fun i =>
    (Finset.Icc (-⌈L i + 1⌉ : ℤ) ⌈L i + 1⌉).image
      (fun z => (⌊c i / a i⌋ : ℤ) + z)
  let F : Finset (ι → ℤ) := Fintype.piFinset V
  have hcover : E ⊆ ⋃ q ∈ F, {p | (fun i => (⌊x p i / a i⌋ : ℤ)) = q} := by
    intro p hp
    apply mem_iUnion.mpr
    refine ⟨fun i => (⌊x p i / a i⌋ : ℤ), mem_iUnion.mpr ⟨?_, rfl⟩⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_image.mpr
    refine ⟨⌊x p i / a i⌋ - ⌊c i / a i⌋, floor_offset_mem (ha i) (hE p hp i), ?_⟩
    omega
  have hcard : (F.card : ℝ) ≤ ∏ i, (2 * L i + 5) := by
    dsimp only [F]
    rw [Fintype.card_piFinset, Nat.cast_prod]
    apply Finset.prod_le_prod₀
    · intro i _
      positivity
    · intro i _
      exact (Nat.cast_le.mpr (Finset.card_image_le)).trans (card_floor_offsets_le (hL i))
  calc
    μ E ≤ μ (⋃ q ∈ F, {p | (fun i => (⌊x p i / a i⌋ : ℤ)) = q}) := measure_mono hcover
    _ ≤ ∑ q ∈ F, μ {p | (fun i => (⌊x p i / a i⌋ : ℤ)) = q} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ F, M := Finset.sum_le_sum fun q _ => hcap q
    _ = (F.card : ENNReal) * M := by simp
    _ ≤ ENNReal.ofReal (∏ i, (2 * L i + 5)) * M := by
      exact mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal hcard) le_rfl

/-- The physical diameter of a normalized floor cell is its mesh times
its normalization scale. -/
theorem normalized_cell_diameter {h ξ x y z : ℝ} (hh : 0 < h) (hξ : 0 < ξ)
    (heq : (⌊(x - z) / h / ξ⌋ : ℤ) = ⌊(y - z) / h / ξ⌋) :
    |x - y| ≤ h * ξ := by
  have hf := (Int.abs_sub_lt_one_of_floor_eq_floor heq).le
  have hid : (x - z) / h / ξ - (y - z) / h / ξ = (x - y) / (h * ξ) := by ring
  rw [hid, abs_div, abs_of_pos (mul_pos hh hξ)] at hf
  simpa using (div_le_iff₀ (mul_pos hh hξ)).mp hf

/-- A graph strip over a normalized base cell inherits the original
rectangular cap. This is the finite-mesh form of the intercept base cap;
no continuous-base disintegration is assumed. -/
theorem graph_cell_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) (hμρ : μ ≤ ρ) (b : Ω → Fin 2 → ℝ) (X : Ω → ℝ)
    (z : Fin 2 → ℝ) {h ξ a E L : ℝ}
    (hh : 0 < h) (hξ : 0 < ξ) (ha : 0 < a) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (f : (Fin 2 → ℝ) → ℝ) (M : ENNReal)
    (hcap : ∀ (q : Fin 2 → ℤ) (j : ℤ),
      ρ {p | (fun i => (⌊b p i / (h * ξ)⌋ : ℤ)) = q ∧ ⌊X p / a⌋ = j} ≤ M)
    (S : Set Ω) (hsupport : ∀ᵐ p ∂μ, p ∈ S)
    (hfit : ∀ p ∈ S, |X p - f (fun i => (b p i - z i) / h)| ≤ E * a)
    (hosc : ∀ p ∈ S, ∀ p' ∈ S,
      (fun i => (⌊(b p i - z i) / h / ξ⌋ : ℤ)) =
        (fun i => (⌊(b p' i - z i) / h / ξ⌋ : ℤ)) →
      |f (fun i => (b p i - z i) / h) - f (fun i => (b p' i - z i) / h)| ≤ L * a)
    (q : Fin 2 → ℤ) :
    μ {p | (fun i => (⌊(b p i - z i) / h / ξ⌋ : ℤ)) = q} ≤
      ENNReal.ofReal (49 * (2 * (2 * E + L) + 5)) * M := by
  classical
  let C : Set Ω := {p | p ∈ S ∧
    (fun i => (⌊(b p i - z i) / h / ξ⌋ : ℤ)) = q}
  have hC : μ {p | (fun i => (⌊(b p i - z i) / h / ξ⌋ : ℤ)) = q} = μ C := by
    apply measure_congr
    filter_upwards [hsupport] with p hp
    simp only [C, mem_ofPred_eq, hp, true_and]
  rw [hC]
  rcases C.eq_empty_or_nonempty with hempty | ⟨p₀, hp₀⟩
  · simp [hempty]
  let obs : Ω → Fin 3 → ℝ := fun p => ![b p 0, b p 1, X p]
  let widths : Fin 3 → ℝ := ![h * ξ, h * ξ, a]
  let radii : Fin 3 → ℝ := ![1, 1, 2 * E + L]
  have hfull : ∀ j : Fin 3 → ℤ,
      ρ {p | (fun i => (⌊obs p i / widths i⌋ : ℤ)) = j} ≤ M := by
    intro j
    apply le_trans (measure_mono ?_) (hcap ![j 0, j 1] (j 2))
    intro p hp
    refine ⟨?_, congrFun hp 2⟩
    ext i
    fin_cases i
    · simpa [obs, widths] using congrFun hp 0
    · simpa [obs, widths] using congrFun hp 1
  have hbox : ∀ p ∈ C, ∀ i, |obs p i - obs p₀ i| ≤ radii i * widths i := by
    intro p hp i
    have hbase : ∀ j : Fin 2, |b p j - b p₀ j| ≤ h * ξ := by
      intro j
      exact normalized_cell_diameter hh hξ (congrFun (hp.2.trans hp₀.2.symm) j)
    fin_cases i
    · simpa [obs, widths, radii] using hbase 0
    · simpa [obs, widths, radii] using hbase 1
    · change |X p - X p₀| ≤ (2 * E + L) * a
      have hf := hosc p hp.1 p₀ hp₀.1 (hp.2.trans hp₀.2.symm)
      calc
        _ ≤ |X p - f (fun i => (b p i - z i) / h)| +
            |f (fun i => (b p i - z i) / h) - f (fun i => (b p₀ i - z i) / h)| +
            |f (fun i => (b p₀ i - z i) / h) - X p₀| := by
              have ht₁ := abs_sub_le (X p) (f (fun i => (b p i - z i) / h))
                (f (fun i => (b p₀ i - z i) / h))
              have ht₂ := abs_sub_le (X p) (f (fun i => (b p₀ i - z i) / h)) (X p₀)
              linarith
        _ ≤ E * a + L * a + E * a := by
          exact add_le_add (add_le_add (hfit p hp.1) hf)
            (by simpa only [abs_sub_comm] using hfit p₀ hp₀.1)
        _ = _ := by ring
  calc
    μ C ≤ ρ C := hμρ C
    _ ≤ ENNReal.ofReal (∏ i, (2 * radii i + 5)) * M :=
      coordinate_box_cap ρ obs widths radii (obs p₀)
        (by intro i; fin_cases i <;> dsimp [widths] <;> positivity)
        (by intro i; fin_cases i <;> dsimp [radii] <;> positivity) M hfull C hbox
    _ = _ := by congr 2; simp [radii, Fin.prod_univ_succ]; ring

/-- Dividing the original rectangular cap by the packet's unchanged
prior mass gives exactly the relative intercept-width gain. -/
theorem rectangular_cap_relative_to_prior {a w h ξ K A d : ℝ} {prior : ENNReal}
    (ha : 0 < a) (hw : 0 < w) (hh : 0 ≤ h)
    (hK : 0 < K) (hA : 0 ≤ A)
    (hprior : ENNReal.ofReal (a ^ d * h / K) ≤ prior) :
    ENNReal.ofReal (A * K * (h * ξ) ^ 2 * w ^ d) ≤
      ENNReal.ofReal (A * K ^ 2 * h * ξ ^ 2 * (w / a) ^ d) * prior := by
  have hid : A * K * (h * ξ) ^ 2 * w ^ d =
      (A * K ^ 2 * h * ξ ^ 2 * (w / a) ^ d) * (a ^ d * h / K) := by
    rw [Real.div_rpow hw.le ha.le]
    field_simp [hK.ne', (Real.rpow_pos_of_pos ha d).ne']
  rw [hid, ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul' le_rfl hprior

/-- The improved base-cell ceiling for an intercept group, derived from
original floor caps and the original packet prior. -/
theorem graph_cell_relative_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ ρ : Measure Ω) (hμρ : μ ≤ ρ) (b : Ω → Fin 2 → ℝ) (X : Ω → ℝ)
    (z : Fin 2 → ℝ) {h ξ a w E L K d : ℝ} {prior : ENNReal}
    (hh : 0 < h) (hξ : 0 < ξ) (ha : 0 < a) (hw : 0 < w)
    (hE : 0 ≤ E) (hL : 0 ≤ L) (hK : 0 < K)
    (f : (Fin 2 → ℝ) → ℝ)
    (hcap : ∀ (q : Fin 2 → ℤ) (j : ℤ),
      ρ {p | (fun i => (⌊b p i / (h * ξ)⌋ : ℤ)) = q ∧ ⌊X p / w⌋ = j} ≤
        ENNReal.ofReal (K * (h * ξ) ^ 2 * w ^ d))
    (hprior : ENNReal.ofReal (a ^ d * h / K) ≤ prior)
    (S : Set Ω) (hsupport : ∀ᵐ p ∂μ, p ∈ S)
    (hfit : ∀ p ∈ S, |X p - f (fun i => (b p i - z i) / h)| ≤ E * w)
    (hosc : ∀ p ∈ S, ∀ p' ∈ S,
      (fun i => (⌊(b p i - z i) / h / ξ⌋ : ℤ)) =
        (fun i => (⌊(b p' i - z i) / h / ξ⌋ : ℤ)) →
      |f (fun i => (b p i - z i) / h) - f (fun i => (b p' i - z i) / h)| ≤ L * w)
    (q : Fin 2 → ℤ) :
    μ {p | (fun i => (⌊(b p i - z i) / h / ξ⌋ : ℤ)) = q} ≤
      ENNReal.ofReal (49 * (2 * (2 * E + L) + 5) * K ^ 2 * h * ξ ^ 2 * (w / a) ^ d) *
        prior := by
  have hA : 0 ≤ 49 * (2 * (2 * E + L) + 5) := by positivity
  apply (graph_cell_cap μ ρ hμρ b X z hh hξ hw hE hL f _ hcap
    S hsupport hfit hosc q).trans
  rw [← ENNReal.ofReal_mul hA]
  simpa only [mul_assoc] using rectangular_cap_relative_to_prior ha hw hh.le hK hA hprior

/-- Relative caps survive unions of whole fine states. This is why
coarse base cells are assigned using fine-state centers. -/
theorem state_union_event_cap {Ω Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (A : Set Ω) (C : ENNReal)
    (hcap : ∀ q, μ {p | state p = q ∧ p ∈ A} ≤ C * μ (state ⁻¹' {q}))
    (U : Set Q) :
    μ {p | state p ∈ U ∧ p ∈ A} ≤ C * μ (state ⁻¹' U) := by
  classical
  have hcover : {p | state p ∈ U ∧ p ∈ A} ⊆
      ⋃ q : U, {p | state p = q.1 ∧ p ∈ A} := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨state p, hp.1⟩, rfl, hp.2⟩
  calc
    _ ≤ μ (⋃ q : U, {p | state p = q.1 ∧ p ∈ A}) := measure_mono hcover
    _ ≤ ∑' q : U, μ {p | state p = q.1 ∧ p ∈ A} := measure_iUnion_le _
    _ ≤ ∑' q : U, C * μ (state ⁻¹' {q.1}) := ENNReal.tsum_le_tsum fun q => hcap q
    _ = C * μ (state ⁻¹' U) := by
      rw [ENNReal.tsum_mul_left,
        tsum_measure_preimage_singleton U.to_countable
          (fun q _ => hs (measurableSet_singleton q))]

/-- Original velocity-bin ceilings imply a pencil ceiling at the same
width, without converting the palette to a posterior probability law. -/
theorem state_velocity_pencil_cap {Ω Q : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (state : Ω → Q) (hs : Measurable state)
    (v : Ω → ℝ) (hv : Measurable v) {η : ℝ} (hη : 0 < η)
    (C P : ENNReal)
    (hcap : ∀ q (j : ℤ), μ {p | state p = q ∧ (⌊v p / η⌋ : ℤ) = j} ≤
      C * μ (state ⁻¹' {q}) * P) (q : Q) (w : ℝ) :
    μ {p | state p = q ∧ |v p - w| < η} ≤
      (7 * C * P) * μ (state ⁻¹' {q}) := by
  let ν := μ.restrict (state ⁻¹' {q})
  have hnear : μ {p | state p = q ∧ |v p - w| < η} = ν {p | |v p - w| < η} := by
    rw [Measure.restrict_apply (measurableSet_lt (hv.sub_const w).abs measurable_const)]
    congr 1
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    tauto
  rw [hnear]
  have hcell : ∀ j : Fin 1 → ℤ,
      ν {p | (fun i : Fin 1 => (⌊v p / η⌋ : ℤ)) = j} ≤ C * μ (state ⁻¹' {q}) * P := by
    intro j
    have hj : MeasurableSet {p | (fun i : Fin 1 => (⌊v p / η⌋ : ℤ)) = j} := by
      have hm : Measurable (fun p (_i : Fin 1) => (⌊v p / η⌋ : ℤ)) := by fun_prop
      exact hm (measurableSet_singleton j)
    rw [Measure.restrict_apply hj]
    apply (measure_mono ?_).trans (hcap q (j 0))
    rintro p ⟨hp, hq⟩
    exact ⟨hq, congrFun hp 0⟩
  have hb := coordinate_box_cap ν (fun p (_i : Fin 1) => v p) (fun _ => η)
    (fun _ => 1) (fun _ => w) (fun _ => hη) (fun _ => by norm_num)
    (C * μ (state ⁻¹' {q}) * P) hcell {p | |v p - w| < η}
    (fun p hp _ => by simpa using hp.le)
  norm_num at hb
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hb

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
