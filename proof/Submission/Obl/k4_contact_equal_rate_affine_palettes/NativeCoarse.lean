import Mathlib
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.LabelPaletteBudget
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.MeshVelocity
import Submission.Obl.k4_contact_fine_labels_from_coarse_cover.TimeAlignedFilling
import Submission.Obl.k4_fixed_budget_quadratic_recovery.GraphCaps

/-!
# The native coarse affine cover at one index

At a fixed index the native test `P` (width one) is handled as a true label of unit size:
`t₀ = 0`, `q = g = a = 1`, `c = 0`. The base law has cell caps `B₀ δ³` (`B₀ = (2K+5)K`,
from the unit native bins) and velocity-joint caps `B₀ δ³ · π(bin)`.

* Light mesh cells (good mass below `11 b₁ δ³`, `b₁ = B₀ πb`) carry at most `396 K² b₁` in total,
  by the mesh saturation of the bounded base box (`light_mass_le`).
* Every heavy cell has three good incidences with `Nv`-separated velocities
  (`three_velocity_witnesses_of_mesh`).
* The heavy good incidences fill, after time-aligned mesh saturation, a set of times in `[0,1]` and
  volume at least `1/(54 K B₀)`, each point within `3δ` of three heavy witnesses
  (`exists_time_aligned_filling`).
* `label_palette_budget` then fits every good line with an event (hence `μ`-almost every
  incidence) on all of `[0,1]` by one of three affine functions, with error `C Λ⁸⁰`.
-/

namespace Submission.Obl.k4_contact_equal_rate_affine_palettes

open MeasureTheory Set Filter MvPolynomial
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_contact_fine_labels_from_coarse_cover

noncomputable section

/-- The base point `(t, Z, Y)` of an incidence. -/
def nbase {α : Type*} (b : α → Fin 6 → ℝ) (u : α × ℝ) : Fin 3 → ℝ := basePt (b u.1) u.2

/-- A good native incidence at one index. -/
structure NativeGood {α : Type*} (K Ne : ℝ) (b : α → Fin 6 → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (u : α × ℝ) : Prop where
  time : u.2 ∈ Ico (0 : ℝ) 1
  coeff : |b u.1 0| + |b u.1 1| + |b u.1 3| + |b u.1 4| ≤ K
  contact : |b u.1 4 + b u.1 0| ≤ Ne
  fit : ∀ t ∈ Icc (0 : ℝ) 1, |eval (point (b u.1) t) P| ≤ K ∧
    |eval (point (b u.1) t) (pderiv 3 P)| ≤ K ∧
    |eval (point (b u.1) t) (pderiv 3 (pderiv 3 P))| ≤ K
  regular : K⁻¹ ≤ |eval (point (b u.1) u.2) (pderiv 3 P)|

/-- The coefficient vectors of the unit native box. -/
def nativeBox (K : ℝ) : Set (Fin 6 → ℝ) := {β | |β 0| + |β 1| + |β 3| + |β 4| ≤ K}

theorem nativeBox_bounds {K : ℝ} {β : Fin 6 → ℝ} (hβ : β ∈ nativeBox K) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |β 0 + t * β 3 - 0 - t * 0| ≤ K * 1 ∧
      |β 1 + t * β 4 - 0 - t * 0 - 0 * (β 0 + t * β 3)| ≤ K * 1 * 1 ∧
      |β 4 - 0 - 0 * β 3| ≤ K * 1 := by
  have h := hβ
  simp only [nativeBox, mem_setOf_eq] at h
  have ht0 := ht.1; have ht1 := ht.2
  have a0 := abs_nonneg (β 0); have a1 := abs_nonneg (β 1)
  have a3 := abs_nonneg (β 3); have a4 := abs_nonneg (β 4)
  have e1 : |t * β 3| ≤ |β 3| := by
    rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_of_le_one_left a3 ht1
  have e2 : |t * β 4| ≤ |β 4| := by
    rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_of_le_one_left a4 ht1
  refine ⟨?_, ?_, ?_⟩
  · have : β 0 + t * β 3 - 0 - t * 0 = β 0 + t * β 3 := by ring
    rw [this, mul_one]
    calc _ ≤ |β 0| + |t * β 3| := abs_add_le _ _
      _ ≤ K := by linarith
  · have : β 1 + t * β 4 - 0 - t * 0 - 0 * (β 0 + t * β 3) = β 1 + t * β 4 := by ring
    rw [this, mul_one, mul_one]
    calc _ ≤ |β 1| + |t * β 4| := abs_add_le _ _
      _ ≤ K := by linarith
  · have : β 4 - 0 - 0 * β 3 = β 4 := by ring
    rw [this, mul_one]; linarith

theorem nbase_bounds {α : Type*} {K Ne : ℝ} {b : α → Fin 6 → ℝ} {P : MvPolynomial (Fin 4) ℝ}
    {u : α × ℝ} (hu : NativeGood K Ne b P u) :
    nbase b u 0 ∈ Ico (0 : ℝ) 1 ∧ |nbase b u 1| ≤ K ∧ |nbase b u 2| ≤ K := by
  have hb := nativeBox_bounds (show b u.1 ∈ nativeBox K from hu.coeff)
    (Ico_subset_Icc_self hu.time)
  refine ⟨hu.time, ?_, ?_⟩
  · have := hb.1
    simp only [nbase, basePt, Matrix.cons_val]
    simpa using this
  · have := hb.2.1
    simp only [nbase, basePt, Matrix.cons_val]
    simpa using this

/-- Summing the occupied unit native bins. Inlined from x0834's
`NativeBaseCaps.bounded_scalar_bin_cap` (branch x0834 of o241), to avoid its model imports. -/
theorem native_scalar_bin_cap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : Set Ω) (f : Ω → ℝ) {a L : ℝ}
    (ha : 0 < a) (hL : 0 ≤ L) (W : ENNReal)
    (hbound : ∀ᵐ u ∂μ, |f u| ≤ L * a)
    (hcap : ∀ j : ℤ, μ {u | u ∈ C ∧ ⌊f u / a⌋ = j} ≤ W) :
    μ C ≤ ENNReal.ofReal (2 * L + 5) * W := by
  classical
  let J : Finset ℤ := Finset.Icc (-⌈L + 1⌉) ⌈L + 1⌉
  have hsub : ∀ᵐ u ∂μ, u ∈ C →
      u ∈ ⋃ j ∈ J, {u | u ∈ C ∧ ⌊f u / a⌋ = j} := by
    filter_upwards [hbound] with u hu hC
    have hm := Submission.Obl.k4_fixed_budget_quadratic_recovery.floor_offset_mem ha
      (show |f u - 0| ≤ L * a by simpa using hu)
    have hj : ⌊f u / a⌋ ∈ J := by simpa [J] using hm
    exact mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨hj, hC, rfl⟩⟩
  have hcard : (J.card : ENNReal) ≤ ENNReal.ofReal (2 * L + 5) := by
    simpa only [ENNReal.ofReal_natCast] using
      ENNReal.ofReal_le_ofReal
        (Submission.Obl.k4_fixed_budget_quadratic_recovery.card_floor_offsets_le hL)
  calc
    μ C ≤ μ (⋃ j ∈ J, {u | u ∈ C ∧ ⌊f u / a⌋ = j}) := measure_mono_ae hsub
    _ ≤ ∑ j ∈ J, μ {u | u ∈ C ∧ ⌊f u / a⌋ = j} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ J, W := Finset.sum_le_sum (fun j _ => hcap j)
    _ = (J.card : ENNReal) * W := by simp
    _ ≤ ENNReal.ofReal (2 * L + 5) * W := mul_le_mul hcard le_rfl bot_le bot_le

/-- The filling ratio of the native step. -/
def nativeLam (K : ℝ) : ℝ := 1 / (54 * K * ((2 * K + 5) * K))

/-- The bounded base box of native incidences. -/
def nativeRegion (K : ℝ) : Set (Fin 3 → ℝ) := {z | z 0 ∈ Icc (0 : ℝ) 1 ∧ |z 1| ≤ K ∧ |z 2| ≤ K}

/-- The mesh saturation of the native box has volume at most `18 K²`. -/
theorem volume_meshSaturation_nativeRegion {K δ : ℝ} (hK : 1 ≤ K) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    volume (meshSaturation δ (nativeRegion K)) ≤ ENNReal.ofReal (18 * K ^ 2) := by
  let lo : Fin 3 → ℝ := ![-δ, -(K + δ), -(K + δ)]
  let hi : Fin 3 → ℝ := ![1 + δ, K + δ, K + δ]
  have hsub : meshSaturation δ (nativeRegion K) ⊆ Icc lo hi := by
    intro z hz
    obtain ⟨w, hw, hclose⟩ := meshSaturation_close hδ _ hz
    obtain ⟨hw0, hw1, hw2⟩ := hw
    have c0 := hclose 0; have c1 := hclose 1; have c2 := hclose 2
    rw [abs_le] at c0 c1 c2 hw1 hw2
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
    · show -δ ≤ z 0; linarith [hw0.1]
    · show -(K + δ) ≤ z 1; linarith [hw1.1]
    · show -(K + δ) ≤ z 2; linarith [hw2.1]
    · show z 0 ≤ 1 + δ; linarith [hw0.2]
    · show z 1 ≤ K + δ; linarith [hw1.2]
    · show z 2 ≤ K + δ; linarith [hw2.2]
  refine (measure_mono hsub).trans ?_
  rw [Real.volume_Icc_pi, Fin.prod_univ_three]
  simp only [lo, hi, Matrix.cons_val]
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by nlinarith)]
  apply ENNReal.ofReal_le_ofReal
  calc (1 + δ - -δ) * (K + δ - -(K + δ)) * (K + δ - -(K + δ)) ≤ 2 * (3 * K) * (3 * K) := by
        gcongr <;> linarith
    _ = 18 * K ^ 2 := by ring

/-- The native mesh cell of an incidence. -/
def ncell {α : Type*} (b : α → Fin 6 → ℝ) (δ : ℝ) (q : Fin 3 → ℤ) : Set (α × ℝ) :=
  {u | baseMesh δ (nbase b u) = q}

theorem nativeLam_pos {K : ℝ} (hK : 1 ≤ K) : 0 < nativeLam K := by
  unfold nativeLam; have : 0 < K := by linarith
  positivity

theorem nativeLam_le_one {K : ℝ} (hK : 1 ≤ K) : nativeLam K ≤ 1 := by
  have hK0 : 0 < K := by linarith
  unfold nativeLam
  rw [div_le_one (by positivity)]
  have h1 : 1 ≤ (2 * K + 5) * K := by nlinarith
  have h2 : 1 ≤ 54 * K := by linarith
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ 54 * K * ((2 * K + 5) * K) := mul_le_mul h2 h1 zero_le_one (by linarith)

set_option maxHeartbeats 8000000 in
/-- **Native palette at one index.** Unit native caps, the native fit and the residual floor give
three affine functions fitting almost every native incidence on all of `[0,1]`. -/
theorem native_palette_at : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ)) (π : Measure ℝ)
      (b : α → Fin 6 → ℝ) (P : MvPolynomial (Fin 4) ℝ) (K Ne Nr Nv πb : ℝ),
    1 ≤ K → 0 ≤ Ne → Ne ≤ 1 → 0 < Nr → Nr ≤ 1 / 2 → 0 < Nv → Nv ≤ 1 → 0 ≤ πb →
    P.totalDegree ≤ 2 →
    (∀ᵐ u ∂μ, NativeGood K Ne b P u) →
    ENNReal.ofReal K⁻¹ ≤ μ univ →
    (∀ (q : Fin 3 → ℤ) (a : ℤ), μ {u | baseMesh Nr (nbase b u) = q ∧
      ⌊eval (point (b u.1) u.2) P / 1⌋ = a} ≤ ENNReal.ofReal (K * Nr ^ 3)) →
    (∀ (q : Fin 3 → ℤ) (a j : ℤ), μ {u | baseMesh Nr (nbase b u) = q ∧
      ⌊eval (point (b u.1) u.2) P / 1⌋ = a ∧ ⌊b u.1 3 / Nv⌋ = j} ≤
        ENNReal.ofReal (K * Nr ^ 3) * π {w | ⌊w / Nv⌋ = j}) →
    (∀ j : ℤ, π {w | ⌊w / Nv⌋ = j} ≤ ENNReal.ofReal πb) →
    400 * K ^ 3 * ((2 * K + 5) * K * πb) ≤ 1 →
    C * labelΛ K Nv (nativeLam K) ^ 80 *
      (Ne / (1 * labelμ K Nv) + 7 * K * (3 * Nr) / 1 ^ 2) ≤ 1 →
    ∃ L : Fin 3 → Fin 4 → ℝ, ∀ᵐ u ∂μ, ∃ i : Fin 3, ∀ t ∈ Icc (0 : ℝ) 1,
      |point (b u.1) t 3 - (L i 0 + L i 1 * t + L i 2 * point (b u.1) t 1 +
        L i 3 * point (b u.1) t 2)| ≤ C * labelΛ K Nv (nativeLam K) ^ 80 * 1 := by
  obtain ⟨C, hC1, hLP⟩ := label_palette_budget
  refine ⟨C, hC1, ?_⟩
  intro α _ μ π b P K Ne Nr Nv πb hK hNe0 hNe1 hNr hNr2 hNv hNv1 hπb hP hgood hmass hcapP
    hcapJ hπ hsmallL hbudget
  have hK0 : 0 < K := by linarith
  set B₀ : ℝ := (2 * K + 5) * K with hB₀
  have hB₀0 : 0 < B₀ := by positivity
  set G : Set (α × ℝ) := {u | NativeGood K Ne b P u} with hGdef
  have hGae : ∀ᵐ u ∂μ, u ∈ G := hgood
  have hGc : μ Gᶜ = 0 := ae_iff.mp hgood
  -- the native value is bounded almost everywhere
  have hPbound : ∀ᵐ u ∂μ, |eval (point (b u.1) u.2) P| ≤ K * 1 := by
    filter_upwards [hgood] with u hu
    rw [mul_one]
    exact (hu.fit u.2 (Ico_subset_Icc_self hu.time)).1
  -- cell caps and velocity-bin caps
  have hcell : ∀ q, μ (ncell b Nr q) ≤ ENNReal.ofReal (B₀ * Nr ^ 3) := by
    intro q
    have h := native_scalar_bin_cap μ (ncell b Nr q) (fun u => eval (point (b u.1) u.2) P)
      one_pos hK0.le (ENNReal.ofReal (K * Nr ^ 3)) hPbound (fun j => by
        simpa only [ncell, mem_setOf_eq] using hcapP q j)
    rw [← ENNReal.ofReal_mul (by linarith)] at h
    refine h.trans (le_of_eq ?_)
    congr 1; rw [hB₀]; ring
  set bb : ENNReal := ENNReal.ofReal (B₀ * πb * Nr ^ 3) with hbb
  have hbin : ∀ q (j : ℤ), μ {u | u ∈ ncell b Nr q ∧ ⌊b u.1 3 / Nv⌋ = j} ≤ bb := by
    intro q j
    have h := native_scalar_bin_cap μ {u | u ∈ ncell b Nr q ∧ ⌊b u.1 3 / Nv⌋ = j}
      (fun u => eval (point (b u.1) u.2) P) one_pos hK0.le
      (ENNReal.ofReal (K * Nr ^ 3) * π {w | ⌊w / Nv⌋ = j}) hPbound (fun a => by
        have e : {u | u ∈ {u | u ∈ ncell b Nr q ∧ ⌊b u.1 3 / Nv⌋ = j} ∧
            ⌊eval (point (b u.1) u.2) P / 1⌋ = a} =
            {u | baseMesh Nr (nbase b u) = q ∧ ⌊eval (point (b u.1) u.2) P / 1⌋ = a ∧
              ⌊b u.1 3 / Nv⌋ = j} := by
          ext u; simp only [ncell, mem_setOf_eq]; tauto
        rw [e]; exact hcapJ q a j)
    refine h.trans ?_
    calc ENNReal.ofReal (2 * K + 5) * (ENNReal.ofReal (K * Nr ^ 3) * π {w | ⌊w / Nv⌋ = j})
        ≤ ENNReal.ofReal (2 * K + 5) * (ENNReal.ofReal (K * Nr ^ 3) * ENNReal.ofReal πb) := by
          gcongr; exact hπ j
      _ = bb := by
          rw [hbb, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by linarith)]
          congr 1; rw [hB₀]; ring
  -- heavy cells
  let heavy : (Fin 3 → ℤ) → Prop := fun q => 10 * bb < μ (ncell b Nr q)
  -- the light part of the good set is small
  have hlight : μ {u | u ∈ G ∧ ¬ heavy (baseMesh Nr (nbase b u))} ≤
      ENNReal.ofReal (1 / (2 * K)) := by
    have hcapL : ∀ q : Fin 3 → ℤ, μ {u | baseMesh Nr (nbase b u) = q ∧
        (u ∈ G ∧ ¬ heavy (baseMesh Nr (nbase b u)))} ≤
        ENNReal.ofReal (10 * B₀ * πb * Nr ^ 3) := by
      intro q
      by_cases hq : heavy q
      · have hE : {u | baseMesh Nr (nbase b u) = q ∧
            (u ∈ G ∧ ¬ heavy (baseMesh Nr (nbase b u)))} = ∅ := by
          ext u
          simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
          intro hu _ hnh
          exact hnh (hu ▸ hq)
        rw [hE, measure_empty]; exact bot_le
      · have hsub : {u | baseMesh Nr (nbase b u) = q ∧
            (u ∈ G ∧ ¬ heavy (baseMesh Nr (nbase b u)))} ⊆ ncell b Nr q :=
          fun u hu => hu.1
        refine (measure_mono hsub).trans ?_
        have hnh : μ (ncell b Nr q) ≤ 10 * bb := not_lt.mp hq
        refine hnh.trans (le_of_eq ?_)
        rw [hbb, show (10 : ENNReal) = ENNReal.ofReal 10 by simp,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring
    have hsat := measure_le_meshSaturation_volume μ (nbase b)
      (fun u => u ∈ G ∧ ¬ heavy (baseMesh Nr (nbase b u))) hNr (by positivity) hcapL
      (nativeRegion K)
    have hsub : {u | u ∈ G ∧ ¬ heavy (baseMesh Nr (nbase b u))} ⊆
        {u | nbase b u ∈ nativeRegion K ∧ (u ∈ G ∧ ¬ heavy (baseMesh Nr (nbase b u)))} := by
      intro u hu
      refine ⟨?_, hu⟩
      obtain ⟨h0, h1, h2⟩ := nbase_bounds hu.1
      exact ⟨Ico_subset_Icc_self h0, h1, h2⟩
    refine (measure_mono hsub).trans (hsat.trans ?_)
    calc ENNReal.ofReal (10 * B₀ * πb) * volume (meshSaturation Nr (nativeRegion K))
        ≤ ENNReal.ofReal (10 * B₀ * πb) * ENNReal.ofReal (18 * K ^ 2) := by
          gcongr; exact volume_meshSaturation_nativeRegion hK hNr hNr2
      _ = ENNReal.ofReal (10 * B₀ * πb * (18 * K ^ 2)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (1 / (2 * K)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [le_div_iff₀ (by positivity)]
          have : 10 * B₀ * πb * (18 * K ^ 2) * (2 * K) = 360 * K ^ 3 * ((2 * K + 5) * K * πb) := by
            rw [hB₀]; ring
          rw [this]
          have h0 : 0 ≤ K ^ 3 * ((2 * K + 5) * K * πb) := by positivity
          linarith
  -- the heavy good set carries half of the floor
  set CH : Set (α × ℝ) := {u | u ∈ G ∧ heavy (baseMesh Nr (nbase b u))} with hCHdef
  have hCH : ENNReal.ofReal (1 / (2 * K)) ≤ μ CH := by
    have hcover : (univ : Set (α × ℝ)) ⊆ CH ∪ {u | u ∈ G ∧ ¬ heavy (baseMesh Nr (nbase b u))} ∪ Gᶜ := by
      intro u _
      by_cases hG : u ∈ G
      · by_cases hh : heavy (baseMesh Nr (nbase b u))
        · exact Or.inl (Or.inl ⟨hG, hh⟩)
        · exact Or.inl (Or.inr ⟨hG, hh⟩)
      · exact Or.inr hG
    have h1 : μ univ ≤ μ CH + μ {u | u ∈ G ∧ ¬ heavy (baseMesh Nr (nbase b u))} + μ Gᶜ :=
      (measure_mono (μ := μ) hcover).trans ((measure_union_le (μ := μ) _ _).trans
        (add_le_add (measure_union_le (μ := μ) _ _) le_rfl))
    rw [hGc, add_zero] at h1
    have h2 := hmass.trans h1
    have hsplit : ENNReal.ofReal K⁻¹ = ENNReal.ofReal (1 / (2 * K)) + ENNReal.ofReal (1 / (2 * K)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; field_simp; ring
    rw [hsplit] at h2
    have h3 : ENNReal.ofReal (1 / (2 * K)) + ENNReal.ofReal (1 / (2 * K)) ≤
        μ CH + ENNReal.ofReal (1 / (2 * K)) := h2.trans (add_le_add le_rfl hlight)
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h3
  -- the reciprocal integer mesh
  set M : ℕ := ⌊1 / Nr⌋₊ with hMdef
  have hNr1 : (2 : ℝ) ≤ 1 / Nr := by rw [le_div_iff₀ hNr]; linarith
  have hM2 : 2 ≤ M := Nat.le_floor (by exact_mod_cast hNr1)
  have hM : 0 < M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hMle : (M : ℝ) ≤ 1 / Nr := Nat.floor_le (by positivity)
  have hMgt : 1 / Nr < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hres : Nr / 1 ≤ (M : ℝ)⁻¹ := by
    rw [div_one, inv_eq_one_div, le_div_iff₀ hMpos]
    calc Nr * M ≤ Nr * (1 / Nr) := mul_le_mul_of_nonneg_left hMle hNr.le
      _ = 1 := by field_simp
  have hMinv : (M : ℝ)⁻¹ ≤ 2 * Nr := by
    rw [inv_eq_one_div, div_le_iff₀ hMpos]
    have h1 : 1 / Nr - 1 < M := by linarith
    have h2 : 1 ≤ Nr * (1 / Nr - 1) * 2 := by
      have : Nr * (1 / Nr - 1) = 1 - Nr := by field_simp
      rw [this]; linarith
    nlinarith
  -- time-aligned filling
  have htime : ∀ u ∈ CH, nbase b u 0 ∈ Ico (0 : ℝ) (0 + 1) := by
    intro u hu; rw [zero_add]; exact (nbase_bounds hu.1).1
  have hcapCH : ∀ r : Fin 3 → ℤ, μ {u | baseMesh Nr (nbase b u) = r ∧ u ∈ CH} ≤
      ENNReal.ofReal (B₀ * Nr ^ 3) := fun r =>
    (measure_mono (fun u hu => hu.1 : {u | baseMesh Nr (nbase b u) = r ∧ u ∈ CH} ⊆
      ncell b Nr r)).trans (hcell r)
  obtain ⟨E, -, hEt, hEvol, hEclose⟩ := exists_time_aligned_filling μ (nbase b) CH
    (t₀ := 0) (q := 1) (δ := Nr) (B := B₀) one_pos le_rfl hNr hB₀0.le M hM hres htime hcapCH
  have hEvol' : ENNReal.ofReal (nativeLam K * 1 ^ 4) ≤ volume E := by
    have h := hCH.trans hEvol
    have hc0 : ENNReal.ofReal (27 * B₀) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hct : ENNReal.ofReal (27 * B₀) ≠ ⊤ := ENNReal.ofReal_ne_top
    have heq : ENNReal.ofReal (27 * B₀) * ENNReal.ofReal (nativeLam K * 1 ^ 4) =
        ENNReal.ofReal (1 / (2 * K)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1; rw [nativeLam, hB₀]; field_simp; ring
    rw [← heq] at h
    exact (ENNReal.mul_le_mul_iff_right hc0 hct).mp h
  -- the native line sets
  set SB : Set (Fin 6 → ℝ) := {β | β ∈ nativeBox K ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    |eval (point β t) P| ≤ K ∧ |eval (point β t) (pderiv 3 P)| ≤ K ∧
      |eval (point β t) (pderiv 3 (pderiv 3 P))| ≤ K} with hSBdef
  set SW : Set (Fin 6 → ℝ) := {β | β ∈ SB ∧ |β 4 + β 0| ≤ Ne ∧ |β 3| ≤ K} with hSWdef
  have hgoodSB : ∀ u, NativeGood K Ne b P u → b u.1 ∈ SB := fun u hu => ⟨hu.coeff, hu.fit⟩
  have hgoodSW : ∀ u, NativeGood K Ne b P u → b u.1 ∈ SW := by
    intro u hu
    refine ⟨hgoodSB u hu, hu.contact, ?_⟩
    have := hu.coeff
    have := abs_nonneg (b u.1 0); have := abs_nonneg (b u.1 1); have := abs_nonneg (b u.1 4)
    linarith
  have hboxN : ∀ β ∈ nativeBox K, ∀ t ∈ Icc (0 : ℝ) (0 + 1),
      |β 0 + t * β 3 - (fun _ : Fin 5 => (0 : ℝ)) 0 - t * (fun _ : Fin 5 => (0 : ℝ)) 1| ≤ K * 1 ∧
      |β 1 + t * β 4 - (fun _ : Fin 5 => (0 : ℝ)) 2 - t * (fun _ : Fin 5 => (0 : ℝ)) 3 -
        (fun _ : Fin 5 => (0 : ℝ)) 4 * (β 0 + t * β 3)| ≤ K * 1 * 1 ∧
      |β 4 - (fun _ : Fin 5 => (0 : ℝ)) 3 - (fun _ : Fin 5 => (0 : ℝ)) 4 * β 3| ≤ K * 1 := by
    intro β hβ t ht
    rw [zero_add] at ht
    exact nativeBox_bounds hβ ht
  have hfitN : ∀ β ∈ SB, ∀ t ∈ Icc (0 : ℝ) (0 + 1), |eval (point β t) P| ≤ K * 1 ∧
      |eval (point β t) (pderiv 3 P)| ≤ K ∧ |eval (point β t) (pderiv 3 (pderiv 3 P))| ≤ K / 1 := by
    intro β hβ t ht
    rw [zero_add] at ht
    obtain ⟨h1, h2, h3⟩ := hβ.2 t ht
    exact ⟨by rw [mul_one]; exact h1, h2, by rw [div_one]; exact h3⟩
  have hWN : ∀ β ∈ SW, |β 4 + β 0| ≤ Ne ∧ |β 3| ≤ K := fun β hβ => hβ.2
  have hEtN : ∀ p ∈ E, p 0 ∈ Icc (0 : ℝ) (0 + 1) := hEt
  -- witnesses at every point of the filling
  have hwitE : ∀ p ∈ E, ∃ b₁ ∈ SW, ∃ b₂ ∈ SW, ∃ b₃ ∈ SW,
      ∃ τ₁ ∈ Icc (0 : ℝ) (0 + 1), ∃ τ₂ ∈ Icc (0 : ℝ) (0 + 1), ∃ τ₃ ∈ Icc (0 : ℝ) (0 + 1),
        (∀ i, |basePt b₁ τ₁ i - p i| ≤ 3 * Nr) ∧ (∀ i, |basePt b₂ τ₂ i - p i| ≤ 3 * Nr) ∧
        (∀ i, |basePt b₃ τ₃ i - p i| ≤ 3 * Nr) ∧
        Nv ≤ |b₁ 3 - b₂ 3| ∧ Nv ≤ |b₁ 3 - b₃ 3| ∧ Nv ≤ |b₂ 3 - b₃ 3| ∧
        K⁻¹ ≤ |eval (point b₁ τ₁) (pderiv 3 P)| := by
    intro z hz
    obtain ⟨u, huCH, hu⟩ := hEclose z hz
    set qc := baseMesh Nr (nbase b u) with hqc
    have hheavy : heavy qc := huCH.2
    obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, h01, h02, h12⟩ :=
      three_velocity_witnesses_of_mesh μ (ncell b Nr qc) G (fun p => b p.1 3) hNv bb
        (fun a => hbin qc a) hGae hheavy
    have hdist : ∀ p, p ∈ ncell b Nr qc → ∀ i, |basePt (b p.1) p.2 i - z i| ≤ 3 * Nr := by
      intro p hp i
      have h1 : |nbase b p i - nbase b u i| ≤ Nr :=
        meshBox_coordinate_distance hNr (q := qc) hp (show nbase b u ∈ meshBox Nr qc from rfl) i
      have h2 : |nbase b u i - z i| ≤ 2 * Nr := by
        rw [abs_sub_comm]; exact (hu i).trans hMinv
      calc |basePt (b p.1) p.2 i - z i| = |(nbase b p i - nbase b u i) + (nbase b u i - z i)| := by
            simp only [nbase]; ring_nf
        _ ≤ |nbase b p i - nbase b u i| + |nbase b u i - z i| := abs_add_le _ _
        _ ≤ Nr + 2 * Nr := add_le_add h1 h2
        _ = 3 * Nr := by ring
    have htimeI : ∀ p, p ∈ G → p.2 ∈ Icc (0 : ℝ) (0 + 1) := by
      intro p hp; rw [zero_add]; exact Ico_subset_Icc_self hp.time
    exact ⟨b p₀.1, hgoodSW p₀ hp₀.2, b p₁.1, hgoodSW p₁ hp₁.2, b p₂.1, hgoodSW p₂ hp₂.2,
      p₀.2, htimeI p₀ hp₀.2, p₁.2, htimeI p₁ hp₁.2, p₂.2, htimeI p₂ hp₂.2,
      hdist p₀ hp₀.1, hdist p₁ hp₁.1, hdist p₂ hp₂.1, h01.le, h02.le, h12.le, hp₀.2.regular⟩
  have hc0 : ∀ e : Fin 5, |(fun _ : Fin 5 => (0 : ℝ)) e| ≤ K := by
    intro e; simp only [abs_zero]; linarith
  obtain ⟨L, hL⟩ := hLP K 1 1 1 Ne Nv (3 * Nr) (nativeLam K) 0 (fun _ => 0) P (nativeBox K) SB SW
    E hK one_pos one_pos le_rfl (by linarith) zero_le_one hNe0 hNe1 hNv hNv1 (by positivity)
    (nativeLam_pos hK) (nativeLam_le_one hK) ⟨le_rfl, zero_le_one⟩ hc0 hP hboxN
    (fun β hβ => hβ.1) (fun β hβ => hβ.1) hfitN hWN hEtN hEvol' hwitE hbudget
  refine ⟨L, ?_⟩
  filter_upwards [hgood] with u hu
  have hev : ∃ τ ∈ Icc (0 : ℝ) (0 + 1), K⁻¹ ≤ |eval (point (b u.1) τ) (pderiv 3 P)| :=
    ⟨u.2, by rw [zero_add]; exact Ico_subset_Icc_self hu.time, hu.regular⟩
  obtain ⟨i, hi⟩ := hL (b u.1) (hgoodSB u hu) hev
  exact ⟨i, fun t ht => hi t (by rw [zero_add]; exact ht)⟩

end

end Submission.Obl.k4_contact_equal_rate_affine_palettes
