-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ParameterFloors2, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ParameterFloors2.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ParameterFloors2.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ParameterFloors2.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 4c91e1da. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic

/-!
# Parameter-bin caps in version 2 (paper `tex-06`, l. 195–281, upper half)

Paper display (6.x) `a05:parameter-floor`, upper half: for an affine bin `α = [y₀, V]_p` (the
`p`-bins of the tangential position `y₀ ∈ ℝ²` and of the velocity `V ∈ ℝ²`) and a ball `B_r`,
`r ≥ p`, of the scalar coefficients `(x₀, x₁, x₂)`,
`ν°{α, (x₀, x₁, x₂) ∈ B_r} ≤ K r^d p² π([V]_p)`,
from the rectangular cap `a05:rectangular-cap` on time windows of length `p` and the occupation
floor of the long-line prior `ν°`. In the coordinates of `Jets2` (`zx`, `zy`, `zv`):

* `ybin p c`, `vbin p c`: the `p`-bins of `y₀ = (c 3, c 5)` and `V = (c 4, c 6)`;
* `affine_bin_coefficient_cap`: the cap above, with constant
  `2 K_r K (2 + 2K)² (6 + 6K)^d` (`K_r` the rectangular-cap constant, `K` the coefficient bound
  and the inverse occupation floor).
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open MeasureTheory Set

noncomputable section

/-- The `p`-bin of the initial tangential position `y₀ = (c 3, c 5)`. -/
def ybin (p : ℝ) (c : Fin 7 → ℝ) : Fin 2 → ℤ := fun i => ⌊zy c 0 i / p⌋

/-- The `p`-bin of the tangential velocity `V = (c 4, c 6)`. -/
def vbin (p : ℝ) (c : Fin 7 → ℝ) : Fin 2 → ℤ := fun i => ⌊zv c i / p⌋

theorem measurable_ybin {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ} (hc : Measurable c)
    (p : ℝ) : Measurable (fun l => ybin p (c l)) := by
  apply measurable_pi_lambda
  intro i
  have h3 := (measurable_pi_apply 3).comp hc
  have h4 := (measurable_pi_apply 4).comp hc
  have h5 := (measurable_pi_apply 5).comp hc
  have h6 := (measurable_pi_apply 6).comp hc
  fin_cases i
  · simp only [ybin, Fin.zero_eta, zy_zero]
    exact ((h3.add (h4.mul_const 0)).div_const p).floor
  · simp only [ybin, Fin.mk_one, zy_one]
    exact ((h5.add (h6.mul_const 0)).div_const p).floor

theorem measurable_vbin {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ} (hc : Measurable c)
    (p : ℝ) : Measurable (fun l => vbin p (c l)) := by
  apply measurable_pi_lambda
  intro i
  have h4 := (measurable_pi_apply 4).comp hc
  have h6 := (measurable_pi_apply 6).comp hc
  fin_cases i
  · simp only [vbin, Fin.zero_eta, zv_zero]
    exact (h4.div_const p).floor
  · simp only [vbin, Fin.mk_one, zv_one]
    exact (h6.div_const p).floor

theorem bin_mem_Icc {x p : ℝ} (hp : 0 < p) {z : ℤ} (h : ⌊x / p⌋ = z) :
    x ∈ Icc (p * z) (p * z + p) := by
  have h1 := Int.floor_le (x / p)
  have h2 := Int.lt_floor_add_one (x / p)
  rw [h] at h1 h2
  constructor
  · have := (le_div_iff₀ hp).mp h1; linarith
  · have := (div_lt_iff₀ hp).mp h2; linarith

/-- The tangential position of a line in an affine bin stays in one box of side `(2 + 2K) p`
during a time window `[k p, k p + p]`, `k p ≤ 1`. -/
theorem zy_mem_window_box {c : Fin 7 → ℝ} {p K : ℝ} (hp : 0 < p)
    (hV : ∀ i, |zv c i| ≤ K) (β J : Fin 2 → ℤ) (hβ : ybin p c = β) (hJ : vbin p c = J)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1) (ht : t ∈ Icc s (s + p)) (i : Fin 2) :
    zy c t i ∈ Icc (p * β i + s * (p * J i) - K * p)
      (p * β i + s * (p * J i) - K * p + (2 + 2 * K) * p) := by
  have hy0 : zy c 0 i ∈ Icc (p * β i) (p * β i + p) := bin_mem_Icc hp (congrFun hβ i)
  have hv : zv c i ∈ Icc (p * J i) (p * J i + p) := bin_mem_Icc hp (congrFun hJ i)
  have hyt : zy c t i = zy c 0 i + t * zv c i := by
    rw [zy_add c t 0]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_zero]
  have h1 : |(t - s) * zv c i| ≤ p * K := by
    rw [abs_mul]
    have hd : |t - s| ≤ p := by
      rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    exact mul_le_mul hd (hV i) (abs_nonneg _) hp.le
  have h2 : 0 ≤ s * (zv c i - p * J i) := mul_nonneg hs0 (by linarith [hv.1])
  have h3 : s * (zv c i - p * J i) ≤ p := by
    calc s * (zv c i - p * J i) ≤ 1 * p :=
          mul_le_mul hs (by linarith [hv.2]) (by linarith [hv.1]) zero_le_one
      _ = p := one_mul p
  have he : zy c t i = zy c 0 i + s * (p * J i) +
      ((t - s) * zv c i + s * (zv c i - p * J i)) := by
    rw [hyt]; ring
  have h1' := abs_le.mp h1
  rw [he]
  constructor <;> nlinarith [hy0.1, hy0.2]

/-- The hidden coordinate of a line with scalar coefficients near `(b₀, b₁, b₂)` stays in one
interval of width `6 r + 6 K p` during a time window `[s, s + p]`, `0 ≤ s`. -/
theorem zx_mem_window_interval {c : Fin 7 → ℝ} {b₀ b₁ b₂ p r K : ℝ}
    (hK : 0 ≤ K) (hb₁ : |b₁| ≤ K) (hb₂ : |b₂| ≤ K)
    (hc0 : |c 0 - b₀| ≤ r) (hc1 : |c 1 - b₁| ≤ r) (hc2 : |c 2 - b₂| ≤ r)
    {s t : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1) (hp : 0 ≤ p) (ht : t ∈ Icc s (s + p))
    (ht1 : t ∈ Icc (0 : ℝ) 1) :
    zx c t ∈ Icc (b₀ + b₁ * s + b₂ * s ^ 2 - 3 * r - 3 * K * p)
      (b₀ + b₁ * s + b₂ * s ^ 2 - 3 * r - 3 * K * p + (6 * r + 6 * K * p)) := by
  have ht0 : 0 ≤ t := ht1.1
  have ht1' : t ≤ 1 := ht1.2
  have hts : |t - s| ≤ p := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hA : |zx c t - (b₀ + b₁ * t + b₂ * t ^ 2)| ≤ 3 * r := by
    have he : zx c t - (b₀ + b₁ * t + b₂ * t ^ 2) =
        (c 0 - b₀) + (c 1 - b₁) * t + (c 2 - b₂) * t ^ 2 := by
      simp only [zx]; ring
    rw [he]
    have e1 : |(c 1 - b₁) * t| ≤ r := by
      rw [abs_mul, abs_of_nonneg ht0]
      calc |c 1 - b₁| * t ≤ r * 1 := mul_le_mul hc1 ht1' ht0 (le_trans (abs_nonneg _) hc1)
        _ = r := mul_one r
    have e2 : |(c 2 - b₂) * t ^ 2| ≤ r := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
      have : t ^ 2 ≤ 1 := by nlinarith
      calc |c 2 - b₂| * t ^ 2 ≤ r * 1 :=
            mul_le_mul hc2 this (sq_nonneg t) (le_trans (abs_nonneg _) hc2)
        _ = r := mul_one r
    calc _ ≤ |c 0 - b₀| + |(c 1 - b₁) * t| + |(c 2 - b₂) * t ^ 2| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 3 * r := by linarith
  have hB : |(b₀ + b₁ * t + b₂ * t ^ 2) - (b₀ + b₁ * s + b₂ * s ^ 2)| ≤ 3 * K * p := by
    have he : (b₀ + b₁ * t + b₂ * t ^ 2) - (b₀ + b₁ * s + b₂ * s ^ 2) =
        (t - s) * (b₁ + b₂ * (t + s)) := by ring
    rw [he, abs_mul]
    have hts2 : |t + s| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith
    have hinner : |b₁ + b₂ * (t + s)| ≤ 3 * K := by
      calc |b₁ + b₂ * (t + s)| ≤ |b₁| + |b₂ * (t + s)| := abs_add_le _ _
        _ = |b₁| + |b₂| * |t + s| := by rw [abs_mul]
        _ ≤ K + K * 2 := add_le_add hb₁ (mul_le_mul hb₂ hts2 (abs_nonneg _) hK)
        _ = 3 * K := by ring
    calc |t - s| * |b₁ + b₂ * (t + s)| ≤ p * (3 * K) :=
          mul_le_mul hts hinner (abs_nonneg _) hp
      _ = 3 * K * p := by ring
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  constructor <;> linarith

/-- **The upper half of the parameter floor** (version 2): affine-bin coefficient caps from the
rectangular cap on time windows of length `p` and the occupation floor. -/
theorem affine_bin_coefficient_cap {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) [SFinite ν]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {S : Set Λ} (hS : MeasurableSet S)
    {p K Kr d : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hK : 1 ≤ K) (hKr : 0 ≤ Kr) (hd : 0 ≤ d)
    (π : (Fin 2 → ℤ) → ENNReal)
    (hV : ∀ l ∈ S, ∀ i, |zv (c l) i| ≤ K)
    (hocc : ∀ l ∈ S, ENNReal.ofReal K⁻¹ ≤ volume {t | (l, t) ∈ E})
    (hrect : ∀ (t₀ : ℝ) (Y : Fin 2 → ℝ) (a q w : ℝ) (J : Fin 2 → ℤ), p ≤ q → p ≤ w →
      (ν.prod volume) {z | z ∈ E ∧ z.2 ∈ Icc t₀ (t₀ + p) ∧
        (∀ i, zy (c z.1) z.2 i ∈ Icc (Y i) (Y i + q)) ∧ zx (c z.1) z.2 ∈ Icc a (a + w) ∧
        vbin p (c z.1) = J} ≤ ENNReal.ofReal (Kr * p * q ^ 2 * w ^ d) * π J)
    (β J : Fin 2 → ℤ) {b₀ b₁ b₂ : ℝ} (hb₁ : |b₁| ≤ K) (hb₂ : |b₂| ≤ K) {r : ℝ} (hr : p ≤ r) :
    ν {l | l ∈ S ∧ ybin p (c l) = β ∧ vbin p (c l) = J ∧
        |c l 0 - b₀| ≤ r ∧ |c l 1 - b₁| ≤ r ∧ |c l 2 - b₂| ≤ r} ≤
      ENNReal.ofReal (2 * Kr * K * (2 + 2 * K) ^ 2 * (6 + 6 * K) ^ d * p ^ 2 * r ^ d) * π J := by
  classical
  have hK0 : 0 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  set A : Set Λ := {l | l ∈ S ∧ ybin p (c l) = β ∧ vbin p (c l) = J ∧
      |c l 0 - b₀| ≤ r ∧ |c l 1 - b₁| ≤ r ∧ |c l 2 - b₂| ≤ r} with hAdef
  have hc0 : Measurable (fun l => c l 0) := (measurable_pi_apply 0).comp hc
  have hc1 : Measurable (fun l => c l 1) := (measurable_pi_apply 1).comp hc
  have hc2 : Measurable (fun l => c l 2) := (measurable_pi_apply 2).comp hc
  have hA : MeasurableSet A := by
    refine hS.inter (((measurable_ybin hc p) (measurableSet_singleton β)).inter
      (((measurable_vbin hc p) (measurableSet_singleton J)).inter ?_))
    refine (measurableSet_le (hc0.sub measurable_const).abs measurable_const).inter
      ((measurableSet_le (hc1.sub measurable_const).abs measurable_const).inter
        (measurableSet_le (hc2.sub measurable_const).abs measurable_const))
  -- occupation
  have hEA : MeasurableSet (E ∩ (A ×ˢ univ)) := hE.inter (hA.prod MeasurableSet.univ)
  have hocc' : ENNReal.ofReal K⁻¹ * ν A ≤ (ν.prod volume) (E ∩ (A ×ˢ univ)) := by
    rw [Measure.prod_apply hEA]
    calc ENNReal.ofReal K⁻¹ * ν A = ∫⁻ _l in A, ENNReal.ofReal K⁻¹ ∂ν := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ l in A, volume (Prod.mk l ⁻¹' (E ∩ (A ×ˢ univ))) ∂ν := by
          apply setLIntegral_mono' hA
          intro l hl
          have heq : Prod.mk l ⁻¹' (E ∩ (A ×ˢ univ)) = {t | (l, t) ∈ E} := by
            ext t; simp [hl]
          rw [heq]
          exact hocc l hl.1
      _ ≤ ∫⁻ l, volume (Prod.mk l ⁻¹' (E ∩ (A ×ˢ univ))) ∂ν := setLIntegral_le_lintegral _ _
  have hνA : ν A ≤ ENNReal.ofReal K * (ν.prod volume) (E ∩ (A ×ˢ univ)) := by
    have hKK : ENNReal.ofReal K * ENNReal.ofReal K⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul hK0, mul_inv_cancel₀ hKpos.ne', ENNReal.ofReal_one]
    calc ν A = ENNReal.ofReal K * (ENNReal.ofReal K⁻¹ * ν A) := by
          rw [← mul_assoc, hKK, one_mul]
      _ ≤ _ := mul_le_mul' le_rfl hocc'
  -- the windows
  set M : ℕ := ⌊1 / p⌋₊ + 1 with hMdef
  set q : ℝ := (2 + 2 * K) * p with hqdef
  set w : ℝ := 6 * r + 6 * K * p with hwdef
  let W : ℕ → Set (Λ × ℝ) := fun k =>
    {z | z ∈ E ∧ z.2 ∈ Icc ((k : ℝ) * p) ((k : ℝ) * p + p) ∧
      (∀ i, zy (c z.1) z.2 i ∈ Icc (p * β i + (k : ℝ) * p * (p * J i) - K * p)
        (p * β i + (k : ℝ) * p * (p * J i) - K * p + q)) ∧
      zx (c z.1) z.2 ∈ Icc (b₀ + b₁ * ((k : ℝ) * p) + b₂ * ((k : ℝ) * p) ^ 2 - 3 * r - 3 * K * p)
        (b₀ + b₁ * ((k : ℝ) * p) + b₂ * ((k : ℝ) * p) ^ 2 - 3 * r - 3 * K * p + w) ∧
      vbin p (c z.1) = J}
  have hcover : E ∩ (A ×ˢ univ) ⊆ ⋃ k ∈ Finset.range M, W k := by
    intro z hz
    have hzE := hz.1
    have hzA : z.1 ∈ A := hz.2.1
    have ht1 := (hunit hzE).2
    set k : ℕ := ⌊z.2 / p⌋₊ with hk
    have hkle : (k : ℝ) * p ≤ z.2 := by
      have := Nat.floor_le (div_nonneg ht1.1 hp.le)
      calc (k : ℝ) * p ≤ z.2 / p * p := mul_le_mul_of_nonneg_right this hp.le
        _ = z.2 := div_mul_cancel₀ _ hp.ne'
    have hklt : z.2 < (k : ℝ) * p + p := by
      have := Nat.lt_floor_add_one (z.2 / p)
      have h2 : z.2 / p < (k : ℝ) + 1 := this
      have h3 := (div_lt_iff₀ hp).mp h2
      linarith
    have hkM : k < M := by
      have : k ≤ ⌊1 / p⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_right ht1.2 hp.le)
      omega
    have hs0 : 0 ≤ (k : ℝ) * p := by positivity
    have hs1 : (k : ℝ) * p ≤ 1 := hkle.trans ht1.2
    have htI : z.2 ∈ Icc ((k : ℝ) * p) ((k : ℝ) * p + p) := ⟨hkle, hklt.le⟩
    refine mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr hkM, hzE, htI, ?_, ?_, hzA.2.2.1⟩
    · intro i
      exact zy_mem_window_box hp (hV z.1 hzA.1) β J hzA.2.1 hzA.2.2.1 hs0 hs1 htI i
    · exact zx_mem_window_interval hK0 hb₁ hb₂ hzA.2.2.2.1 hzA.2.2.2.2.1 hzA.2.2.2.2.2
        hs0 hs1 hp.le htI ht1
  have hq : p ≤ q := by rw [hqdef]; nlinarith
  have hw : p ≤ w := by rw [hwdef]; nlinarith
  have hWcap : ∀ k, (ν.prod volume) (W k) ≤ ENNReal.ofReal (Kr * p * q ^ 2 * w ^ d) * π J :=
    fun k => hrect _ _ _ q w J hq hw
  have hsum : (ν.prod volume) (E ∩ (A ×ˢ univ)) ≤
      (M : ENNReal) * (ENNReal.ofReal (Kr * p * q ^ 2 * w ^ d) * π J) := by
    calc (ν.prod volume) (E ∩ (A ×ˢ univ)) ≤ (ν.prod volume) (⋃ k ∈ Finset.range M, W k) :=
          measure_mono hcover
      _ ≤ ∑ k ∈ Finset.range M, (ν.prod volume) (W k) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ Finset.range M, ENNReal.ofReal (Kr * p * q ^ 2 * w ^ d) * π J :=
          Finset.sum_le_sum fun k _ => hWcap k
      _ = (M : ENNReal) * (ENNReal.ofReal (Kr * p * q ^ 2 * w ^ d) * π J) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the numbers
  have hMp : (M : ℝ) * p ≤ 2 := by
    have h1 : (⌊1 / p⌋₊ : ℝ) ≤ 1 / p := Nat.floor_le (by positivity)
    have h2 : (⌊1 / p⌋₊ : ℝ) * p ≤ 1 := by
      calc (⌊1 / p⌋₊ : ℝ) * p ≤ 1 / p * p := mul_le_mul_of_nonneg_right h1 hp.le
        _ = 1 := by field_simp
    rw [hMdef]; push_cast; linarith
  have hr0 : 0 < r := hp.trans_le hr
  have hwr : w ≤ (6 + 6 * K) * r := by rw [hwdef]; nlinarith
  have hwd : w ^ d ≤ (6 + 6 * K) ^ d * r ^ d := by
    rw [← Real.mul_rpow (by linarith) hr0.le]
    exact Real.rpow_le_rpow (by positivity) hwr hd
  have hnum : K * ((M : ℝ) * (Kr * p * q ^ 2 * w ^ d)) ≤
      2 * Kr * K * (2 + 2 * K) ^ 2 * (6 + 6 * K) ^ d * p ^ 2 * r ^ d := by
    have hq2 : q ^ 2 = (2 + 2 * K) ^ 2 * p ^ 2 := by rw [hqdef]; ring
    rw [hq2]
    have hw0 : 0 ≤ w ^ d := Real.rpow_nonneg (by linarith) d
    have hrd : 0 ≤ (6 + 6 * K) ^ d * r ^ d :=
      mul_nonneg (Real.rpow_nonneg (by linarith) d) (Real.rpow_nonneg hr0.le d)
    calc K * ((M : ℝ) * (Kr * p * ((2 + 2 * K) ^ 2 * p ^ 2) * w ^ d))
        = K * Kr * (2 + 2 * K) ^ 2 * p ^ 2 * ((M : ℝ) * p) * w ^ d := by ring
      _ ≤ K * Kr * (2 + 2 * K) ^ 2 * p ^ 2 * 2 * ((6 + 6 * K) ^ d * r ^ d) := by
          have h0 : 0 ≤ K * Kr * (2 + 2 * K) ^ 2 * p ^ 2 := by positivity
          calc K * Kr * (2 + 2 * K) ^ 2 * p ^ 2 * ((M : ℝ) * p) * w ^ d
              ≤ K * Kr * (2 + 2 * K) ^ 2 * p ^ 2 * 2 * w ^ d :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMp h0) hw0
            _ ≤ _ := mul_le_mul_of_nonneg_left hwd (by positivity)
      _ = 2 * Kr * K * (2 + 2 * K) ^ 2 * (6 + 6 * K) ^ d * p ^ 2 * r ^ d := by ring
  calc ν A ≤ ENNReal.ofReal K * (ν.prod volume) (E ∩ (A ×ˢ univ)) := hνA
    _ ≤ ENNReal.ofReal K * ((M : ENNReal) * (ENNReal.ofReal (Kr * p * q ^ 2 * w ^ d) * π J)) :=
        mul_le_mul' le_rfl hsum
    _ = ENNReal.ofReal (K * ((M : ℝ) * (Kr * p * q ^ 2 * w ^ d))) * π J := by
        rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul (Nat.cast_nonneg M),
          ENNReal.ofReal_natCast]
        ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hnum) le_rfl

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
