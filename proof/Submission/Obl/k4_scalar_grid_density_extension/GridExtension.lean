import Submission.Obl.k4_scalar_grid_density_extension.Interface
import Submission.Obl.k4_scalar_grid_density_extension.GridSlices
import Submission.Obl.k4_scalar_grid_density_extension.GridTypical
import Submission.Obl.k4_native_grid_profile_extension.DepthGrid
import Submission.Obl.k4_native_grid_profile_extension.Profiles.JointProfile
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ExponentLimit

/-!
# Scalar grid-to-real profile extension

Typical pure and joint densities on the clamped rational depth grid, with bounded
exponents, give along a subsequence a regular limiting profile and typical
densities at every depth in `[0, s] × [0, V]`. This is `gridExtensionStatement`.

The proof follows the native extension of o086 (subsequence on the countable grid,
increments, Lipschitz extension, squeezing between grid depths), with exact
nesting of observations replaced by the approximate refinement comparisons of
`GridSlices` and `GridTypical`.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_grid_density_extension

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- A constant multiple of a fixed negative power is power-small. -/
theorem isPowerSmall_of_le_const_mul (N : ℕ → ℝ) (hN : Tendsto N atTop atTop)
    (C ε : ℝ) (hε : 0 < ε) (b : ℕ → ℝ≥0∞)
    (hb : ∀ᶠ k in atTop, b k ≤ ENNReal.ofReal (C * N k ^ (-ε))) : IsPowerSmall N b := by
  refine ⟨ε / 2, by positivity, ?_⟩
  have hlarge : ∀ᶠ k in atTop, C ≤ N k ^ (ε / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < ε / 2)).comp hN).eventually (eventually_ge_atTop C)
  filter_upwards [hb, hlarge, hN.eventually (eventually_gt_atTop 0)] with k hbk hk hNk
  refine hbk.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    C * N k ^ (-ε) ≤ N k ^ (ε / 2) * N k ^ (-ε) :=
      mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hNk.le _)
    _ = N k ^ (-(ε / 2)) := by
      rw [← Real.rpow_add hNk]
      congr 1
      ring

theorem add_two_le_three_rpow {N a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) : N ^ a + 2 ≤ 3 * N ^ a := by
  have : 1 ≤ N ^ a := Real.one_le_rpow hN ha
  linarith

/-- Coarser joint densities exceed a power fraction of finer ones, typically. -/
theorem joint_approx_mono (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : ℕ → Measure Incidence) (hmass : ∀ k, μ k univ ≤ 1)
    (G : ℕ → ℝ → ℝ → JointSpace → ℝ≥0∞) {r u r' u' : ℝ} (hrr : r ≤ r') (huu : u ≤ u')
    (hG : ∀ k, Measurable (G k r u) ∧
      (μ k).map (aug (N k) r u) = jointReference.withDensity (G k r u))
    (hG' : ∀ k, Measurable (G k r' u') ∧
      (μ k).map (aug (N k) r' u') = jointReference.withDensity (G k r' u'))
    (ε : ℝ) (hε : 0 < ε) :
    IsPowerSmall N (fun k => μ k {p | G k r u (aug (N k) r u p) <
      ENNReal.ofReal (N k ^ (-ε)) * G k r' u' (aug (N k) r' u' p)}) := by
  apply isPowerSmall_of_le_const_mul N hN 4 ε hε
  apply Eventually.of_forall
  intro k
  have hNk : 0 < N k := by linarith [hN₂ k]
  have h := joint_coarse_low_mass (μ k) (by linarith [hN₂ k] : 1 ≤ N k) hrr huu _ _
    (hG k).1 (hG' k).1 (hG k).2 (hG' k).2 (ENNReal.ofReal (N k ^ (-ε)))
  calc
    _ ≤ ENNReal.ofReal (N k ^ (-ε)) * 4 * μ k univ := h
    _ ≤ ENNReal.ofReal (N k ^ (-ε)) * 4 * 1 := mul_le_mul' le_rfl (hmass k)
    _ = ENNReal.ofReal (4 * N k ^ (-ε)) := by
      rw [mul_one, mul_comm, ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- Finer joint densities lose at most the refinement exponent, typically. -/
theorem joint_approx_tail (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : ℕ → Measure Incidence) (hmass : ∀ k, μ k univ ≤ 1)
    (G : ℕ → ℝ → ℝ → JointSpace → ℝ≥0∞) {r u r' u' : ℝ} (hrr : r ≤ r') (huu : u ≤ u')
    (hG : ∀ k, Measurable (G k r u) ∧
      (μ k).map (aug (N k) r u) = jointReference.withDensity (G k r u))
    (hG' : ∀ k, Measurable (G k r' u') ∧
      (μ k).map (aug (N k) r' u') = jointReference.withDensity (G k r' u'))
    (ε : ℝ) (hε : 0 < ε) :
    IsPowerSmall N (fun k => μ k {p | G k r' u' (aug (N k) r' u' p) <
      ENNReal.ofReal (N k ^ (-(((r' - r) + (u' - u)) + ε))) * G k r u (aug (N k) r u p)}) := by
  apply isPowerSmall_of_le_const_mul N hN 9 ε hε
  apply Eventually.of_forall
  intro k
  have hN1 : 1 ≤ N k := by linarith [hN₂ k]
  have hNk : 0 < N k := by linarith
  have h := joint_fine_low_mass (μ k) hN1 hrr huu _ _
    (hG k).1 (hG' k).1 (hG k).2 (hG' k).2
    (ENNReal.ofReal (N k ^ (-(((r' - r) + (u' - u)) + ε))))
  refine h.trans ?_
  calc
    _ ≤ ENNReal.ofReal (N k ^ (-(((r' - r) + (u' - u)) + ε))) *
        ENNReal.ofReal ((N k ^ (r' - r) + 2) * (N k ^ (u' - u) + 2)) * 1 :=
      mul_le_mul' le_rfl (hmass k)
    _ = ENNReal.ofReal (N k ^ (-(((r' - r) + (u' - u)) + ε)) *
        ((N k ^ (r' - r) + 2) * (N k ^ (u' - u) + 2))) := by
      rw [mul_one, ← ENNReal.ofReal_mul (Real.rpow_nonneg hNk.le _)]
    _ ≤ ENNReal.ofReal (9 * N k ^ (-ε)) := by
      apply ENNReal.ofReal_le_ofReal
      have h1 := add_two_le_three_rpow hN1 (sub_nonneg.mpr hrr)
      have h2 := add_two_le_three_rpow hN1 (sub_nonneg.mpr huu)
      have hp1 : 0 ≤ N k ^ (r' - r) + 2 := by positivity
      calc
        N k ^ (-(((r' - r) + (u' - u)) + ε)) * ((N k ^ (r' - r) + 2) * (N k ^ (u' - u) + 2)) ≤
            N k ^ (-(((r' - r) + (u' - u)) + ε)) * ((3 * N k ^ (r' - r)) * (3 * N k ^ (u' - u))) := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hNk.le _)
          exact mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 9 * (N k ^ (-(((r' - r) + (u' - u)) + ε)) * N k ^ (r' - r) * N k ^ (u' - u)) := by
          ring
        _ = 9 * N k ^ (-ε) := by
          rw [← Real.rpow_add hNk, ← Real.rpow_add hNk]
          congr 2
          ring

/-- Coarser pure densities exceed a power fraction of finer ones, typically. -/
theorem pure_approx_mono (N : ℕ → ℝ) (hN₂ : ∀ k, 2 ≤ N k) (hN : Tendsto N atTop atTop)
    (μ : ℕ → Measure Incidence) (hmass : ∀ k, μ k univ ≤ 1)
    (g : ℕ → ℝ → ObsSpace → ℝ≥0∞) {r r' : ℝ} (hrr : r ≤ r')
    (hg : ∀ k, Measurable (g k r) ∧ (μ k).map (obs (N k) r) = reference.withDensity (g k r))
    (hg' : ∀ k, Measurable (g k r') ∧
      (μ k).map (obs (N k) r') = reference.withDensity (g k r'))
    (ε : ℝ) (hε : 0 < ε) :
    IsPowerSmall N (fun k => μ k {p | g k r (obs (N k) r p) <
      ENNReal.ofReal (N k ^ (-ε)) * g k r' (obs (N k) r' p)}) := by
  apply isPowerSmall_of_le_const_mul N hN 2 ε hε
  apply Eventually.of_forall
  intro k
  have h := pure_coarse_low_mass (μ k) (by linarith [hN₂ k] : 1 ≤ N k) hrr _ _
    (hg k).1 (hg' k).1 (hg k).2 (hg' k).2 (ENNReal.ofReal (N k ^ (-ε)))
  calc
    _ ≤ ENNReal.ofReal (N k ^ (-ε)) * 2 * μ k univ := h
    _ ≤ ENNReal.ofReal (N k ^ (-ε)) * 2 * 1 := mul_le_mul' le_rfl (hmass k)
    _ = ENNReal.ofReal (2 * N k ^ (-ε)) := by
      rw [mul_one, mul_comm, ENNReal.ofReal_mul (by norm_num)]
      norm_num

theorem clamp_eq_Clamp (B : ℝ) (q : ℚ) :
    clamp B q = Submission.Obl.k4_native_grid_profile_extension.Clamp B q := rfl

theorem clamp_zero {V : ℝ} (hV : 0 ≤ V) : clamp V 0 = 0 := by
  simp [clamp, hV]

/-- Child (2) of the o100 split: grid typicality extends to a regular profile and
typicality at every depth, along a subsequence. -/
theorem scalar_grid_extension : gridExtensionStatement := by
  intro N K μ hN₂ hN hK s V hs hV hmass hgrid
  obtain ⟨A, a, g, G, ha, ⟨hgP, hgJ⟩, hwinP, hwinJ⟩ := hgrid
  classical
  have hN₁ : ∀ k, 1 ≤ N k := fun k => by linarith [hN₂ k]
  let ar : ℕ → ℚ × ℚ → ℝ := fun k x => a k x.1 x.2
  have har (k : ℕ) (x : ℚ × ℚ) : ar k x ∈ Icc (-(A : ℝ)) (A : ℝ) :=
    abs_le.mp (ha k x.1 x.2)
  obtain ⟨ψ, lim, hψ, -, hlim⟩ := countable_bounded_subsequence ar
    (fun _ => -(A : ℝ)) (fun _ => (A : ℝ)) har
  let Ns : ℕ → ℝ := N ∘ ψ
  let μs : ℕ → Measure Incidence := μ ∘ ψ
  let gs : ℕ → ℝ → ObsSpace → ℝ≥0∞ := fun k => g (ψ k)
  let Gs : ℕ → ℝ → ℝ → JointSpace → ℝ≥0∞ := fun k => G (ψ k)
  have hNs₂ (k : ℕ) : 2 ≤ Ns k := hN₂ (ψ k)
  have hNs₁ (k : ℕ) : 1 ≤ Ns k := hN₁ (ψ k)
  have hNst : Tendsto Ns atTop atTop := hN.comp hψ.tendsto_atTop
  have hmasss (k : ℕ) : μs k univ ≤ 1 := (hmass (ψ k)).2
  have hnonzero : ¬ IsPowerSmall Ns (fun k => μs k univ) := by
    apply not_isPowerSmall_of_inverse_subpower hNst
    intro ε hε
    filter_upwards [hψ.tendsto_atTop.eventually (hK.2 ε hε)] with k hk
    have hKpos : 0 < K (ψ k) := lt_of_lt_of_le zero_lt_one (hK.1 (ψ k))
    have hNpos : 0 < N (ψ k) := by linarith [hN₂ (ψ k)]
    have hinv : N (ψ k) ^ (-ε) ≤ (K (ψ k))⁻¹ := by
      rw [Real.rpow_neg hNpos.le]
      simpa only [one_div] using one_div_le_one_div_of_le hKpos hk
    exact (ENNReal.ofReal_le_ofReal hinv).trans (hmass (ψ k)).1
  have hgPs (r : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (k : ℕ) : Measurable (gs k r) ∧
      (μs k).map (obs (Ns k) r) = reference.withDensity (gs k r) := hgP (ψ k) r hr hrs
  have hgJs (r u : ℝ) (hr : 0 ≤ r) (hrs : r ≤ s) (hu : 0 ≤ u) (huV : u ≤ V) (k : ℕ) :
      Measurable (Gs k r u) ∧
        (μs k).map (aug (Ns k) r u) = jointReference.withDensity (Gs k r u) :=
    hgJ (ψ k) r u hr hrs hu huV
  let dJ : ℝ × ℝ → (k : ℕ) → Incidence → ℝ≥0∞ := fun x k p =>
    Gs k x.1 x.2 (aug (Ns k) x.1 x.2 p)
  let dP : ℝ → (k : ℕ) → Incidence → ℝ≥0∞ := fun r k p => gs k r (obs (Ns k) r p)
  -- typical densities at the rational grid points
  have hgridJ (q v : ℚ) :
      HasTypicalDensity Ns μs (dJ (clamp s q, clamp V v)) (lim (q, v)) := by
    apply hasTypicalDensity_of_exponent_tendsto Ns hNs₁ μs (dJ (clamp s q, clamp V v))
      (fun k => a (ψ k) q v) (lim (q, v)) (hlim (q, v))
    intro τ hτ
    obtain ⟨c, hc, hbad⟩ := hwinJ q v τ hτ
    exact ⟨c, hc, hψ.tendsto_atTop.eventually hbad⟩
  have hgridP (q : ℚ) : HasTypicalDensity Ns μs (dP (clamp s q)) (lim (q, 0)) := by
    apply hasTypicalDensity_of_exponent_tendsto Ns hNs₁ μs (dP (clamp s q))
      (fun k => a (ψ k) q 0) (lim (q, 0)) (hlim (q, 0))
    intro τ hτ
    obtain ⟨c, hc, hbad⟩ := hwinP q τ hτ
    exact ⟨c, hc, hψ.tendsto_atTop.eventually hbad⟩
  -- approximate refinement on the rectangle
  have hmonoJ : ∀ x ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V, ∀ y ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V,
      x.1 ≤ y.1 → x.2 ≤ y.2 → ∀ ε : ℝ, 0 < ε → IsPowerSmall Ns (fun k =>
        μs k {p | dJ x k p < ENNReal.ofReal (Ns k ^ (-ε)) * dJ y k p}) := by
    intro x hx y hy hxy₁ hxy₂ ε hε
    exact joint_approx_mono Ns hNs₂ hNst μs hmasss Gs hxy₁ hxy₂
      (hgJs x.1 x.2 hx.1.1 hx.1.2 hx.2.1 hx.2.2) (hgJs y.1 y.2 hy.1.1 hy.1.2 hy.2.1 hy.2.2) ε hε
  have htailJ : ∀ x ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V, ∀ y ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V,
      x.1 ≤ y.1 → x.2 ≤ y.2 → ∀ ε : ℝ, 0 < ε → IsPowerSmall Ns (fun k =>
        μs k {p | dJ y k p < ENNReal.ofReal (Ns k ^ (-(((y.1 - x.1) + (y.2 - x.2)) + ε))) *
          dJ x k p}) := by
    intro x hx y hy hxy₁ hxy₂ ε hε
    exact joint_approx_tail Ns hNs₂ hNst μs hmasss Gs hxy₁ hxy₂
      (hgJs x.1 x.2 hx.1.1 hx.1.2 hx.2.1 hx.2.2) (hgJs y.1 y.2 hy.1.1 hy.1.2 hy.2.1 hy.2.2) ε hε
  -- the grid and its exponents
  let grid : Set (ℝ × ℝ) :=
    Submission.Obl.k4_native_grid_profile_extension.depthGrid s ×ˢ
      Submission.Obl.k4_native_grid_profile_extension.depthGrid V
  let rep : grid → ℚ × ℚ := fun x => (Classical.choose x.2.1, Classical.choose x.2.2)
  have hrep (x : grid) : clamp s (rep x).1 = x.1.1 ∧ clamp V (rep x).2 = x.1.2 :=
    ⟨Classical.choose_spec x.2.1, Classical.choose_spec x.2.2⟩
  have hrange (x : grid) : x.1 ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V := by
    constructor
    · rw [← Submission.Obl.k4_native_grid_profile_extension.closure_depthGrid hs.le]
      exact subset_closure x.2.1
    · rw [← Submission.Obl.k4_native_grid_profile_extension.closure_depthGrid hV.le]
      exact subset_closure x.2.2
  let a' : grid → ℝ := fun x => lim (rep x)
  have htypGrid (x : grid) : HasTypicalDensity Ns μs (dJ x.1) (a' x) := by
    have h := hgridJ (rep x).1 (rep x).2
    rw [(hrep x).1, (hrep x).2] at h
    exact h
  have hincrement (x y : grid) (h₁ : x.1.1 ≤ y.1.1) (h₂ : x.1.2 ≤ y.1.2) :
      0 ≤ a' y - a' x ∧ a' y - a' x ≤ (y.1.1 - x.1.1) + (y.1.2 - x.1.2) :=
    density_exponent_increment_approx Ns hNs₂ hNst μs (dJ x.1) (dJ y.1) (a' x) (a' y)
      ((y.1.1 - x.1.1) + (y.1.2 - x.1.2)) hnonzero (htypGrid x) (htypGrid y)
      (hmonoJ x.1 (hrange x) y.1 (hrange y) h₁ h₂)
      (htailJ x.1 (hrange x) y.1 (hrange y) h₁ h₂)
  have hcost : ∀ x y : grid, a' y - a' x ≤ jointProfileCost 1 (x, y) := by
    intro x y
    have hzR : max x.1.1 y.1.1 ∈ Submission.Obl.k4_native_grid_profile_extension.depthGrid s := by
      by_cases h : x.1.1 ≤ y.1.1
      · simpa only [max_eq_right h] using y.2.1
      · simpa only [max_eq_left (le_of_not_ge h)] using x.2.1
    have hzU : max x.1.2 y.1.2 ∈ Submission.Obl.k4_native_grid_profile_extension.depthGrid V := by
      by_cases h : x.1.2 ≤ y.1.2
      · simpa only [max_eq_right h] using y.2.2
      · simpa only [max_eq_left (le_of_not_ge h)] using x.2.2
    let z : grid := ⟨(max x.1.1 y.1.1, max x.1.2 y.1.2), hzR, hzU⟩
    have hxz := hincrement x z (le_max_left _ _) (le_max_left _ _)
    have hyz := hincrement y z (le_max_right _ _) (le_max_right _ _)
    have hmax (b c : ℝ) : max b c - b = max 0 (c - b) := by
      by_cases h : b ≤ c
      · rw [max_eq_right h, max_eq_right (sub_nonneg.mpr h)]
      · rw [max_eq_left (le_of_not_ge h), sub_self,
          max_eq_left (sub_nonpos.mpr (le_of_not_ge h))]
    have hdiff : (z.1.1 - x.1.1) + (z.1.2 - x.1.2) = jointProfileCost 1 (x, y) := by
      change (max x.1.1 y.1.1 - x.1.1) + (max x.1.2 y.1.2 - x.1.2) = _
      rw [hmax, hmax]
      simp [jointProfileCost]
    calc
      a' y - a' x ≤ a' z - a' x := by linarith [hyz.1]
      _ ≤ jointProfileCost 1 (x, y) := hxz.2.trans_eq hdiff
  obtain ⟨f, hf, hfa, hinc⟩ := extend_profile_with_cost a' (jointProfileCost 1) 2
    (continuous_jointProfileCost 1)
    (by
      intro x y
      convert jointProfileCost_le_dist (j := 1) (by norm_num) x y using 1
      norm_num)
    hcost
  have hclosure : closure grid = Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V := by
    rw [closure_prod_eq,
      Submission.Obl.k4_native_grid_profile_extension.closure_depthGrid hs.le,
      Submission.Obl.k4_native_grid_profile_extension.closure_depthGrid hV.le]
  have hinc' : ∀ x ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V,
      ∀ y ∈ Icc (0 : ℝ) s ×ˢ Icc (0 : ℝ) V, f y - f x ≤ jointProfileCost 1 (x, y) := by
    simpa only [hclosure] using hinc
  have hcoords := joint_profile_coordinate_increments hinc'
  -- typicality of joint densities at every depth
  have hjoint : ∀ r ∈ Icc (0 : ℝ) s, ∀ u ∈ Icc (0 : ℝ) V,
      HasTypicalDensity Ns μs (dJ (r, u)) (f (r, u)) := by
    apply hasTypicalDensity_on_rectangle_of_grid_approx Ns hNs₁ hNst μs dJ f hf.continuous
      hs.le hV.le (Submission.Obl.k4_native_grid_profile_extension.depthGrid s)
      (Submission.Obl.k4_native_grid_profile_extension.depthGrid V)
      (Submission.Obl.k4_native_grid_profile_extension.closure_depthGrid hs.le)
      (Submission.Obl.k4_native_grid_profile_extension.zero_mem_depthGrid hs.le)
      (Submission.Obl.k4_native_grid_profile_extension.right_mem_depthGrid hs.le)
      (Submission.Obl.k4_native_grid_profile_extension.closure_depthGrid hV.le)
      (Submission.Obl.k4_native_grid_profile_extension.zero_mem_depthGrid hV.le)
      (Submission.Obl.k4_native_grid_profile_extension.right_mem_depthGrid hV.le)
    · intro r hr u hu
      have hx := htypGrid (⟨(r, u), hr, hu⟩ : grid)
      rw [← hfa (⟨(r, u), hr, hu⟩ : grid)] at hx
      exact hx
    · intro u hu r hr r' hr' hrr ε hε
      exact hmonoJ (r, u) ⟨hr, hu⟩ (r', u) ⟨hr', hu⟩ hrr le_rfl ε hε
    · intro r hr u hu u' hu' huu ε hε
      exact hmonoJ (r, u) ⟨hr, hu⟩ (r, u') ⟨hr, hu'⟩ le_rfl huu ε hε
  -- typicality of pure densities at every depth
  have hpureGrid : ∀ r ∈ Submission.Obl.k4_native_grid_profile_extension.depthGrid s,
      HasTypicalDensity Ns μs (dP r) (f (r, 0)) := by
    rintro r ⟨q, rfl⟩
    have hr : Submission.Obl.k4_native_grid_profile_extension.Clamp s q ∈ Icc (0 : ℝ) s :=
      Submission.Obl.k4_native_grid_profile_extension.clamp_mem hs.le q
    have hJ := hgridJ q 0
    rw [clamp_zero hV.le] at hJ
    have hJ' := hjoint (clamp s q) hr 0 ⟨le_rfl, hV.le⟩
    have heq : lim (q, 0) = f (clamp s q, 0) :=
      typical_exponent_unique Ns hNs₂ hNst μs (dJ (clamp s q, 0)) hnonzero hJ hJ'
    have hP := hgridP q
    rw [heq] at hP
    exact hP
  have hpure : ∀ r ∈ Icc (0 : ℝ) s, HasTypicalDensity Ns μs (dP r) (f (r, 0)) := by
    apply hasTypicalDensity_on_Icc_of_grid_approx Ns hNs₁ hNst μs dP (fun r => f (r, 0))
      (hf.continuous.comp (continuous_id.prodMk continuous_const)) hs.le
      (Submission.Obl.k4_native_grid_profile_extension.depthGrid s)
      (Submission.Obl.k4_native_grid_profile_extension.closure_depthGrid hs.le)
      (Submission.Obl.k4_native_grid_profile_extension.zero_mem_depthGrid hs.le)
      (Submission.Obl.k4_native_grid_profile_extension.right_mem_depthGrid hs.le) hpureGrid
    intro r hr r' hr' hrr ε hε
    exact pure_approx_mono Ns hNs₂ hNst μs hmasss gs hrr (hgPs r hr.1 hr.2) (hgPs r' hr'.1 hr'.2)
      ε hε
  -- assemble
  refine ⟨ψ, hψ, fun r u => f (r, u), ⟨?_, ?_⟩, gs, Gs, ?_, ?_, ?_, ?_⟩
  · intro r r' u hr hrr hr's hu huV
    exact hcoords.1 r r' u ⟨⟨hr, hrr.trans hr's⟩, hu, huV⟩
      ⟨⟨hr.trans hrr, hr's⟩, hu, huV⟩ hrr
  · intro r u u' hr hrs hu huu hu'V
    have h := hcoords.2 r u u' ⟨⟨hr, hrs⟩, hu, huu.trans hu'V⟩
      ⟨⟨hr, hrs⟩, hu.trans huu, hu'V⟩ huu
    simpa only [one_mul] using h
  · intro k r hr hrs
    exact hgPs r hr hrs k
  · intro k r u hr hrs hu huV
    exact hgJs r u hr hrs hu huV k
  · intro r τ hr hrs hτ
    exact hpure r ⟨hr, hrs⟩ τ hτ
  · intro r u τ hr hrs hu huV hτ
    exact hjoint r ⟨hr, hrs⟩ u ⟨hu, huV⟩ τ hτ

end Submission.Obl.k4_scalar_grid_density_extension
