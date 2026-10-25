/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/NestedNodes.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_linear_critical_extremizers.Profile

/-!
Choice of actual critical depths and the normalization of outer and
remaining horizon costs, for the nested-path step of Section 4.1.
-/

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open Set Filter
open scoped Topology
open Submission.Obl.k4_scalar_linear_critical_extremizers

/-- Tilt tolerances may vanish more slowly than uniform profile errors.
This construction also stays positive when an error is exactly zero. -/
theorem exists_slow_tilt_tolerances (err tol : ℕ → ℝ)
    (herr : ∀ i, 0 ≤ err i) (htol : ∀ i, 0 < tol i)
    (herrlim : Tendsto err atTop (𝓝 0)) (htollim : Tendsto tol atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ i, 0 < ε i) ∧ Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun i => err i / ε i) atTop (𝓝 0) := by
  let ε := fun i => Real.sqrt (err i) + tol i
  have hε (i : ℕ) : 0 < ε i := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (htol i)
  have hsqrt : Tendsto (fun i => Real.sqrt (err i)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp herrlim
  have hlim : Tendsto ε atTop (𝓝 0) := by simpa [ε] using hsqrt.add htollim
  refine ⟨ε, hε, hlim, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsqrt
    (fun i => div_nonneg (herr i) (hε i).le)
  intro i
  apply (div_le_iff₀ (hε i)).2
  have hs := Real.sq_sqrt (herr i)
  have hp := mul_nonneg (Real.sqrt_nonneg (err i)) (htol i).le
  dsimp [ε]
  nlinarith

/-- Minimize a slightly tilted profile at each actual outer index.
The endpoints converge to the prescribed target, rather than merely
lying at approximately the right depth in a limiting object. -/
theorem exists_tilted_nodes_tendsto (f : ℕ → ℝ → ℝ)
    (dstar r : ℝ) (err ε : ℕ → ℝ) (hr : 0 ≤ r)
    (hf : ∀ i, ContinuousOn (f i) (Icc 0 r))
    (hε : ∀ i, 0 < ε i)
    (herror : ∀ i x, x ∈ Icc 0 r → |f i x - f i 0 - dstar * x| ≤ err i)
    (hratio : Tendsto (fun i => err i / ε i) atTop (𝓝 0)) :
    ∃ depth : ℕ → ℝ, (∀ i, depth i ∈ Icc 0 r) ∧
      (∀ i x, x ∈ Icc 0 (depth i) →
        f i (depth i) - f i x ≤ (dstar + ε i) * (depth i - x)) ∧
      Tendsto depth atTop (𝓝 r) := by
  have hchoose (i : ℕ) := exists_tilted_profile_minimum hr (hf i) (dstar + ε i)
  choose depth hdepth hmin hcap using hchoose
  have hdist (i : ℕ) : r - depth i ≤ 2 * err i / ε i := by
    exact tilted_profile_minimum_near_endpoint (hε i)
      (abs_le.mp (herror i _ (hdepth i))).1
      (abs_le.mp (herror i r ⟨hr, le_rfl⟩)).2
      (hmin i r ⟨hr, le_rfl⟩)
  have hu : Tendsto (fun i => 2 * err i / ε i) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hratio.const_mul 2
  have hz : Tendsto (fun i => r - depth i) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun i => sub_nonneg.mpr (hdepth i).2) hdist
  refine ⟨depth, hdepth, hcap, ?_⟩
  have := (tendsto_const_nhds (x := r)).sub hz
  simpa only [sub_sub_cancel, sub_zero] using this

/-- Composition sandwiches the outer horizon between quantities with
the same limit. Normalization divides by the actual depth at each term. -/
theorem outer_cost_maximizes (H outer tailRate outerRate depth : ℕ → ℝ)
    (k r : ℝ) (hr : 0 < r)
    (hH : Tendsto H atTop (𝓝 k)) (htail : Tendsto tailRate atTop (𝓝 k))
    (houter : Tendsto outerRate atTop (𝓝 k)) (hdepth : Tendsto depth atTop (𝓝 r))
    (hlower : ∀ i, H i ≤ outer i + tailRate i * (1 - depth i))
    (hupper : ∀ i, outer i ≤ outerRate i * depth i) :
    Tendsto outer atTop (𝓝 (k * r)) ∧
      Tendsto (fun i => outer i / depth i) atTop (𝓝 k) := by
  have hlo : Tendsto (fun i => H i - tailRate i * (1 - depth i))
      atTop (𝓝 (k * r)) := by
    convert hH.sub (htail.mul (tendsto_const_nhds.sub hdepth)) using 2
    ring
  have hhi := houter.mul hdepth
  have hlim : Tendsto outer atTop (𝓝 (k * r)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
      (fun i => by linarith [hlower i]) hupper
  refine ⟨hlim, ?_⟩
  have heq : k * r / r = k := by field_simp
  have hdiv := hlim.div hdepth hr.ne'
  rw [heq] at hdiv
  exact hdiv.congr' (Eventually.of_forall fun _ => rfl)

/-- A remaining problem is again maximizing after its individual
length normalization. Its outer parent cost and remaining length keep
their actual values throughout the sequence. -/
theorem remaining_cost_maximizes (H parent remaining rate length : ℕ → ℝ)
    (k r : ℝ) (hr : r < 1)
    (hH : Tendsto H atTop (𝓝 k))
    (hparent : Tendsto parent atTop (𝓝 (k * r)))
    (hrate : Tendsto rate atTop (𝓝 k))
    (hlength : Tendsto length atTop (𝓝 (1 - r)))
    (hlower : ∀ i, H i ≤ parent i + remaining i)
    (hupper : ∀ i, remaining i ≤ rate i * length i) :
    Tendsto remaining atTop (𝓝 (k * (1 - r))) ∧
      Tendsto (fun i => remaining i / length i) atTop (𝓝 k) := by
  have hlo : Tendsto (fun i => H i - parent i) atTop (𝓝 (k * (1 - r))) := by
    convert hH.sub hparent using 2
    ring
  have hhi := hrate.mul hlength
  have hlim : Tendsto remaining atTop (𝓝 (k * (1 - r))) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
      (fun i => by linarith [hlower i]) hupper
  refine ⟨hlim, ?_⟩
  have hne : 1 - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
  have heq : k * (1 - r) / (1 - r) = k := by field_simp
  have hdiv := hlim.div hlength hne
  rw [heq] at hdiv
  exact hdiv.congr' (Eventually.of_forall fun _ => rfl)

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
