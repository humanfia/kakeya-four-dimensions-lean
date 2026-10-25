-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketNativeCube, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketNativeCube.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketNativeCube.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketNativeCube.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketNativeCube.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCube
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.NativeCubeCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketPhysical

/-! # Unit-base native equations from the actual original path -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set MvPolynomial
open Analytic k4_quadratic_atlas_normalization

noncomputable section

def packetNativeCubePoint {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (q : Event) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (nativeCubePoint (3 * p.κ) (B (p.γ b)) (δ Nk (p.r (p.lev b)))
    (xp (normalizedPacketLine p b q.1) (packetTime p b q)))

def packetNativeCubeTest {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) : Poly :=
  nativeCubeTest (3 * p.κ) (B (p.γ b)) (δ Nk (p.r (p.lev b)))
    (normalizedPacketTest Nk p b)

theorem packetNativeCube_base_eq {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (q : Event) :
    WithLp.toLp 2 (fun j : Fin 3 => packetNativeCubePoint Nk B p b q j.castSucc) =
      nativeCubeBase (3 * p.κ) (packetBase p b q) := by
  rw [packetBase_eq_normalizedPoint]
  ext j
  fin_cases j <;> rfl

/-- Any original polynomial, in the same fine native coordinates and
fine signal unit. In particular this can be an OLD packet's signal. -/
def packetNativeCubePolynomial {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (S : Poly) : Poly :=
  nativeCubeTest (3 * p.κ) (B (p.γ b)) (δ Nk (p.r (p.lev b)))
    ((nativeOldBaseFrame p b).normTest (δ Nk (p.r (p.lev b))) S)

theorem packetNativeCubePolynomial_degree {W : ℕ} (Nk : ℝ) (B : Fin W → ℝ)
    (p : Native.PathData W) (b : Fin p.C) (S : Poly) :
    (packetNativeCubePolynomial Nk B p b S).totalDegree ≤ S.totalDegree :=
  (nativeCubeTest_totalDegree _ _ _ _).trans
    ((nativeOldBaseFrame p b).totalDegree_normTest_le _ _)

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem packetNativeCubeTest_degree (b : Fin p.C) :
    (packetNativeCubeTest Nk B p b).totalDegree ≤ 2 :=
  (nativeCubeTest_totalDegree _ _ _ _).trans (normalizedPacketTest_degree hp b)

/-- An original packet incidence has actual normalized time in [0,1]. -/
theorem packetTime_unit (b : Fin p.C) {q : Event} (hq : q ∈ p.F b) :
    packetTime p b q ∈ Icc (0 : ℝ) 1 := by
  have hs := (path_packet_support hp b hq).2.2.1
  let F := nativeOldBaseFrame p b
  have hFq : 0 < F.q := by dsimp [F, nativeOldBaseFrame]; positivity
  have hend : ((p.j b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b) = F.t₀ + F.q := by
    dsimp [F, nativeOldBaseFrame]
    ring
  change 0 ≤ (q.2 - F.t₀) / F.q ∧ (q.2 - F.t₀) / F.q ≤ 1
  constructor
  · exact div_nonneg (sub_nonneg.mpr hs.1) hFq.le
  · apply (div_le_one hFq).mpr
    rw [hend] at hs
    linarith [hs.2]

/-- The same original selected incidence supplies the lower native
hidden derivative, before the explicit hidden-unit rescaling. -/
theorem normalizedPacket_selected_lower (b : Fin p.C) {q : Event} (hq : q ∈ p.F b) :
    B (p.γ b) / δ Nk (p.r (p.lev b)) / p.κ ≤
      |eval (xp (normalizedPacketLine p b q.1) (packetTime p b q))
        (pderiv 3 (normalizedPacketTest Nk p b))| := by
  let F := nativeOldBaseFrame p b
  have hFq : F.q ≠ 0 := by dsimp [F, nativeOldBaseFrame]; positivity
  have hD : IsUnit F.D.det := isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 b).2.2.1
  have ht : F.t₀ + F.q * ((q.2 - F.t₀) / F.q) = q.2 := by field_simp; ring
  apply F.normTest_lower hFq (by unfold δ; positivity) (p.R b)
    (F.normTraj q.1) ((q.2 - F.t₀) / F.q)
  rw [F.denormTraj_normTraj hFq hD, ht]
  exact (path_packet_support hp b hq).2.2.2

theorem packet_frame_original_polynomial_value (b : Fin p.C) (S : Poly) (q : Event) :
    eval (xp (normalizedPacketLine p b q.1) (packetTime p b q))
      ((nativeOldBaseFrame p b).normTest (δ Nk (p.r (p.lev b))) S) =
        (δ Nk (p.r (p.lev b)))⁻¹ * eval (xp q.1 q.2) S := by
  let F := nativeOldBaseFrame p b
  have hFq : F.q ≠ 0 := by dsimp [F, nativeOldBaseFrame]; positivity
  have hD : IsUnit F.D.det := isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 b).2.2.1
  have ht : F.t₀ + F.q * ((q.2 - F.t₀) / F.q) = q.2 := by field_simp; ring
  have hh := F.eval_normTest hFq (δ Nk (p.r (p.lev b))) S
    (F.normTraj q.1) ((q.2 - F.t₀) / F.q)
  rw [F.denormTraj_normTraj hFq hD, ht] at hh
  exact hh

/-- All values and hidden derivatives refer to the SAME original point.
For an old signal the second derivative gains the actual fine width;
its coefficient envelope and absolute signal value play no role. -/
theorem packetNativeCubePolynomial_original_values (b : Fin p.C)
    (hB : 0 < B (p.γ b)) (S : Poly) (q : Event) :
    eval (fun j => packetNativeCubePoint Nk B p b q j) (packetNativeCubePolynomial Nk B p b S) =
        (δ Nk (p.r (p.lev b)))⁻¹ * eval (xp q.1 q.2) S ∧
      eval (fun j => packetNativeCubePoint Nk B p b q j)
        (pderiv 3 (packetNativeCubePolynomial Nk B p b S)) =
        eval (xp q.1 q.2) (pderiv 3 S) / B (p.γ b) ∧
      eval (fun j => packetNativeCubePoint Nk B p b q j)
        (pderiv 3 (pderiv 3 (packetNativeCubePolynomial Nk B p b S))) =
        (δ Nk (p.r (p.lev b)) / B (p.γ b) ^ 2) * eval (xp q.1 q.2) (pderiv 3 (pderiv 3 S)) := by
  have hκ : 0 < 3 * p.κ := by linarith [hp.1]
  have hδ : 0 < δ Nk (p.r (p.lev b)) := by unfold δ; positivity
  let x := xp (normalizedPacketLine p b q.1) (packetTime p b q)
  have hh := nativeCubeTest_derivatives hκ.ne' hB.ne' hδ.ne'
    ((nativeOldBaseFrame p b).normTest (δ Nk (p.r (p.lev b))) S) x
  refine ⟨?_, ?_, ?_⟩
  · change eval (nativeCubePoint _ _ _ x) (nativeCubeTest _ _ _ _) = _
    rw [nativeCubeTest_eval hκ.ne' hB.ne' hδ.ne']
    exact packet_frame_original_polynomial_value hp b S q
  · change eval (nativeCubePoint _ _ _ x) (pderiv 3 (nativeCubeTest _ _ _ _)) = _
    rw [hh.1, Submission.Lib.K4ChartLifting.Frame.pderiv_normTest]
    dsimp only [x]
    rw [packet_frame_original_polynomial_value hp b (pderiv 3 S) q]
    field_simp
  · change eval (nativeCubePoint _ _ _ x) (pderiv 3 (pderiv 3 (nativeCubeTest _ _ _ _))) = _
    rw [hh.2, Submission.Lib.K4ChartLifting.Frame.pderiv_normTest,
      Submission.Lib.K4ChartLifting.Frame.pderiv_normTest]
    dsimp only [x]
    rw [packet_frame_original_polynomial_value hp b (pderiv 3 (pderiv 3 S)) q]
    field_simp

/-- Old whole-block hidden bounds imply the fine-native signal bounds
needed for root correction. Only the actual width ratio is used. -/
theorem packetNativeCubePolynomial_hidden_bounds (b : Fin p.C)
    (hB : 0 < B (p.γ b)) (S : Poly) (q : Event) {K oldWidth : ℝ}
    (hK : 0 ≤ K) (holdWidth : 0 < oldWidth)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ oldWidth)
    (hfirst : |eval (xp q.1 q.2) (pderiv 3 S)| ≤ K * B (p.γ b))
    (hsecond : |eval (xp q.1 q.2) (pderiv 3 (pderiv 3 S))| ≤
      K * B (p.γ b) ^ 2 / oldWidth) :
    |eval (fun j => packetNativeCubePoint Nk B p b q j)
      (pderiv 3 (packetNativeCubePolynomial Nk B p b S))| ≤ K ∧
      |eval (fun j => packetNativeCubePoint Nk B p b q j)
        (pderiv 3 (pderiv 3 (packetNativeCubePolynomial Nk B p b S)))| ≤ K := by
  have hδ : 0 < δ Nk (p.r (p.lev b)) := by unfold δ; positivity
  obtain ⟨_, hid1, hid2⟩ := packetNativeCubePolynomial_original_values hp b hB S q
  rw [hid1, hid2, abs_div, abs_of_pos hB, abs_mul,
    abs_of_pos (div_pos hδ (sq_pos_of_pos hB))]
  refine ⟨(div_le_iff₀ hB).mpr hfirst, ?_⟩
  calc
    _ ≤ (δ Nk (p.r (p.lev b)) / B (p.γ b) ^ 2) *
        (K * B (p.γ b) ^ 2 / oldWidth) :=
      mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ = K * (δ Nk (p.r (p.lev b)) / oldWidth) := by field_simp
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left ((div_le_one holdWidth).mpr hwidth) hK
    _ = K := mul_one _

/-- The actual OLD path test has bounded hidden derivatives on a fine
native sheet whenever its original incidence lies in both packets. -/
theorem packetNativeCube_old_signal_bounds (a b : Fin p.C)
    (hB : 0 < B (p.γ b)) (hγ : p.γ b = p.γ a)
    (hwidth : δ Nk (p.r (p.lev b)) ≤ δ Nk (p.r (p.lev a)))
    {q : Event} (hq : q ∈ p.F a) :
    |eval (fun j => packetNativeCubePoint Nk B p b q j)
      (pderiv 3 (packetNativeCubePolynomial Nk B p b (p.R a)))| ≤ p.κ ∧
      |curvature (packetNativeCubePolynomial Nk B p b (p.R a)) 3| ≤ p.κ := by
  have hκ : 0 ≤ p.κ := by linarith [hp.1]
  have hs := path_packet_support hp a hq
  rcases (hp.2.2.2.2.2.2.2 a).2.2 with
    ⟨_, _, _, _, hdeg, _, _, _, _, hwhole, _, _⟩
  have hh := (hwhole q.1 hs.2.1).2.2 q.2 hs.2.2.1
  have hfirst : |eval (xp q.1 q.2) (pderiv 3 (p.R a))| ≤ p.κ * B (p.γ b) := by
    simpa only [hγ, Native.x, xp] using hh.2.2.1
  have hsecond : |eval (xp q.1 q.2) (pderiv 3 (pderiv 3 (p.R a)))| ≤
      p.κ * B (p.γ b) ^ 2 / δ Nk (p.r (p.lev a)) := by
    simpa only [hγ, Native.x, xp, Native.δ, δ] using hh.2.2.2
  obtain ⟨h1, h2⟩ := packetNativeCubePolynomial_hidden_bounds hp b hB (p.R a) q hκ
    (by unfold δ; positivity) hwidth hfirst hsecond
  rw [second_pderiv_eq_curvature _
    ((packetNativeCubePolynomial_degree Nk B p b (p.R a)).trans hdeg) 3, eval_C] at h2
  exact ⟨h1, h2⟩

/-- The ACTUAL original source point lies in a unit base cube, while its
normalized hidden equation has bounded value, derivative and curvature
scale independently of every input format exponent. -/
theorem packetNativeCube_source_bounds (b : Fin p.C) (hB : 0 < B (p.γ b))
    {q : Event} (hq : q ∈ p.F b) :
    (fun j : Fin 3 => packetNativeCubePoint Nk B p b q j.castSucc) ∈ Icc 0 1 ∧
      |eval (fun j => packetNativeCubePoint Nk B p b q j) (packetNativeCubeTest Nk B p b)| ≤ p.κ ∧
      (3 * p.κ)⁻¹ ≤ |eval (fun j => packetNativeCubePoint Nk B p b q j)
        (pderiv 3 (packetNativeCubeTest Nk B p b))| ∧
      |eval (fun j => packetNativeCubePoint Nk B p b q j)
        (pderiv 3 (packetNativeCubeTest Nk B p b))| ≤ 3 * p.κ ∧
      |eval (fun j => packetNativeCubePoint Nk B p b q j)
        (pderiv 3 (pderiv 3 (packetNativeCubeTest Nk B p b)))| ≤ 3 * p.κ := by
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hδ : 0 < δ Nk (p.r (p.lev b)) := by unfold δ; positivity
  have hs := path_packet_support hp b hq
  have hb := normalizedPacket_native_bounds hp b q.1 hs.2.1 (packetTime p b q)
    (packetTime_unit hp b hq)
  have hn : ‖y (normalizedPacketLine p b q.1) (packetTime p b q)‖ ≤ 3 * p.κ := by
    linarith [norm_nonneg (v (normalizedPacketLine p b q.1))]
  have hxy1 : |xp (normalizedPacketLine p b q.1) (packetTime p b q) 1| ≤ 3 * p.κ :=
    (PiLp.norm_apply_le (y (normalizedPacketLine p b q.1) (packetTime p b q)) 0).trans hn
  have hxy2 : |xp (normalizedPacketLine p b q.1) (packetTime p b q) 2| ≤ 3 * p.κ :=
    (PiLp.norm_apply_le (y (normalizedPacketLine p b q.1) (packetTime p b q)) 1).trans hn
  refine ⟨nativeCube_base_mem_unit (by positivity) _ (packetTime_unit hp b hq) hxy1 hxy2, ?_, ?_⟩
  · change |eval (nativeCubePoint (3 * p.κ) (B (p.γ b)) (δ Nk (p.r (p.lev b))) _)
      (nativeCubeTest _ _ _ _)| ≤ p.κ
    rw [nativeCubeTest_eval (by positivity) hB.ne' hδ.ne']
    exact hb.2.1
  · apply nativeCubeTest_native_bounds (by positivity) hB hδ
      (normalizedPacketTest Nk p b) _
    · exact hb.2.2.1.trans (by gcongr; linarith)
    · exact hb.2.2.2.trans (by gcongr; linarith)
    · exact (show B (p.γ b) / δ Nk (p.r (p.lev b)) / (3 * p.κ) ≤
          B (p.γ b) / δ Nk (p.r (p.lev b)) / p.κ by gcongr; linarith).trans
        (normalizedPacket_selected_lower hp b hq)

/-- An actual occupied original packet supplies a global constant
curvature bound for its unit-native quadratic. -/
theorem packetNativeCube_curvature (hNk : 0 < Nk) (b : Fin p.C)
    (hB : 0 < B (p.γ b)) : |curvature (packetNativeCubeTest Nk B p b) 3| ≤ 3 * p.κ := by
  obtain ⟨q, hq⟩ := nonempty_of_measure_ne_zero (hp.packet_mass_pos hNk b).ne'
  have hh := (packetNativeCube_source_bounds hp b hB hq).2.2.2.2
  rw [second_pderiv_eq_curvature _ (packetNativeCubeTest_degree hp b) 3, eval_C] at hh
  exact hh

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
