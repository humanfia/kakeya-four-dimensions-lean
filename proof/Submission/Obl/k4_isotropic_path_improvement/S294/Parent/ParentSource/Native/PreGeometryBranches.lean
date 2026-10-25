-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PreGeometryBranches, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PreGeometryBranches.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PreGeometryBranches.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PreGeometryBranches.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PointwisePureCore
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeValueCapNumerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceValueBranches

/-! Actual original native value branches before geometric state selection.
Their geometric envelope contains no entropy palette parameter and no fixed
profile tolerance. The depth test is supplied by the actual path. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Analytic
open scoped ENNReal BigOperators

def OriginalValueBranchFamily (d : ProblemData) (k : ℕ) (p : PathData (d.W k))
    (H : Fin (d.W k) → Set Event) (mid : ℕ) (K : ℝ) (q e R : ℕ) : Prop :=
    ∃ M : ℕ, ∃ center : Fin M → ℝ,
    ∃ U V : Fin p.C → Fin M → Set Event, ∃ H' : Fin (d.W k) → Set Event,
      (M : ℝ) ≤ K ^ 10 ∧
      (∀ b a, MeasurableSet (U b a) ∧ MeasurableSet (V b a)) ∧
      (∀ b, Pairwise fun a a' => Disjoint (V b a) (V b a')) ∧
      (∀ b a, V b a ⊆ U b a ∧ U b a ⊆ H (p.γ b) ∩ p.F b) ∧
      (∀ b a z, z ∈ U b a → |packetSignal (d.N k) p b z - center a| ≤ (K ^ 6)⁻¹) ∧
      (∀ w, MeasurableSet (H' w) ∧ H' w ⊆ H w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w \ H' w)) ≤
        ENNReal.ofReal (K ^ 10) * ENNReal.ofReal ((K ^ q)⁻¹) ∧
      (∀ b, p.lev b = mid → ∀ a, (V b a).Nonempty →
        ENNReal.ofReal ((K ^ q)⁻¹) *
          (ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹) * d.ν k (p.γ b) (p.A b)) ≤
            ((d.ν k (p.γ b)).prod volume) (U b a)) ∧
      (∀ b, p.lev b = mid → ∀ a, (V b a).Nonempty →
        NativeQuarterBranchCover e R K (packetNativeValueTest (d.N k) (d.B k) p b (center a))
          (((d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹))⁻¹) •
            (((d.ν k (p.γ b)).prod volume).restrict (U b a)))
          (fun z j => packetNativeCubePoint (d.N k) (d.B k) p b z j.castSucc)) ∧
      ∀ w z, z ∈ H' w → ∃ b a, p.lev b = mid ∧ p.γ b = w ∧ z ∈ V b a

/-- Choose the native branch exponents before the original problem, path,
residual and actual depth arrive. The only density cost is the freely
chosen pure tolerance tau+epsilon. -/
theorem exists_original_pre_geometry_value_branches (q : ℕ) (hq : 7 ≤ q) :
    ∃ e R : ℕ, 4 ≤ e ∧ 1 ≤ R ∧
    ∀ {T : Type*} {d : ProblemData}, d.Valid →
    ∀ {k : ℕ} {p : PathData (d.W k)}
      {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ},
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
    ∀ {H : Fin (d.W k) → Set Event} {u : T → ℝ} {τ ε : ℝ},
    ∀ Q : PreparedAngularPath d k p m H u τ, Q.uniformPureCeiling ε → 0 ≤ τ + ε →
    ∀ J : Fin (d.W k) → Set Event, (∀ w, MeasurableSet (J w)) →
      (∀ w, J w ⊆ d.E k w) → (∀ w, J w ⊆ Q.base w) →
      (∀ w, J w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
    ∀ mid : ℕ, mid < m → 0 ≤ p.r mid → p.r mid ≤ d.L →
    ∃ J0 : Fin (d.W k) → Set Event,
      (∀ w, MeasurableSet (J0 w)) ∧ (∀ w, J0 w ⊆ J w) ∧
      (∀ w, (((d.ν k w).prod volume).restrict (J0 w)) =
        (((d.ν k w).prod volume).restrict (J w))) ∧
      OriginalValueBranchFamily d k p J0 mid
        (nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + ε)) q e R := by
  obtain ⟨e, R, he, hR, hfactory⟩ := source_heavy_original_value_branches q
  refine ⟨e, R, he, hR, ?_⟩
  intro T d hd k p κ₁ m s δ₀ Mp Dp σ hp H u τ ε Q hQ htol J hJ hJE hJbase hterminal
    mid hmid hr hrL
  obtain ⟨J0, hJ0, hsub, heq, hpoint⟩ := Q.exists_pointwise_pure_core hd hQ J hJ hJE hJbase hr hrL
  let K := nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + ε)
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  have hNpos : 0 < d.N k := zero_lt_one.trans_le hN
  obtain ⟨hKlarge, hκK, hmaxK, hpowerK⟩ := native_pre_geometry_envelope_bounds hp.1 hN htol
  have hK : 2 ≤ K := by dsimp only [K]; linarith
  have hK1 : 1 ≤ K := by linarith
  have hscale : δ (d.N k) (p.r mid) * (K ^ 6)⁻¹ ≤ δ (d.N k) (p.r mid) := by
    have hwidth : 0 ≤ δ (d.N k) (p.r mid) := by unfold δ; positivity
    have hinv := inv_le_one_of_one_le₀ (one_le_pow₀ hK1 (n := 6))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hinv hwidth
  refine ⟨J0, hJ0, hsub, heq, ?_⟩
  apply hfactory hd hp J0 hJ0 (fun w => (hsub w).trans (hterminal w)) mid hmid
    K (p.r mid) hK hκK hr hrL le_rfl hscale
    (ENNReal.ofReal (d.N k ^ (-d.f (p.r mid) + (τ + ε))))
  · simpa only [add_assoc, obs, δ, x,
      Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.obs,
      Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.δ,
      Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.x] using hpoint
  · intro b hb
    exact native_original_value_cap_budget hNpos hp.1 hKlarge hmaxK hpowerK hq

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
