-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoreSourceCaps, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoreSourceCaps.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoreSourceCaps.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ValueBranchData
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreCoordinatesCap
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketNativeLines

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native Analytic
open scoped ENNReal

noncomputable section

/-- The original value-entry law uses the complete old assignment and
block length. Its denominator is independent of all later core choices. -/
def ValueBranchData.entryLaw
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R) (b : Fin p.C) (a : Fin V.count) :
    Measure Event :=
  (d.ν k (p.γ b) (p.A b) * ENNReal.ofReal (((2 : ℝ) ^ p.T mid)⁻¹))⁻¹ •
    (((d.ν k (p.γ b)).prod volume).restrict (V.outer b a))

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- The actual pure ceiling gives a continuous cap for every original
value entry, before any later geometric or intercept selection. -/
theorem ValueBranchData.entryLaw_native_cap
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (a : Fin V.count) :
    (V.entryLaw b a).map (fun z => WithLp.toLp 2
      (fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b z j.castSucc)) ≤
        ENNReal.ofReal (K ^ 7) • volume := by
  let ρ := ((d.ν k (p.γ b)).prod volume).restrict (V.outer b a)
  have hN : 0 < d.N k := (by norm_num : (0 : ℝ) < 2).trans_le (hd.1 k)
  have hKpos : 0 < K := by linarith
  have hKone : 1 ≤ K := by linarith
  have hρ : ρ ≤ d.μ k (p.γ b) :=
    Measure.restrict_mono_set _ (fun z hz => hHE _ ((V.subset b a).2 hz).1)
  have hsupport : ∀ᵐ z ∂ρ, z ∈ V.outer b a := ae_restrict_mem (V.measurable b a).1
  have hbase : ∀ᵐ z ∂ρ, z ∈ Q.base (p.γ b) :=
    hsupport.mono (fun z hz => hHbase _ ((V.subset b a).2 hz).1)
  have hF : ∀ᵐ z ∂ρ, z ∈ p.F b :=
    hsupport.mono (fun z hz => ((V.subset b a).2 hz).2)
  have hB : 0 < d.B k (p.γ b) := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, hformat, _⟩
    obtain ⟨M, D, hformat⟩ := hformat
    exact ((hformat k).2.2.2.1 (p.γ b)).2.1
  have hbin : ∀ᵐ z ∂ρ,
      |MvPolynomial.eval (fun j => packetNativeCubePoint (d.N k) (d.B k) p b z j)
        (packetNativeCubeTest (d.N k) (d.B k) p b) - V.center a| ≤ (K ^ 6)⁻¹ := by
    filter_upwards [hsupport] with z hz
    have heq := (packetNativeCubePolynomial_original_values hp b hB (p.R b) z).1
    change MvPolynomial.eval (fun j => packetNativeCubePoint (d.N k) (d.B k) p b z j)
      (packetNativeCubeTest (d.N k) (d.B k) p b) = packetSignal (d.N k) p b z at heq
    rw [heq]
    exact V.value b a z hz
  have hscale : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r (p.lev b)) := by rw [hb]
  have hεwidth : δ (d.N k) (p.r (p.lev b)) * (K ^ 6)⁻¹ ≤ δ (d.N k) (p.r mid) := by
    rw [hb]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (inv_le_one_of_one_le₀ (one_le_pow₀ hKone (n := 6)))
      (show 0 ≤ δ (d.N k) (p.r mid) by unfold δ; positivity)
  have hcap := source_value_bin_native_cube_cap hd hp b (p.r mid) hr hrL hscale
    (show 0 < (K ^ 6)⁻¹ by positivity) hεwidth ρ hρ _ (V.center a) hF hbin
    (hpure.ceiling _ ρ hρ hbase _ hr hrL)
  have hbudget := native_original_value_cap_budget (q := 7) (profile := d.f (p.r mid))
    hN hp.1 hK hmax hpower (by norm_num)
  let Cap : ENNReal := ((ENNReal.ofReal (d.N k ^ (-d.f (p.r mid) + (τ + ε))) *
    ENNReal.ofReal (64 * (max p.κ (d.K k)) ^ 2)) *
    ENNReal.ofReal (p.κ * d.N k ^ d.f (p.r mid))) * ENNReal.ofReal (36 * p.κ ^ 2)
  have hcap' : (V.entryLaw b a).map (fun z => WithLp.toLp 2
      (fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b z j.castSucc)) ≤
      Cap • volume := by
    simpa only [ValueBranchData.entryLaw, hb, add_assoc, Cap] using hcap
  apply hcap'.trans
  apply Measure.le_iff.mpr
  intro U _
  simpa only [Cap, Measure.smul_apply, smul_eq_mul] using
    (mul_le_mul' hbudget (le_refl (volume U)))

/-- Every later raw core restriction inherits the same cap in its own
local coordinates. No later core mass appears in the bound. -/
theorem ValueBranchData.entryLaw_core_cap
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (a : Fin V.count)
    (U : Set Event) (c : EuclideanSpace ℝ (Fin 3)) :
    ((V.entryLaw b a).restrict U).map (packetLocalCorePoint (d.N k) (d.B k) p b K R c) ≤
      ENNReal.ofReal (K ^ 7) • volume := by
  let base := fun z => WithLp.toLp 2
    (fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b z j.castSucc)
  have hbase : Measurable base := by
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_iff.mpr
    intro j
    exact (PiLp.continuous_apply 2 _ j.castSucc).measurable.comp
      (measurable_packetNativeCubePoint (d.N k) (d.B k) p b)
  have hcap : (((V.entryLaw b a).restrict U).map base) ≤ ENNReal.ofReal (K ^ 7) • volume :=
    (Measure.map_mono Measure.restrict_le_self hbase).trans
      (V.entryLaw_native_cap Q hpure hd hp hHE hHbase hK hmax hpower b hb hr hrL a)
  have hh := core_coordinates_cap ((V.entryLaw b a).restrict U) base hbase
    (by linarith : 1 ≤ K) R c _ hcap
  have heq : packetLocalCorePoint (d.N k) (d.B k) p b K R c =
      fun z => (K ^ R) • (base z - c) := by
    funext z
    unfold packetLocalCorePoint
    congr 1
    ext j
    fin_cases j <;> rfl
  rw [heq]
  exact hh

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
