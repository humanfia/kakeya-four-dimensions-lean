-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.PacketPhysical, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/PacketPhysical.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/PacketPhysical.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/PacketPhysical.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketBoxes
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.PacketQuadratics
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.NativeCurveCells

/-! # The physical graph point and the exact original packet law -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

def packetTime {W : ℕ} (p : Native.PathData W) (a : Fin p.C) (q : Event) : ℝ :=
  (q.2 - (nativeOldBaseFrame p a).t₀) / (nativeOldBaseFrame p a).q

def packetSignal {W : ℕ} (Nk : ℝ) (p : Native.PathData W) (a : Fin p.C) (q : Event) : ℝ :=
  (δ Nk (p.r (p.lev a)))⁻¹ * MvPolynomial.eval (xp q.1 q.2) (p.R a)

def packetPhysicalPoint {W : ℕ} (Nk : ℝ) (p : Native.PathData W) (a : Fin p.C)
    (q : Event) : EuclideanSpace ℝ (Fin 4) :=
  SourceGeometry.liftedVector (fun j => packetBase p a q j) (packetSignal Nk p a q)

theorem measurable_packetSignal {W : ℕ} (Nk : ℝ) (p : Native.PathData W)
    (a : Fin p.C) : Measurable (packetSignal Nk p a) := by
  have hx : Measurable (fun q : Event => xp q.1 q.2) := by
    unfold xp
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j <;> simp <;> fun_prop
  exact ((MvPolynomial.continuous_eval (p.R a)).measurable.comp hx).const_mul _

theorem measurable_packetPhysicalPoint {W : ℕ} (Nk : ℝ) (p : Native.PathData W)
    (a : Fin p.C) : Measurable (packetPhysicalPoint Nk p a) := by
  unfold packetPhysicalPoint SourceGeometry.liftedVector
  apply (PiLp.volume_preserving_toLp (Fin 4)).measurable.comp
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j
  · change Measurable (fun q : Event => packetBase p a q 0)
    exact (PiLp.continuous_apply 2 _ 0).measurable.comp (measurable_packetBase p a)
  · change Measurable (fun q : Event => packetBase p a q 1)
    exact (PiLp.continuous_apply 2 _ 1).measurable.comp (measurable_packetBase p a)
  · change Measurable (fun q : Event => packetBase p a q 2)
    exact (PiLp.continuous_apply 2 _ 2).measurable.comp (measurable_packetBase p a)
  · exact measurable_packetSignal Nk p a

/-- The physical base is exactly the base of the same normalized line at
the same normalized time. This imports the accepted observation identity. -/
theorem packetBase_eq_normalizedPoint {W : ℕ} (p : Native.PathData W) (a : Fin p.C)
    (q : Event) :
    packetBase p a q = WithLp.toLp 2
      (fun j : Fin 3 => xp (normalizedPacketLine p a q.1) (packetTime p a q) j.castSucc) := by
  let F := nativeOldBaseFrame p a
  have hq : F.q ≠ 0 := by dsimp [F, nativeOldBaseFrame]; positivity
  have hobs := congrArg Prod.fst (F.obs_normInc hq 1 1 1 one_ne_zero q)
  simp only [one_mul, div_one] at hobs
  calc
    _ = (Submission.Lib.K4ChartLifting.obs 1 1 (F.normInc q)).1 := hobs.symm
    _ = _ := by ext j; fin_cases j <;> rfl

section Path

variable {W : ℕ} {p : Native.PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Line} {E : Fin W → Set Event} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

theorem packetSignal_eq_normalizedCurve (a : Fin p.C) (q : Event) :
    packetSignal Nk p a q = normalizedPacketCurve Nk p a q.1 (packetTime p a q) := by
  let F := nativeOldBaseFrame p a
  have hq : F.q ≠ 0 := by dsimp [F, nativeOldBaseFrame]; positivity
  have hD : IsUnit F.D.det := isUnit_iff_ne_zero.mpr (hp.2.2.2.2.2.2.2 a).2.2.1
  have ht : F.t₀ + F.q * ((q.2 - F.t₀) / F.q) = q.2 := by field_simp; ring
  have hh := F.eval_normTest hq (δ Nk (p.r (p.lev a))) (p.R a) (F.normTraj q.1)
    ((q.2 - F.t₀) / F.q)
  rw [F.denormTraj_normTraj hq hD, ht] at hh
  exact hh.symm

/-- The physical point used in the count is the actual native quadratic
curve used by the Kakeya moment theorem. -/
theorem packetPhysicalPoint_eq_nativeCurve (a : Fin p.C) (q : Event) :
    packetPhysicalPoint Nk p a q = SourceGeometry.nativePhysicalCurve
      (normalizedPacketTest Nk p a) (normalizedPacketPosition p a q.1)
      (normalizedPacketVelocity p a q.1) (packetTime p a q) := by
  unfold packetPhysicalPoint SourceGeometry.nativePhysicalCurve
  rw [packetSignal_eq_normalizedCurve hp, packetBase_eq_normalizedPoint]
  congr 1
  · funext j
    exact congrFun (normalizedPacketMotion p a q.1 (packetTime p a q)) j.castSucc
  · exact congrArg (fun z => MvPolynomial.eval z (normalizedPacketTest Nk p a))
      (normalizedPacketMotion p a q.1 (packetTime p a q))

/-- Specialize the accepted normalization identity to any actual later
event inside the old packet. The denominator remains the FULL original
old assignment times its original time length. -/
theorem packet_normalized_original_law [∀ w, IsFiniteMeasure (ν w)]
    (a : Fin p.C) (S : Set Event) (hS : MeasurableSet S) (hSF : S ⊆ p.F a) :
    (((ν (p.γ a) (p.A a))⁻¹ •
        ((ν (p.γ a)).restrict (p.A a)).map (nativeOldBaseFrame p a).normTraj).prod volume).restrict
        ((nativeOldBaseFrame p a).normEvent (p.A a) S) =
      (ν (p.γ a) (p.A a) * ENNReal.ofReal (nativeOldBaseFrame p a).q)⁻¹ •
        (((ν (p.γ a)).prod volume).restrict S).map (nativeOldBaseFrame p a).normInc := by
  let F := nativeOldBaseFrame p a
  have hq : 0 < F.q := by dsimp [F, nativeOldBaseFrame]; positivity
  rcases hp.2.2.2.2.2.2.2 a with
    ⟨_, _, hdet, _, _, _, _, _, hA, _, _, _, hsel, _⟩
  apply F.normalized_selected_law hq (isUnit_iff_ne_zero.mpr hdet) (ν (p.γ a)) hA hS
  intro q hqS
  have hF := hsel q (hSF hqS)
  refine ⟨hF.2.1, hF.2.2.1.1, ?_⟩
  have hright : F.t₀ + F.q =
      ((p.j a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a) := by dsimp [F, nativeOldBaseFrame]; ring
  rw [hright]
  exact hF.2.2.1.2

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
