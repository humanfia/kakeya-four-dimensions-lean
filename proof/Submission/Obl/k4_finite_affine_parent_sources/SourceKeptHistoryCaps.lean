import Submission.Obl.k4_finite_affine_parent_sources.SourceKeptEH2Proof
import Submission.Obl.k4_finite_affine_parent_sources.SourceGmVelCapsProof
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionPowerBudget

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_finite_forest_width_selection
open Submission.Obl.k4_stable_native_signal_oscillation

noncomputable section

local instance optMeasKHC (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingKHC (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ d₁ S : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- Original end-history weights, always taken before either later deletion. -/
def endHistoryWeight (D : SourceData p) (e : ℕ) (S0w : Set Incidence)
    (ν : Fin W → Measure Trajectory) (m : ℕ) (h : Option (Fin p.C)) : ENNReal :=
  ((ν D.w₀).prod volume) (S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent} ∩
    {x | p.history m e (D.w₀, x) = h})

/-- A single common end-state restriction supplies every old-label velocity cap
and both Boolean mesh caps, on the unchanged original reference and palette. -/
theorem kept_history_caps
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hEm : ∀ w, MeasurableSet (E w)) (hNk : 1 < Nk) (hL : 0 < L)
    (hd₁ : 0 ≤ d₁) (hd₁1 : d₁ ≤ 1)
    (D : SourceData p) (n : ℕ) (unit T N₀ A : ℝ) (hn : 1 ≤ n) (hu : 0 < unit)
    (hnT : (n : ℝ) < T) (hup : RawUpgrade n T N₀)
    (hA : 10000 ≤ A) (hκA : 7 * p.κ ≤ A)
    (hKnative : A ^ (10 * (groupsC + 2)) ≤ Nk ^ (unit * L))
    (hN₀ : N₀ ≤ Nk ^ (unit * L))
    (hBw : 0 < B D.w₀) (hD0 : D.D₀ = MajorFrame.frame (p.frame D.parent))
    (hDK : D.K = A ^ (100 * (groupsC + 2))) (hDm : MeasurableSet D.S)
    (hπ : IsProbabilityMeasure D.π)
    (hpal : ∀ v : ℝ, (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ a : ℤ,
      D.π {w : ℝ | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = a} ≤
        ENNReal.ofReal (A ^ 6 * (Nk ^ (unit * L)) ^ (-S * v)))
    (e : ℕ) (he : e < m)
    (hdepth : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → D.depth s ≤ e)
    (hge : ∀ s, D.i₀ ≤ D.depth s)
    (S0w S1 S2 : Set Incidence) (δv Cw blur : ℝ)
    (hS0m : MeasurableSet S0w) (hS0E : S0w ⊆ E D.w₀)
    (hS1 : S1 ⊆ S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent})
    (hS2m : MeasurableSet S2) (hS21 : S2 ⊆ S1) (hS2c : S2 ⊆ p.counted D.parent)
    (hCw0 : 0 ≤ Cw) (hCwA : Cw ≤ A)
    (hwin : ∀ (h : Option (Fin p.C)) (z : Fin 2 → ℤ),
      ((ν D.w₀).prod volume).real (S1 ∩
        {x | p.history m e (D.w₀, x) = h ∧ worldBin δv (D.w₀, x) = z}) ≤
      Cw * ((ν D.w₀).prod volume).real (S0w ∩
          {x | p.history m D.i₀ (D.w₀, x) = some D.parent} ∩
          {x | p.history m e (D.w₀, x) = h}) *
        (((ν D.w₀).prod volume).real (S0w ∩
            {x | p.history m D.i₀ (D.w₀, x) = some D.parent} ∩
            {x | worldBin δv (D.w₀, x) = z}) /
          ((ν D.w₀).prod volume).real (S0w ∩
            {x | p.history m D.i₀ (D.w₀, x) = some D.parent})))
    (hR0 : ((ν D.w₀).prod volume) (S0w ∩
      {x | p.history m D.i₀ (D.w₀, x) = some D.parent}) ≠ 0)
    (hdom : ∀ (ρ : Measure Incidence), ρ ≤ nuE (((ν D.w₀).prod volume).restrict (E D.w₀))
        (S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent}) →
      ∀ (P : Set Incidence) (C : ENNReal) (width : ℝ), 2 * blur ≤ width →
      (∀ z : Fin 2 → ℤ, ρ (P ∩ {x | worldBin δv (D.w₀, x) = z}) ≤
        C * nuE (((ν D.w₀).prod volume).restrict (E D.w₀))
          (S0w ∩ {x | p.history m D.i₀ (D.w₀, x) = some D.parent})
          {x | worldBin δv (D.w₀, x) = z}) →
      ∀ e' : ℤ, ρ (P ∩ {x | ⌊(labelFrame p D.parent (B D.w₀)
          (δ Nk (p.r D.i₀))).eb x.1 3 / width⌋ = e'}) ≤
        4 * C * D.π {w | ⌊w / width⌋ = e'})
    (hblur : 2 * blur ≤ (Nk ^ (unit * L)) ^ (-(n : ℝ)))
    {G' : ℕ} (g : ℝ → Observation → ENNReal) (r : Fin G' → ℝ)
    (hg : ∀ j, Measurable (g (r j)))
    (hlaw : ∀ j, (((ν D.w₀).prod volume).restrict (E D.w₀)).map
      (obs (B D.w₀) (δ Nk (r j))) = (volume.prod Measure.count).withDensity (g (r j)))
    (τd hd : ℝ) (hhd : 0 ≤ hd)
    (hmask : S2 ⊆ E D.w₀ ∩ densMask g (B D.w₀) Nk τd f r)
    (hcover : ∀ s : ℝ, 0 ≤ s → s ≤ T → ∃ j, p.r D.i₀ + unit * L * s ≤ r j ∧
      r j ≤ p.r D.i₀ + unit * L * s + hd ∧
      f (p.r D.i₀) + d₁ * (r j - p.r D.i₀) - 2 * (δ₀ * L) ≤ f (r j))
    (hpure : pureConst p.κ Nk hd τd δ₀ L ≤ A ^ 4)
    (mesh : ℝ) (hmesh : 0 < mesh) (hmeshT : mesh ≤ (Nk ^ (unit * L)) ^ (-T))
    (hDS : D.S ⊆ S2 ∩ keptSet (((ν D.w₀).prod volume).restrict S2)
      (fun x => p.history m e (D.w₀, x))
      (stateCode (frameBase (D.frame Nk B)) (frameSignal (D.frame Nk B)
        (D.stage Nk L unit ν B).P) mesh) (endHistoryWeight D e S0w ν m)
      (ENNReal.ofReal ((A ^ (6 * groupsC + 2))⁻¹)))
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hterm : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀)
    (hSend : ∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
      z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) :
    D.VelCaps n unit Nk L ν B ∧ EH2 d₁ S (D.stage Nk L unit ν B) n := by
  classical
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hK0one : 1 ≤ A ^ (10 * (groupsC + 2)) := one_le_pow₀ hA1
  have hN : 1 ≤ Nk ^ (unit * L) := hK0one.trans hKnative
  have hDS2 : D.S ⊆ S2 := fun x hx => (hDS hx).1
  have h4C : 4 * Cw ≤ D.K := by
    rw [hDK]
    calc 4 * Cw ≤ A ^ 2 := by nlinarith [hCwA]
      _ ≤ _ := pow_le_pow_right₀ hA1 (by omega)
  refine ⟨gmVelCaps hp hν hE hEm hNk D n unit e δv Cw S0w S1 S2 hD0 hN he hdepth hge
    hS0m hS0E hS1 hCw0 h4C hwin hR0 hdom hblur hS2m hS21 hDS2 hSo hterm hSend, ?_⟩
  have hframe : D.frame Nk B = labelFrame p D.parent (B D.w₀) (δ Nk (p.r D.i₀)) := by
    unfold SourceData.frame
    rw [hD0]
    rfl
  have hnum : ∀ v : ℝ, (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ (v₀ : ℤ) (h : Option (Fin p.C)),
      ((ν D.w₀).prod volume) (S2 ∩ ({x | p.history m e (D.w₀, x) = h} ∩
        {x | ⌊(D.frame Nk B).eb x.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀})) ≤
      (4 * ENNReal.ofReal Cw) * endHistoryWeight D e S0w ν m h *
        D.π {w | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} := by
    intro v hv hvn v₀ h
    have hw : 2 * blur ≤ (Nk ^ (unit * L)) ^ (-v) :=
      hblur.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
    rw [hframe]
    exact end_bin_numerator hp hν hE hEm D.w₀ D.i₀ e D.parent δv S0w hS0m hS0E S1 hS1
      Cw hCw0 hwin hR0 D.π _ hdom S2 hS2m hS21 hw h v₀
  have hκ0 : 0 ≤ p.κ := zero_le_one.trans hp.one_le_slack
  have hCp0 : 0 ≤ pureConst p.κ Nk hd τd δ₀ L := by unfold pureConst; positivity
  have hcost := ENNReal.ofReal_le_ofReal (kept_joint_power_budget hA groupsC hCwA hCp0 hpure)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num)] at hcost
  norm_num only [ENNReal.ofReal_ofNat] at hcost
  refine keptEH2 hp hν hE hNk hL hd₁ hd₁1 D n unit T N₀ hn hu hnT hup hBw hD0 hDm hπ
    ?_ S2 hS2m hS2c g r hg hlaw τd hd hhd hmask hcover
    (fun x => p.history m e (D.w₀, x)) ?_ (endHistoryWeight D e S0w ν m)
    (ENNReal.ofReal ((A ^ (6 * groupsC + 2))⁻¹)) ?_ ENNReal.ofReal_ne_top
    mesh hmesh hmeshT hDS (4 * ENNReal.ofReal Cw) hnum
    (A ^ (10 * (groupsC + 2))) hK0one ?_ hKnative hN₀ ?_ hcost ?_
  · intro v hv hvn a
    exact (hpal v hv hvn a).trans (ENNReal.ofReal_le_ofReal (by
      rw [hDK]
      gcongr
      omega))
  · exact (hp.measurable_history _).comp measurable_prodMk_left
  · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · exact hκA.trans (le_self_pow₀ hA1 (by omega))
  · exact hpure.trans (pow_le_pow_right₀ hA1 (by omega))
  · rw [hDK]
    exact kept_raw_power_budget hA groupsC

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
