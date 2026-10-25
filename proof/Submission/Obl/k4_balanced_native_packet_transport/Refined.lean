import Submission.Obl.k4_balanced_native_packet_transport.Native
import Submission.Obl.k4_balanced_native_packet_transport.StageInterfaces
import Submission.Obl.k4_balanced_native_packet_transport.SelectedBlockLaws
import Submission.Obl.k4_balanced_native_packet_transport.MassBookkeeping
import Submission.Obl.k4_balanced_native_packet_transport.NativeWindows
import Submission.Obl.k4_balanced_native_packet_transport.ObservationTransport
import Submission.Obl.k4_balanced_native_packet_transport.CoefficientBounds
import Submission.Obl.k4_balanced_native_packet_transport.WeightedDomination

/-!
A refinement of the charts of one native full-time sample into dyadic time
subblocks and subcharts. Given its geometry, the uncapped intermediate sample
of the two-stage seam is assembled from restricted native laws.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport
namespace Refined

open MeasureTheory Filter Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option linter.unusedVariables false

/-- Subcharts in dyadic time blocks, each inside one chart of a native sample. -/
structure Family (W C₀ : ℕ) where
  T : ℕ
  C : ℕ
  parent : Fin C → Fin C₀
  j : Fin C → Fin (2 ^ T)
  c : Fin C → EuclideanSpace ℝ (Fin 2)
  u : Fin C → EuclideanSpace ℝ (Fin 2)
  Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ
  A : Fin C → Set Traj
  F : Fin C → Set Inc
  lst : Fin W → Obs → Finset (Fin C)

variable {W C₀ : ℕ}

def Family.q (ρ : Family W C₀) : ℝ := 1 / (2 : ℝ) ^ ρ.T

def Family.t₀ (ρ : Family W C₀) (i : Fin ρ.C) : ℝ := ((ρ.j i : ℕ) : ℝ) / (2 : ℝ) ^ ρ.T

/-- The half-open selected incidences of a subchart. -/
def Family.H (ρ : Family W C₀) (i : Fin ρ.C) : Set Inc :=
  ρ.F i ∩ (univ ×ˢ Ico (ρ.t₀ i) (ρ.t₀ i + ρ.q))

/-- The spatial tangent of the parent native chart. -/
def tangentAxis (σ : NativeSample W) (a : Fin σ.C) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![σ.tangent a 1, σ.tangent a 2]

/-- All geometric properties of a refinement relative to its native sample. -/
structure Family.Valid (σ : NativeSample W) (ρ : Family W σ.C) (N : ℝ)
    (ν : Fin W → Measure Traj) (E : Fin W → Set Inc)
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (M D : ℕ) (loss h f₀ ξ : ℝ) : Prop where
  A_sub : ∀ i, ρ.A i ⊆ σ.A (ρ.parent i)
  F_sub : ∀ i, ρ.F i ⊆ σ.F (ρ.parent i)
  charts : ∀ i, chart N M D (N ^ loss) ρ.T ((ρ.j i : ℕ) : ℝ) 0
    (B (σ.γ (ρ.parent i))) (E (σ.γ (ρ.parent i)))
    (ρ.c i) (ρ.u i) (ρ.Q i) (P (σ.γ (ρ.parent i))) (ρ.A i) (ρ.F i)
    (∀ p ∈ ρ.F i, i ∈ ρ.lst (σ.γ (ρ.parent i))
      (obs (B (σ.γ (ρ.parent i))) (δ N 1) p))
  sep : ∀ i i', i ≠ i' → σ.γ (ρ.parent i) = σ.γ (ρ.parent i') →
    ρ.j i = ρ.j i' → Disjoint (ρ.A i) (ρ.A i')
  lst_card : ∀ w o, ((ρ.lst w o).card : ℝ) ≤ N ^ loss
  lst_meas : ∀ w i, MeasurableSet {o | i ∈ ρ.lst w o}
  count : (ρ.C : ℝ) ≤ N ^ M
  time : (2 : ℝ) ^ ρ.T ≤ N ^ (h + loss)
  prior_lower : ∀ i, ENNReal.ofReal (N ^ (-f₀ - ξ) * |Matrix.det (ρ.Q i)|) ≤
    ν (σ.γ (ρ.parent i)) (ρ.A i)
  full : ∀ i, ρ.q / N ^ loss ≤
    ‖Matrix.toEuclideanLin (ρ.Q i).transpose (tangentAxis σ (ρ.parent i))‖


end
end Refined
end Submission.Obl.k4_balanced_native_packet_transport
