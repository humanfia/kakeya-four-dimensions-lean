/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarDyadicBridgeMesh.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarDyadicBridgeMesh.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicBridgeSystem
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicPowerRanges

/-! A finite system of designated meshes and its common final dyadic mesh. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

noncomputable def scalarBridgeMesh {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (q : Fin (Fintype.card (ScalarBridgeLabels m steps))) : ℝ :=
  scalarDyadicLength (scalarBridgeHeight top start q)

theorem scalarBridgeMesh_top {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ) :
    scalarBridgeMesh top start (scalarBridgeTopIndex m steps) = scalarDyadicLength top := by
  rw [scalarBridgeMesh, scalarBridgeHeight_top]

theorem scalarBridgeMesh_start {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (hstart : ∀ i, start i ≤ top) (i : Fin m) :
    scalarBridgeMesh top start (scalarBridgeStartIndex steps i) = scalarDyadicLength (start i) := by
  rw [scalarBridgeMesh, scalarBridgeHeight_start top start hstart]

theorem scalarBridgeMesh_chain_antitone {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (hreach : ∀ i, scalarDyadicBridge top (start i) steps = top) (i : Fin m) :
    Antitone (fun j : Fin (steps + 2) =>
      scalarBridgeMesh top start (scalarBridgeChainIndex steps i j)) := by
  exact scalarDyadicLength_antitone.comp_monotone
    (scalarBridgeHeight_chain_monotone top start hreach i)

theorem scalarBridgeMesh_chain_step {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (hreach : ∀ i, scalarDyadicBridge top (start i) steps = top) (i : Fin m) (j : Fin (steps + 1)) :
    (scalarBridgeMesh top start (scalarBridgeChainIndex steps i j.castSucc)) ^ (33 / 32 : ℝ) / 2 ≤
      scalarBridgeMesh top start (scalarBridgeChainIndex steps i j.succ) := by
  exact scalarDyadicLength_lower_of_height_growth
    (scalarBridgeHeight_chain_step top start hreach i j)

/-- All inserted meshes remain in the same compact power range as
the original designated meshes and the common final mesh. -/
theorem scalarBridgeMesh_bounds {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (hstart : ∀ i, start i ≤ top) {lo hi : ℝ}
    (htop : lo ≤ scalarDyadicLength top ∧ scalarDyadicLength top ≤ hi)
    (hupper : ∀ i, scalarDyadicLength (start i) ≤ hi)
    (q : Fin (Fintype.card (ScalarBridgeLabels m steps))) :
    lo ≤ scalarBridgeMesh top start q ∧ scalarBridgeMesh top start q ≤ hi := by
  have hlower : lo ≤ scalarBridgeMesh top start q := by
    apply htop.1.trans
    exact scalarDyadicLength_antitone (scalarBridgeHeight_bounds start (Nat.zero_le top)
      (fun i => ⟨Nat.zero_le _, hstart i⟩) q).2
  refine ⟨hlower, ?_⟩
  unfold scalarBridgeMesh scalarBridgeHeight
  generalize hq : (Fintype.equivFin (ScalarBridgeLabels m steps)).symm q = x
  cases x with
  | none => exact htop.2
  | some ij =>
      obtain ⟨i, j⟩ := ij
      have hheight := scalarDyadicBridge_monotone top (start i) (Nat.zero_le j.val)
      rw [scalarDyadicBridge_zero (hstart i)] at hheight
      exact (scalarDyadicLength_antitone hheight).trans (hupper i)

/-- One number of bridge levels works uniformly for every original
world and every dyadic choice in the prescribed power range. -/
theorem exists_uniform_scalar_dyadic_bridge_length {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ steps : ℕ, ∀ (N : ℝ) (m top : ℕ) (start : Fin m → ℕ), 1 ≤ N →
      N ^ (-(2 * b)) ≤ scalarDyadicLength top →
      (∀ i, scalarDyadicLength (start i) ≤ N ^ (-(a / 2))) →
      ∀ i, scalarDyadicBridge top (start i) steps = top := by
  obtain ⟨steps, hsteps⟩ := exists_scalar_dyadic_bridge_length (4 * b / a)
  refine ⟨steps, ?_⟩
  intro N m top start hN htop hstart i
  exact hsteps top (start i)
    (scalar_dyadic_height_ratio_of_power_range hN ha hab htop (hstart i))

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
