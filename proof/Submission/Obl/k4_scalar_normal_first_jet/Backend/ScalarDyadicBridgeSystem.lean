/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarDyadicBridgeSystem.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarDyadicBridgeSystem.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicBridge
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option

/-! Finitely many designated dyadic rows share one common final row. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

abbrev ScalarBridgeLabels (m steps : ℕ) := Option (Fin m × Fin (steps + 1))

noncomputable def scalarBridgeTopIndex (m steps : ℕ) : Fin (Fintype.card (ScalarBridgeLabels m steps)) :=
  Fintype.equivFin (ScalarBridgeLabels m steps) none

noncomputable def scalarBridgeStartIndex {m : ℕ} (steps : ℕ) (i : Fin m) :
    Fin (Fintype.card (ScalarBridgeLabels m steps)) :=
  Fintype.equivFin (ScalarBridgeLabels m steps) (some (i, 0))

noncomputable def scalarBridgeHeight {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (q : Fin (Fintype.card (ScalarBridgeLabels m steps))) : ℕ :=
  match (Fintype.equivFin (ScalarBridgeLabels m steps)).symm q with
  | none => top
  | some (i, j) => scalarDyadicBridge top (start i) j.val

noncomputable def scalarBridgeChainIndex {m : ℕ} (steps : ℕ) (i : Fin m)
    (j : Fin (steps + 2)) : Fin (Fintype.card (ScalarBridgeLabels m steps)) :=
  if hj : j.val < steps + 1 then
    Fintype.equivFin (ScalarBridgeLabels m steps) (some (i, ⟨j.val, hj⟩))
  else scalarBridgeTopIndex m steps

theorem scalarBridgeHeight_top {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ) :
    scalarBridgeHeight top start (scalarBridgeTopIndex m steps) = top := by
  simp only [scalarBridgeHeight, scalarBridgeTopIndex, Equiv.symm_apply_apply]

theorem scalarBridgeHeight_pair {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (i : Fin m) (j : Fin (steps + 1)) :
    scalarBridgeHeight top start (Fintype.equivFin (ScalarBridgeLabels m steps) (some (i, j))) =
      scalarDyadicBridge top (start i) j.val := by
  simp only [scalarBridgeHeight, Equiv.symm_apply_apply]

theorem scalarBridgeChainIndex_zero {m : ℕ} (steps : ℕ) (i : Fin m) :
    scalarBridgeChainIndex steps i 0 = scalarBridgeStartIndex steps i := by
  simp [scalarBridgeChainIndex, scalarBridgeStartIndex]

theorem scalarBridgeChainIndex_last {m : ℕ} (steps : ℕ) (i : Fin m) :
    scalarBridgeChainIndex steps i (Fin.last (steps + 1)) = scalarBridgeTopIndex m steps := by
  simp [scalarBridgeChainIndex]

theorem scalarBridgeHeight_chain {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (hreach : ∀ i, scalarDyadicBridge top (start i) steps = top) (i : Fin m) (j : Fin (steps + 2)) :
    scalarBridgeHeight top start (scalarBridgeChainIndex steps i j) =
      scalarDyadicBridge top (start i) j.val := by
  dsimp only [scalarBridgeChainIndex]
  split_ifs with hj
  · exact scalarBridgeHeight_pair top start i ⟨j.val, hj⟩
  · rw [scalarBridgeHeight_top]
    have hval : j.val = steps + 1 := by omega
    have hh := scalarDyadicBridge_monotone top (start i) (show steps ≤ j.val by omega)
    rw [hreach i] at hh
    exact (le_antisymm (scalarDyadicBridge_le_top top (start i) j.val) hh).symm

theorem scalarBridgeHeight_start {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (hstart : ∀ i, start i ≤ top) (i : Fin m) :
    scalarBridgeHeight top start (scalarBridgeStartIndex steps i) = start i := by
  change scalarBridgeHeight top start
    (Fintype.equivFin (ScalarBridgeLabels m steps) (some (i, 0))) = _
  rw [scalarBridgeHeight_pair]
  exact scalarDyadicBridge_zero (hstart i)

theorem scalarBridgeHeight_bounds {m steps lo top : ℕ} (start : Fin m → ℕ)
    (hlo : lo ≤ top) (hstart : ∀ i, lo ≤ start i ∧ start i ≤ top)
    (q : Fin (Fintype.card (ScalarBridgeLabels m steps))) :
    lo ≤ scalarBridgeHeight top start q ∧ scalarBridgeHeight top start q ≤ top := by
  unfold scalarBridgeHeight
  generalize hq : (Fintype.equivFin (ScalarBridgeLabels m steps)).symm q = x
  cases x with
  | none => exact ⟨hlo, le_rfl⟩
  | some ij =>
      obtain ⟨i, j⟩ := ij
      have hh := scalarDyadicBridge_monotone top (start i) (Nat.zero_le j.val)
      rw [scalarDyadicBridge_zero (hstart i).2] at hh
      exact ⟨(hstart i).1.trans hh, scalarDyadicBridge_le_top top (start i) j.val⟩

theorem scalarBridgeHeight_chain_monotone {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (hreach : ∀ i, scalarDyadicBridge top (start i) steps = top) (i : Fin m) :
    Monotone (fun j => scalarBridgeHeight top start (scalarBridgeChainIndex steps i j)) := by
  intro a b hab
  change scalarBridgeHeight top start (scalarBridgeChainIndex steps i a) ≤
    scalarBridgeHeight top start (scalarBridgeChainIndex steps i b)
  rw [scalarBridgeHeight_chain top start hreach, scalarBridgeHeight_chain top start hreach]
  exact scalarDyadicBridge_monotone top (start i) hab

theorem scalarBridgeHeight_chain_step {m steps : ℕ} (top : ℕ) (start : Fin m → ℕ)
    (hreach : ∀ i, scalarDyadicBridge top (start i) steps = top) (i : Fin m) (j : Fin (steps + 1)) :
    (scalarBridgeHeight top start (scalarBridgeChainIndex steps i j.succ) : ℝ) ≤
      (33 / 32 : ℝ) * scalarBridgeHeight top start (scalarBridgeChainIndex steps i j.castSucc) + 1 := by
  rw [scalarBridgeHeight_chain top start hreach, scalarBridgeHeight_chain top start hreach]
  exact scalarDyadicBridge_step top (start i) j.val

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
