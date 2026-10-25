/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFirstJetBridge.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFirstJetBridge.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyCurrentTaylor
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarHierarchyReindex
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicTimeGrid
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarDyadicBridgeMesh

/-! Every designated affine row uses its own bridge to the same final row. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

namespace ScalarGridHierarchy

/-- One common original current-floor set supplies all analytic
inputs for every designated bridge, without sorting designated rows. -/
theorem bridge_slopes_and_taylor {Λ : Type*} [MeasurableSpace Λ]
    {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {m steps top : ℕ} {start : Fin m → ℕ}
    (hstart : ∀ i, start i ≤ top)
    (hreach : ∀ i, scalarDyadicBridge top (start i) steps = top)
    {B P : ℝ} (hB : 0 ≤ B) (hP : 0 < P)
    (G : ScalarGridHierarchy ν E F
      (fun q : Fin (Fintype.card (ScalarBridgeLabels m steps)) =>
        2 ^ scalarBridgeHeight top start q)
      (fun _ => by positivity)
      (fun q => (1 / ((2 ^ scalarBridgeHeight top start q : ℕ) : ℝ)) ^ (1 / 4 : ℝ)) B)
    {R : Set (Λ × ℝ)} (hR : R ⊆ E ∩ (univ ×ˢ G.times))
    (hfloor : ∀ q ∈ R, ∀ i : Fin (Fintype.card (ScalarBridgeLabels m steps)),
      ENNReal.ofReal (scalarBridgeMesh top start i / P) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ timeCell (2 ^ scalarBridgeHeight top start i)
          (scalarTimeBlockCode (2 ^ scalarBridgeHeight top start i) (by positivity) q.2)))) :
    ∀ i : Fin m,
      (∀ q ∈ R,
        |G.slope (scalarBridgeStartIndex steps i) q.2 -
          G.slope (scalarBridgeTopIndex m steps) q.2| ≤
          (32 * (steps + 1 : ℕ) * B * P) * scalarDyadicLength (start i) ^ (7 / 32 : ℝ)) ∧
      (∀ q ∈ R, ∀ q' ∈ R,
        scalarTimeBlockCode (2 ^ start i) (by positivity) q.2 =
          scalarTimeBlockCode (2 ^ start i) (by positivity) q'.2 →
        |F q'.2 - F q.2 - (q'.2 - q.2) * G.slope (scalarBridgeTopIndex m steps) q.2| ≤
          (4 * B + 32 * (steps + 1 : ℕ) * B * P) *
            scalarDyadicLength (start i) ^ (11 / 10 : ℝ)) := by
  intro i
  let idx := scalarBridgeChainIndex steps i
  let C := G.reindex idx
  have hmesheq (j : Fin (steps + 2)) :
      1 / ((2 ^ scalarBridgeHeight top start (idx j) : ℕ) : ℝ) =
        scalarBridgeMesh top start (idx j) :=
    (scalarDyadicLength_eq _).symm
  have hmesh : Antitone (fun j : Fin (steps + 2) =>
      1 / ((2 ^ scalarBridgeHeight top start (idx j) : ℕ) : ℝ)) := by
    simpa only [hmesheq] using scalarBridgeMesh_chain_antitone top start hreach i
  have hlower (j : Fin (steps + 1)) :
      (1 / ((2 ^ scalarBridgeHeight top start (idx j.castSucc) : ℕ) : ℝ)) ^
          (33 / 32 : ℝ) / 2 ≤
        1 / ((2 ^ scalarBridgeHeight top start (idx j.succ) : ℕ) : ℝ) := by
    simpa only [hmesheq] using scalarBridgeMesh_chain_step top start hreach i j
  have hreading (j : Fin (steps + 2)) :
      (1 / ((2 ^ scalarBridgeHeight top start (idx j) : ℕ) : ℝ)) ^ (1 / 4 : ℝ) ≤
        2 * (1 / ((2 ^ scalarBridgeHeight top start (idx j) : ℕ) : ℝ)) ^ (1 / 4 : ℝ) := by
    have h0 : 0 ≤ (1 / ((2 ^ scalarBridgeHeight top start (idx j) : ℕ) : ℝ)) ^ (1 / 4 : ℝ) := by
      positivity
    linarith
  have hnesting (a b : Fin (steps + 2)) (hab : a ≤ b)
      (t : ℝ) (ht : t ∈ C.times) (u : ℝ) (hu : u ∈ C.times) :
      scalarTimeBlockCode (2 ^ scalarBridgeHeight top start (idx b)) (by positivity) t =
        scalarTimeBlockCode (2 ^ scalarBridgeHeight top start (idx b)) (by positivity) u →
      scalarTimeBlockCode (2 ^ scalarBridgeHeight top start (idx a)) (by positivity) t =
        scalarTimeBlockCode (2 ^ scalarBridgeHeight top start (idx a)) (by positivity) u := by
    exact scalarTimeBlockCode_dyadic_nesting
      (scalarBridgeHeight_chain_monotone top start hreach i hab) (C.unit_time ht) (C.unit_time hu)
  have hfloorC : ∀ q ∈ R, ∀ j : Fin (steps + 2),
      ENNReal.ofReal ((1 / ((2 ^ scalarBridgeHeight top start (idx j) : ℕ) : ℝ)) / P) ≤
        (ν.prod volume) (R ∩
          (univ ×ˢ timeCell (2 ^ scalarBridgeHeight top start (idx j))
            (scalarTimeBlockCode (2 ^ scalarBridgeHeight top start (idx j)) (by positivity) q.2))) := by
    intro q hq j
    rw [hmesheq]
    exact hfloor q hq (idx j)
  have hzero : idx 0 = scalarBridgeStartIndex steps i := scalarBridgeChainIndex_zero steps i
  have hlast : idx (Fin.last (steps + 1)) = scalarBridgeTopIndex m steps :=
    scalarBridgeChainIndex_last steps i
  have hstartHeight : scalarBridgeHeight top start (idx 0) = start i := by
    rw [hzero, scalarBridgeHeight_start top start hstart]
  constructor
  · intro q hq
    have h := C.slopes_close_to_finest_on_current_floor_set hB hP hmesh hlower hreading
      hnesting hR hfloorC q hq 0
    simpa only [C, reindex, hzero, hlast, hstartHeight, scalarBridgeHeight_start top start hstart,
      scalarDyadicLength_eq] using h
  · intro q hq q' hq' hcode
    have hcodeC :
        scalarTimeBlockCode (2 ^ scalarBridgeHeight top start (idx 0)) (by positivity) q.2 =
          scalarTimeBlockCode (2 ^ scalarBridgeHeight top start (idx 0)) (by positivity) q'.2 := by
      -- `scalarTimeBlockCode (2 ^ k)` lives in `Fin (2 ^ k)`, so the height is
      -- generalized instead of rewritten under that dependent type.
      have key : ∀ k : ℕ, k = start i →
          scalarTimeBlockCode (2 ^ k) (by positivity) q.2 =
            scalarTimeBlockCode (2 ^ k) (by positivity) q'.2 := by
        rintro k rfl
        exact hcode
      exact key _ hstartHeight
    have h := C.taylor_on_current_floor_set hB hP hmesh hlower hreading hnesting hR hfloorC
      q hq q' hq' 0 hcodeC
    simpa only [C, reindex, hzero, hlast, hstartHeight, scalarBridgeHeight_start top start hstart,
      scalarDyadicLength_eq] using h

end ScalarGridHierarchy

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
