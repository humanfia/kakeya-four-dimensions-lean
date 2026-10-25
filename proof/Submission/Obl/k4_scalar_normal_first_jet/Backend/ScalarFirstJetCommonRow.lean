/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFirstJetCommonRow.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFirstJetCommonRow.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetBridge
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetNumerics
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridFirstJetCovers

/-! Original first-jet covers and Taylor estimates use one common final row. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

namespace ScalarGridHierarchy

theorem exists_common_row_first_jet_restriction {Λ : Type*} [MeasurableSpace Λ]
    {D : ScalarMotion Λ} {ν : Measure Λ} [IsProbabilityMeasure ν]
    {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {S : ℝ → Set ℝ}
    {m steps top : ℕ} {start : Fin m → ℕ}
    (hstart : ∀ i, start i ≤ top)
    (hreach : ∀ i, scalarDyadicBridge top (start i) steps = top)
    {B P K ζ d duration : ℝ} (hB : 0 ≤ B)
    (G : ScalarGridHierarchy ν E F
      (fun q : Fin (Fintype.card (ScalarBridgeLabels m steps)) =>
        2 ^ scalarBridgeHeight top start q)
      (fun _ => by positivity)
      (fun q => (1 / ((2 ^ scalarBridgeHeight top start q : ℕ) : ℝ)) ^ (1 / 4 : ℝ)) B)
    (read : Fin m)
    (h : ScalarNormalHyp D ν E F S K ζ d) (hK : 1 ≤ K)
    (hζ : 0 < ζ) (hd0 : 0 ≤ d) (hd : d < 1)
    (hP : 1 ≤ P) (hKP : K ≤ P) (hBP : B ≤ P) (hduration : 0 ≤ duration)
    {R : Set (Λ × ℝ)} (hRm : MeasurableSet R) (hR : R ⊆ E ∩ (univ ×ˢ G.times))
    (hfloor : ∀ q ∈ R, ∀ i : Fin (Fintype.card (ScalarBridgeLabels m steps)),
      ENNReal.ofReal (scalarBridgeMesh top start i / P) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ timeCell (2 ^ scalarBridgeHeight top start i)
          (scalarTimeBlockCode (2 ^ scalarBridgeHeight top start i) (by positivity) q.2))))
    (hζH : ζ ≤ scalarDyadicLength (start read) ^ 2)
    (hconcentration : OriginalScalarResidualAt (d := d) (j := 1) Λ ℤ (scalarBlockFitBound P)
      (scalarDyadicLength (start read) ^ (1 / 8 : ℝ)) duration) :
    ∃ R' : Set (Λ × ℝ), MeasurableSet R' ∧ R' ⊆ R ∧
      (duration / (20000 * P ^ 6)) * (ν.prod volume).real R ≤ (ν.prod volume).real R' ∧
      (∀ i : Fin m, ∀ q ∈ R', ∀ q' ∈ R',
        scalarTimeBlockCode (2 ^ start i) (by positivity) q.2 =
          scalarTimeBlockCode (2 ^ start i) (by positivity) q'.2 →
        |F q'.2 - F q.2 - (q'.2 - q.2) * G.slope (scalarBridgeTopIndex m steps) q.2| ≤
          (4 * B + 32 * (steps + 1 : ℕ) * B * P) *
            scalarDyadicLength (start i) ^ (11 / 10 : ℝ)) ∧
      ∃ L : ℝ → ℤ → Finset ℝ,
        (∀ t z, ((L t z).card : ℝ) ≤ 1000 * scalarBlockFitBound P ^ 2) ∧
        ∀ q ∈ R', ∃ v ∈ L q.2 ⌊D.scalar F q.1 q.2 / scalarDyadicLength (start read)⌋,
          |scalarFirstJet D F (G.slope (scalarBridgeTopIndex m steps)) q.1 q.2 - v| ≤
            (1 + 64 * (steps + 1 : ℕ) * B * P * K) *
              scalarDyadicLength (start read) ^ ((1 - d) / 32) := by
  let idx := scalarBridgeStartIndex steps read
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hreadHeight : scalarBridgeHeight top start idx = start read :=
    scalarBridgeHeight_start top start hstart read
  have hreadMesh : 1 / ((2 ^ scalarBridgeHeight top start idx : ℕ) : ℝ) =
      scalarDyadicLength (start read) := by
    rw [← scalarDyadicLength_eq, hreadHeight]
  have hfloorRead : ∀ q ∈ R,
      ENNReal.ofReal ((1 / ((2 ^ scalarBridgeHeight top start idx : ℕ) : ℝ)) / P) ≤
        (ν.prod volume) (R ∩ (univ ×ˢ timeCell (2 ^ scalarBridgeHeight top start idx)
          (scalarTimeBlockCode (2 ^ scalarBridgeHeight top start idx) (by positivity) q.2))) := by
    intro q hq
    simpa only [scalarBridgeMesh, scalarDyadicLength_eq] using hfloor q hq idx
  obtain ⟨R', hR'm, hR'R, hmass, hcover⟩ :=
    G.exists_original_first_jet_cover_restriction idx h hζ hd0 hd hP hKP hBP hduration
      hRm hR (by simpa only [hreadMesh] using hζH) hfloorRead
      (by simpa only [hreadMesh] using hconcentration)
  have hbridge := bridge_slopes_and_taylor hstart hreach hB hPpos G hR hfloor
  refine ⟨R', hR'm, hR'R, hmass, ?_, ?_⟩
  · intro i q hq q' hq' hcode
    exact (hbridge i).2 q (hR'R hq) q' (hR'R hq') hcode
  · have hcover' : ∃ L : ℝ → ℤ → Finset ℝ,
        (∀ t z, ((L t z).card : ℝ) ≤ 1000 * scalarBlockFitBound P ^ 2) ∧
        ∀ q ∈ R', ∃ v ∈ L q.2 ⌊D.scalar F q.1 q.2 / scalarDyadicLength (start read)⌋,
          |scalarFirstJet D F (G.slope idx) q.1 q.2 - v| ≤
            scalarDyadicLength (start read) ^ ((1 - d) / 32) := by
      simpa only [hreadMesh] using hcover
        (scalarDyadicLength (start read) ^ ((1 - d) / 32)) (by rw [hreadMesh])
    obtain ⟨L, hL, hLcover⟩ := hcover'
    refine ⟨L, hL, ?_⟩
    intro q hq
    obtain ⟨v, hv, hdist⟩ := hLcover q hq
    refine ⟨v, hv, ?_⟩
    have hslope := (hbridge read).1 q (hR'R hq)
    have hy := (h.active_bounds hK (hR (hR'R hq)).1).2.1
    have htransport := scalar_first_jet_reading_transport
      (R := D.residual F q.1 q.2) (A := G.slope idx q.2)
      (A' := G.slope (scalarBridgeTopIndex m steps) q.2) (y := D.y q.1 q.2) (v := v) hd0
      (scalarDyadicLength_pos _) (scalarDyadicLength_le_one _) (by positivity :
        0 ≤ 32 * (steps + 1 : ℕ) * B * P)
      (by linarith [hK] : 0 ≤ 2 * K) hdist hslope hy
    -- `scalarFirstJet` unfolds definitionally to the transported reading;
    -- only the constant `32 * 2 = 64` needs `ring`.
    exact htransport.trans (le_of_eq (by ring))

end ScalarGridHierarchy

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
