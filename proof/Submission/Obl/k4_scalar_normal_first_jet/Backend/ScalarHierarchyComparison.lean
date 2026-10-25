/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarHierarchyComparison.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarHierarchyComparison.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarGridHierarchy
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAffineCoherence

/-! Compare hierarchy slopes on stored original child fitting times. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open Submission.Obl.k4_scalar_marked_coefficient_smoothing

namespace ScalarGridHierarchy

theorem time_fit {Λ : Type*} [MeasurableSpace Λ] {n : ℕ} {ν : Measure Λ}
    {E : Set (Λ × ℝ)} {F : ℝ → ℝ} {J : Fin n → ℕ} {hJ : ∀ i, 0 < J i}
    {p : Fin n → ℝ} {B : ℝ} (G : ScalarGridHierarchy ν E F J hJ p B)
    (i : Fin n) {t : ℝ} (ht : t ∈ G.times) :
    |F t - (G.intercept i t + G.slope i t * t)| ≤ B * (1 / (J i : ℝ)) * p i := by
  obtain ⟨l, hl⟩ := G.active_time ht
  exact G.fit i (l, t) ⟨hl, mem_univ _, ht⟩

theorem slopes_close_on_original_child {Λ : Type*} [MeasurableSpace Λ] {n : ℕ}
    {ν : Measure Λ} [IsProbabilityMeasure ν] {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    {J : Fin n → ℕ} {hJ : ∀ i, 0 < J i} {p : Fin n → ℝ} {B ell : ℝ}
    (G : ScalarGridHierarchy ν E F J hJ p B) (i j : Fin n) {u : ℝ} (hu : u ∈ G.times)
    (hell : 0 < ell)
    (hfloor : ENNReal.ofReal ell ≤ (ν.prod volume)
      ((E ∩ (univ ×ˢ G.times)) ∩
        (univ ×ˢ timeCell (J j) (scalarTimeBlockCode (J j) (hJ j) u))))
    (hnesting : ∀ t ∈ G.times,
      scalarTimeBlockCode (J j) (hJ j) t = scalarTimeBlockCode (J j) (hJ j) u →
      scalarTimeBlockCode (J i) (hJ i) t = scalarTimeBlockCode (J i) (hJ i) u) :
    |G.slope i u - G.slope j u| ≤
      4 * (B * (1 / (J i : ℝ)) * p i + B * (1 / (J j : ℝ)) * p j) / ell := by
  let U := G.times ∩ timeCell (J j) (scalarTimeBlockCode (J j) (hJ j) u)
  have hmassle : (ν.prod volume)
      ((E ∩ (univ ×ˢ G.times)) ∩
        (univ ×ˢ timeCell (J j) (scalarTimeBlockCode (J j) (hJ j) u))) ≤ volume U := by
    calc
      _ ≤ (ν.prod volume) (univ ×ˢ U) := measure_mono (fun q hq => ⟨mem_univ _, hq.1.2.2, hq.2.2⟩)
      _ = _ := by rw [Measure.prod_prod, measure_univ, one_mul]
  have hUvol : ENNReal.ofReal ell ≤ volume U := hfloor.trans hmassle
  have hrows t (ht : t ∈ U) :
      (G.slope i t = G.slope i u ∧ G.intercept i t = G.intercept i u) ∧
      (G.slope j t = G.slope j u ∧ G.intercept j t = G.intercept j u) := by
    have hcode : scalarTimeBlockCode (J j) (hJ j) t = scalarTimeBlockCode (J j) (hJ j) u :=
      scalarTimeBlockCode_on_cell (hJ j) _ ht.2
    exact ⟨G.constant_on_grid i t ht.1 u hu (hnesting t ht.1 hcode),
      G.constant_on_grid j t ht.1 u hu hcode⟩
  apply affine_slopes_close_on_long_set (f := F)
    (a := G.intercept i u) (b := G.intercept j u) hell hUvol
  · intro t ht
    simpa only [(hrows t ht).1.1, (hrows t ht).1.2] using G.time_fit i ht.1
  · intro t ht
    simpa only [(hrows t ht).2.1, (hrows t ht).2.2] using G.time_fit j ht.1

end ScalarGridHierarchy

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
