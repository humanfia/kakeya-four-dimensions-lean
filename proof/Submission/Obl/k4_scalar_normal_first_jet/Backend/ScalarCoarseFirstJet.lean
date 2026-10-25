/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCoarseFirstJet.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCoarseFirstJet.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetOutput
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFirstJetNumerics

/-! Coarse first-jet certificates require only the original pointwise bounds. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set

/-- At scales at least `1/K`, keep the entire original event, use
the zero Taylor row and a single reading center. -/
theorem scalar_first_jet_coarse_output {Λ : Type*} [MeasurableSpace Λ] {m : ℕ}
    (D : ScalarMotion Λ) (ν : Measure Λ) {E : Set (Λ × ℝ)} {F : ℝ → ℝ}
    (start : Fin m → ℕ) (read : Fin m) {K B d : ℝ}
    (hK : 1 ≤ K) (hd : 0 ≤ d) (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hcoeff : ∀ p ∈ E, D.Bounded K p.1) (hrow : ∀ p ∈ E, |F p.2| ≤ K)
    (hmass : K⁻¹ ≤ (ν.prod volume).real E)
    (hscale : ∀ i, 1 / K ≤ scalarDyadicLength (start i)) (hbudget : 4 * K ^ 3 ≤ B) :
    ScalarFirstJetOutput D ν E F start read d B := by
  classical
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hpow1 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  have hpow : K ≤ K ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hK (by norm_num : 1 ≤ 3)
  have hB : 1 ≤ B := by linarith
  have hKB : K ≤ B := by linarith
  refine ⟨E, Subset.rfl, hE,
    ENNReal.ofReal_le_of_le_toReal ((inv_anti₀ hKpos hKB).trans hmass),
    (fun _ => 0), measurable_const, ?_, ?_, (fun _ _ => {(0 : ℝ)}), ?_, ?_⟩
  · intro p hp
    simpa only [abs_zero] using zero_le_one.trans hB
  · intro i j p hp q hq hpi hqi
    have herror : |F q.2 - F p.2| ≤ 2 * K :=
      (abs_sub _ _).trans (by linarith [hrow p hp, hrow q hq])
    have htaylor := scalar_first_jet_coarse_taylor hK (hscale i)
      (scalarDyadicLength_le_one _) hbudget
    simpa only [mul_zero, sub_zero] using herror.trans htaylor
  · intro t z
    simpa only [Finset.card_singleton, Nat.cast_one] using hB
  · intro p hp
    refine ⟨0, Finset.mem_singleton_self _, ?_⟩
    have hbound := (D.bounds_at_unit_time hK (hcoeff p hp) (hunit hp).2 (hrow p hp)).2.2.1
    have hreading := scalar_first_jet_coarse_reading hd hK (hscale read)
      (scalarDyadicLength_le_one _) hbudget
    simpa only [scalarFirstJet, zero_mul, sub_zero] using hbound.trans hreading

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
