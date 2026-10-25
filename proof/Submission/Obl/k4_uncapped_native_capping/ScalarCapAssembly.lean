/-
Adapted from this LOT tree o198, session x0691, commit 9816360a0a6a894f89615acd484d1584ad77897e,
Submission/Obl/k4_balanced_native_packet_transport/ScalarCapAssembly.lean. Existing source attributions below are retained.
-/
import Submission.Obl.k4_uncapped_native_capping.Definitions
import Submission.Obl.k4_uncapped_native_capping.ScalarMeshCaps

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
noncomputable section

theorem scalarZ_eq_iff (b : Traj → Fin 5 → ℝ) (p : Inc) (σ : ℝ) (q : Fin 2 → ℤ) :
    scalarZ (b p.1) p.2 σ = q ↔
      ∀ i, ⌊(WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] :
        EuclideanSpace ℝ (Fin 2)) i / σ⌋ = q i := by
  constructor
  · intro h i
    fin_cases i
    · simpa [scalarZ] using congrFun h 0
    · simpa [scalarZ] using congrFun h 1
  · intro h
    funext i
    fin_cases i
    · simpa [scalarZ] using h 0
    · simpa [scalarZ] using h 1

/-- Continuous original base caps yield both frozen mesh caps, with the exact
area factor and with no change of the angular gain. -/
theorem ScalarCaps.of_continuous
    {N χ d s m S U : ℝ} (hN : 0 < N)
    {ν : Measure Traj} {μ : Measure Inc} {b : Traj → Fin 5 → ℝ}
    (hregular : RegularScalarLaw N χ d s m S U ν μ b)
    (hpure : ∀ (r : ℝ) (j : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
      0 ≤ r → r ≤ s → MeasurableSet E →
      μ {p | WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∈ E ∧
        ⌊scalarX (b p.1) p.2 / N ^ (-r)⌋ = j} ≤
          ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d) * volume E)
    (hangular : ∀ (r : ℝ) (j k : ℤ) (E : Set (EuclideanSpace ℝ (Fin 2))),
      0 < r → r ≤ U → MeasurableSet E →
      μ {p | WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2] ∈ E ∧
        ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋ = j ∧ ⌊b p.1 1 / N ^ (-r)⌋ = k} ≤
          ENNReal.ofReal (N ^ χ * (N ^ (-s)) ^ d * N ^ (-S * r)) * volume E) :
    ScalarCaps N χ d s m S U ν μ b := by
  obtain ⟨hb, hν, hdom, htime, hcoeff⟩ := hregular
  refine ⟨hb, hν, hdom, htime, hcoeff, ?_, ?_, hpure⟩
  · intro r q j hr hrs
    have h := ScalarMesh.mesh_cell_cap_of_continuous μ
      (fun p => WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2])
      {p | ⌊scalarX (b p.1) p.2 / N ^ (-r)⌋ = j}
      (ENNReal.ofReal (N ^ χ * (N ^ (-r)) ^ d))
      (fun E hE => hpure r j E hr hrs hE) (Real.rpow_pos_of_pos hN (-m)) q
    simp only [← scalarZ_eq_iff] at h
    apply h.trans_eq
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · intro r q j k hr hrU
    have h := ScalarMesh.mesh_cell_cap_of_continuous μ
      (fun p => WithLp.toLp 2 ![p.2, scalarY (b p.1) p.2])
      {p | ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋ = j ∧ ⌊b p.1 1 / N ^ (-r)⌋ = k}
      (ENNReal.ofReal (N ^ χ * (N ^ (-s)) ^ d * N ^ (-S * r)))
      (fun E hE => hangular r j k E hr hrU hE) (Real.rpow_pos_of_pos hN (-m)) q
    simp only [← scalarZ_eq_iff] at h
    apply h.trans_eq
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

theorem ScalarCaps.mono
    {N χ d s m S U : ℝ} {ν : Measure Traj} {μ μ' : Measure Inc}
    {b : Traj → Fin 5 → ℝ} (h : ScalarCaps N χ d s m S U ν μ b) (hμ : μ' ≤ μ) :
    ScalarCaps N χ d s m S U ν μ' b := by
  obtain ⟨hb, hν, hdom, htime, hcoeff, hpure, hangular, hcont⟩ := h
  exact ⟨hb, hν, hμ.trans hdom, le_antisymm ((hμ _).trans_eq htime) bot_le,
    hcoeff, fun r q j hr hrs => (hμ _).trans (hpure r q j hr hrs),
    fun r q j k hr hrU => (hμ _).trans (hangular r q j k hr hrU),
    fun r j E hr hrs hE => (hμ _).trans (hcont r j E hr hrs hE)⟩

end
end Submission.Obl.k4_uncapped_native_capping
