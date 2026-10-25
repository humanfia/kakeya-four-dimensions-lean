import Submission.Obl.k4_adapted_oscillation_tests.Frame

noncomputable section

/-! Adapted from this LOT tree o120, x0649, commit 5b5fe35d,
`MeshCellCaps.lean`. The original proof uses the accepted box-volume formula. -/

namespace Submission.Obl.k4_balanced_native_packet_transport.ScalarMesh

open MeasureTheory Set

def packetMeshBox (σ : ℝ) (q : Fin 2 → ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  WithLp.toLp 2 '' Icc (fun i => σ * (q i : ℝ)) (fun i => σ * ((q i : ℝ) + 1))

theorem measurableSet_packetMeshBox (σ : ℝ) (q : Fin 2 → ℤ) :
    MeasurableSet (packetMeshBox σ q) := by
  exact (isCompact_Icc.image (show Continuous (WithLp.toLp 2 :
    (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) by fun_prop)).measurableSet

theorem volume_packetMeshBox {σ : ℝ} (hσ : 0 ≤ σ) (q : Fin 2 → ℤ) :
    volume (packetMeshBox σ q) = ENNReal.ofReal (σ ^ 2) := by
  rw [packetMeshBox, Submission.Obl.k4_adapted_oscillation_tests.volume_box]
  have heq (i : Fin 2) : σ * ((q i : ℝ) + 1) - σ * (q i : ℝ) = σ := by ring
  simp_rw [heq]
  rw [Fin.prod_univ_two, ← ENNReal.ofReal_mul hσ]
  congr 1
  ring

theorem mem_packetMeshBox_of_floor {σ : ℝ} (hσ : 0 < σ)
    (q : Fin 2 → ℤ) (z : EuclideanSpace ℝ (Fin 2))
    (hz : ∀ i, ⌊z i / σ⌋ = q i) : z ∈ packetMeshBox σ q := by
  refine ⟨fun i => z i, ⟨?_, ?_⟩, rfl⟩
  · intro i
    have h := Int.floor_le (z i / σ)
    rw [hz i] at h
    exact (mul_comm σ (q i : ℝ)).le.trans ((le_div_iff₀ hσ).1 h)
  · intro i
    have h := Int.lt_floor_add_one (z i / σ)
    rw [hz i] at h
    exact ((div_lt_iff₀ hσ).1 h).le.trans_eq (mul_comm _ _)

/-- Every continuous base cap immediately gives the required scalar mesh cap,
also with any additional signal or angular event. -/
theorem mesh_cell_cap_of_continuous {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (base : Ω → EuclideanSpace ℝ (Fin 2)) (V : Set Ω)
    (C : ENNReal)
    (hcap : ∀ U : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet U →
      μ {p | base p ∈ U ∧ p ∈ V} ≤ C * volume U)
    {σ : ℝ} (hσ : 0 < σ) (q : Fin 2 → ℤ) :
    μ {p | (∀ i, ⌊base p i / σ⌋ = q i) ∧ p ∈ V} ≤ C * ENNReal.ofReal (σ ^ 2) := by
  calc
    _ ≤ μ {p | base p ∈ packetMeshBox σ q ∧ p ∈ V} :=
      measure_mono (fun p hp => ⟨mem_packetMeshBox_of_floor hσ q (base p) hp.1, hp.2⟩)
    _ ≤ C * volume (packetMeshBox σ q) := hcap _ (measurableSet_packetMeshBox σ q)
    _ = _ := by rw [volume_packetMeshBox hσ.le]

end Submission.Obl.k4_balanced_native_packet_transport.ScalarMesh
