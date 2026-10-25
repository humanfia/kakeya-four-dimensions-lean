import Submission.Obl.k4_raw_localized_native_systems.C.PacketRecovery

/-
Adapted from this LOT tree, o178, session x0596, `ScalarCandidates.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The finite output data of scalar recovery, also allowing an empty family
for a packet discarded because its mass is below the common threshold. -/
structure ScalarCandidates (N d s c : ℝ) (M D : ℕ) where
  count : ℕ
  poly : Fin count → MvPolynomial (Fin 2) ℝ
  assignment : Fin count → Set (Fin 5 → ℝ)
  lists : (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin count)
  count_bound : (count : ℝ) ≤ N ^ (d * s + 1)
  tests : ∀ i, (poly i).totalDegree ≤ 2 ∧ (∀ e, |(poly i).coeff e| ≤ N) ∧
    MeasurableSet (assignment i) ∧ gfmt 5 (N ^ M) D (assignment i) ∧
    ∀ z ∈ assignment i, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |scalarX z t - MvPolynomial.eval ![t, scalarY z t] (poly i)| ≤ N ^ (-c)
  disjoint : ∀ i j, i ≠ j → Disjoint (assignment i) (assignment j)
  list_bound : ∀ o, (lists o).card ≤ M
  list_measurable : ∀ i, MeasurableSet {o | i ∈ lists o}

def ScalarCandidates.empty {N d s c : ℝ} {M D : ℕ} (hN : 0 ≤ N) :
    ScalarCandidates N d s c M D where
  count := 0
  poly := Fin.elim0
  assignment := Fin.elim0
  lists := fun _ => ∅
  count_bound := by simpa using Real.rpow_nonneg hN (d * s + 1)
  tests := fun i => Fin.elim0 i
  disjoint := fun i => Fin.elim0 i
  list_bound := fun _ => by simp
  list_measurable := fun i => Fin.elim0 i

def ScalarRecovery.toCandidates {N d s c : ℝ} {M D : ℕ}
    {μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {b : (ℕ × (Fin 6 → ℝ)) → Fin 5 → ℝ}
    {O : ((ℕ × (Fin 6 → ℝ)) × ℝ) → EuclideanSpace ℝ (Fin 3) × ℤ}
    (a : ScalarRecovery N d s c 1 M D μ b O) : ScalarCandidates N d s c M D where
  count := a.count
  poly := a.poly
  assignment := a.assignment
  lists := a.lists
  count_bound := a.count_bound
  tests := by simpa only [Real.rpow_one] using a.tests
  disjoint := a.disjoint
  list_bound := a.list_bound
  list_measurable := a.list_measurable

/-- Choosing the scalar output at every parent packet keeps the same fixed
coefficient format, and loses mass only in packets below the stated threshold.
The child counts may depend on the parent; their dependent sum is finite. -/
theorem ProjectedPackets.recover_candidates
    {p : Data} {k Mp Dp : ℕ} {loss h η d s m S U c : ℝ} {M D : ℕ}
    (hp : Valid p)
    (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (hrule : ScalarRecoveryRule (p.N k) η d s m S U c M D) :
    ∃ out : Fin a.atlas.C → ScalarCandidates (p.N k) d s c M D,
      ∀ b, ENNReal.ofReal (p.N k ^ (-η)) ≤ a.law b Set.univ →
        ENNReal.ofReal (1 / 2 : ℝ) * a.law b Set.univ ≤
          a.law b {z | ∃ i, packetCoeff a.atlas a.offset a.tangent b z.1 ∈
            (out b).assignment i ∧ i ∈ (out b).lists (packetObservation a.atlas b z)} := by
  classical
  let recovered := Classical.choice (a.recover hrule)
  let out (b : Fin a.atlas.C) : ScalarCandidates (p.N k) d s c M D :=
    if hb : ENNReal.ofReal (p.N k ^ (-η)) ≤ a.law b Set.univ then
      (recovered ⟨b, hb⟩).toCandidates
    else ScalarCandidates.empty (hp.scale_pos k).le
  refine ⟨out, fun b hb => ?_⟩
  have hout : out b = (recovered ⟨b, hb⟩).toCandidates := by
    dsimp only [out]
    exact dif_pos hb
  rw [hout]
  exact (recovered ⟨b, hb⟩).success

end
end Submission.Obl.k4_raw_localized_native_systems.C
