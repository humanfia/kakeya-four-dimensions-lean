import Submission.Obl.k4_unbounded_geometric_packet_reduction.RecoveredAtlas
import Submission.Obl.k4_unbounded_geometric_packet_reduction.OriginalRecoveryMass

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory
open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

def scalarRecoveryEvent {p : Data} {k M D : ℕ} {d s c : ℝ}
    (a : Atlas p k) (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (b : Fin a.C) (out : ScalarCandidates (p.N k) d s c M D) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {z | ∃ i, packetCoeff a offset tangent b z.1 ∈ out.assignment i ∧
    i ∈ out.lists (packetObservation a b z)}

def originalChildEvent {p : Data} {k M D : ℕ} {d s c : ℝ}
    (a : Atlas p k) (offset : Fin a.C → ℝ) (tangent : Fin a.C → Fin 3 → ℝ)
    (b : Fin a.C) (out : ScalarCandidates (p.N k) d s c M D) (i : Fin out.count) :
    Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
  {z | z ∈ recoveredIncidence a offset tangent b (out.assignment i) ∧
    i ∈ out.lists (gobs (p.B k (a.γ b)) (gδ (p.N k) p.L) z)}

def atlasSuccessMass {p : Data} {k : ℕ} (a : Atlas p k) : ENNReal :=
  ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume)
    {z | z ∈ a.F b ∧ b ∈ a.lst (a.γ b) (gobs (p.B k (a.γ b)) (gδ (p.N k) p.L) z)}

theorem ProjectedPackets.originalChildEvent_measurable
    {p : Data} {k Mp Dp Mq Dq : ℕ} {loss h η d s m S U c : ℝ}
    (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (b : Fin a.atlas.C) (out : ScalarCandidates (p.N k) d s c Mq Dq)
    (i : Fin out.count) :
    MeasurableSet (originalChildEvent a.atlas a.offset a.tangent b out i) := by
  obtain ⟨_, _, _, _, _, _, hA, hF, _, _, _, _⟩ := a.known.1.2.2.1 b
  have hmA : MeasurableSet
      (recoveredAssignment a.atlas a.offset a.tangent b (out.assignment i)) :=
    hA.inter ((out.tests i).2.2.1.preimage (scalarCoeff_measurable _ _ _ _ _))
  exact (hF.inter (hmA.preimage measurable_fst)).inter
    ((out.list_measurable i).preimage
      (Submission.Obl.k4_horizon_light_cell_mass.pureMap_measurable _ _))

/-- Recovering in a fixed normalized packet pays the sum of its disjoint
children on the original, unconditioned incidence law. -/
theorem ProjectedPackets.original_recovery_mass
    {p : Data} {k Mp Dp Mq Dq : ℕ} {loss h η d s m S U c : ℝ}
    (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (b : Fin a.atlas.C) (out : ScalarCandidates (p.N k) d s c Mq Dq) :
    packetBudget a.atlas b *
        a.law b (scalarRecoveryEvent a.atlas a.offset a.tangent b out) ≤
      ∑ i, ((p.ν k (a.atlas.γ b)).prod volume)
        (originalChildEvent a.atlas a.offset a.tangent b out i) := by
  classical
  obtain ⟨_, _, _, _, _, _, hA, hF, _, _, hpoints, _⟩ := a.known.1.2.2.1 b
  let O := gobs (p.B k (a.atlas.γ b)) (gδ (p.N k) p.L)
  let S' : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
    {z | ∃ i, packetCoeff a.atlas a.offset a.tangent b z.1 ∈ out.assignment i ∧
      i ∈ out.lists (O z)}
  have hO : Measurable O :=
    Submission.Obl.k4_horizon_light_cell_mass.pureMap_measurable _ _
  have hS' : MeasurableSet S' := by
    change MeasurableSet {z | ∃ i, packetCoeff a.atlas a.offset a.tangent b z.1 ∈
      out.assignment i ∧ i ∈ out.lists (O z)}
    rw [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    exact (((out.tests i).2.2.1.preimage
      ((clippedScalarCoeff_measurable _ _ _ _ _ hA).comp measurable_fst)).inter
      ((out.list_measurable i).preimage hO))
  have heq : a.atlas.F b ∩ S' =
      ⋃ i, originalChildEvent a.atlas a.offset a.tangent b out i := by
    ext z
    constructor
    · rintro ⟨hz, i, hAi, hLi⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i, ⟨hz, (hpoints z hz).2.1, ?_⟩, hLi⟩
      simpa only [packetCoeff, clippedScalarCoeff_eq _ _ _ _ _ (hpoints z hz).2.1,
        Set.mem_preimage] using hAi
    · intro hz
      obtain ⟨i, ⟨hFz, hAz, hAi⟩, hLi⟩ := Set.mem_iUnion.mp hz
      refine ⟨hFz, i, ?_, hLi⟩
      simpa only [packetCoeff, clippedScalarCoeff_eq _ _ _ _ _ hAz, Set.mem_preimage] using hAi
  have hdisj : Pairwise (fun i j => Disjoint
      (originalChildEvent a.atlas a.offset a.tangent b out i)
      (originalChildEvent a.atlas a.offset a.tangent b out j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    exact Set.disjoint_left.mp (out.disjoint i j hij) hzi.1.2.2 hzj.1.2.2
  calc
    _ ≤ ((p.ν k (a.atlas.γ b)).prod volume) (a.atlas.F b ∩ S') :=
      dominated_map_recovery_mass (a.law b) _ (packetExpand a.atlas b)
        (packetExpand_measurable _ _) _ _ S' hS' (a.original_domination b)
    _ = _ := by
      rw [heq, measure_iUnion hdisj (a.originalChildEvent_measurable b out), tsum_fintype]

theorem ProjectedPackets.recovered_event_eq
    {p : Data} {k Mp Dp Mq Dq : ℕ} {loss h η d s m S U c : ℝ}
    (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (out : Fin a.atlas.C → ScalarCandidates (p.N k) d s c Mq Dq)
    (i : Fin (recoveredAtlas a.atlas a.offset a.tangent out).C) :
    let a' := recoveredAtlas a.atlas a.offset a.tangent out
    {z | z ∈ a'.F i ∧ i ∈ a'.lst (a'.γ i)
        (gobs (p.B k (a'.γ i)) (gδ (p.N k) p.L) z)} =
      originalChildEvent a.atlas a.offset a.tangent
        ((candidateEquiv out).symm i).1 (out ((candidateEquiv out).symm i).1)
        ((candidateEquiv out).symm i).2 := by
  let bi := (candidateEquiv out).symm i
  ext z
  change (z ∈ (recoveredAtlas a.atlas a.offset a.tangent out).F i ∧
    i ∈ (recoveredAtlas a.atlas a.offset a.tangent out).lst
      ((recoveredAtlas a.atlas a.offset a.tangent out).γ i)
      (gobs (p.B k ((recoveredAtlas a.atlas a.offset a.tangent out).γ i))
        (gδ (p.N k) p.L) z)) ↔ _
  rw [recoveredAtlas_list_mem]
  change (z ∈ recoveredIncidence a.atlas a.offset a.tangent bi.1 ((out bi.1).assignment bi.2) ∧
    bi.1 ∈ a.atlas.lst (a.atlas.γ bi.1) (gobs (p.B k (a.atlas.γ bi.1)) (gδ (p.N k) p.L) z) ∧
    bi.2 ∈ (out bi.1).lists (gobs (p.B k (a.atlas.γ bi.1)) (gδ (p.N k) p.L) z)) ↔ _
  constructor
  · rintro ⟨hz, _, hi⟩
    exact ⟨hz, hi⟩
  · rintro ⟨hz, hi⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlst⟩ := a.known.1.2.2.1 bi.1
    exact ⟨hz, hlst z hz.1, hi⟩

/-- Summing the actual children introduces no count factor in the recovered
mass.  The reindexing merely turns a finite dependent sum into an atlas. -/
theorem ProjectedPackets.recovered_mass_eq
    {p : Data} {k Mp Dp Mq Dq : ℕ} {loss h η d s m S U c : ℝ}
    (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (out : Fin a.atlas.C → ScalarCandidates (p.N k) d s c Mq Dq) :
    atlasSuccessMass (recoveredAtlas a.atlas a.offset a.tangent out) =
      ∑ b, ENNReal.ofReal (p.ω k (a.atlas.γ b)) *
        ∑ i, ((p.ν k (a.atlas.γ b)).prod volume)
          (originalChildEvent a.atlas a.offset a.tangent b (out b) i) := by
  classical
  unfold atlasSuccessMass
  rw [← (candidateEquiv out).sum_comp, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [a.recovered_event_eq out (candidateEquiv out ⟨b, i⟩)]
  exact congrArg (fun bi : CandidateIndex out =>
    ENNReal.ofReal (p.ω k (a.atlas.γ bi.1)) *
      ((p.ν k (a.atlas.γ bi.1)).prod volume)
        (originalChildEvent a.atlas a.offset a.tangent bi.1 (out bi.1) bi.2))
    ((candidateEquiv out).symm_apply_apply ⟨b, i⟩)

/-- Light-packet pruning and every conditional recovery are paid by the one
original assignment budget. -/
theorem ProjectedPackets.recovered_mass
    {p : Data} {k Mp Dp Mq Dq : ℕ} {loss h η d s m S U c : ℝ}
    (hp : Valid p) (a : ProjectedPackets p k Mp Dp loss h η d s m S U)
    (out : Fin a.atlas.C → ScalarCandidates (p.N k) d s c Mq Dq)
    (hsuccess : ∀ b, ENNReal.ofReal (p.N k ^ (-η)) ≤ a.law b Set.univ →
      ENNReal.ofReal (1 / 2 : ℝ) * a.law b Set.univ ≤
        a.law b (scalarRecoveryEvent a.atlas a.offset a.tangent b (out b))) :
    ENNReal.ofReal (p.N k ^ (-loss)) ≤
      2 * atlasSuccessMass (recoveredAtlas a.atlas a.offset a.tangent out) +
        ENNReal.ofReal (p.N k ^ (-η)) := by
  have hb := packet_recovery_mass
    (fun b => ENNReal.ofReal (p.ω k (a.atlas.γ b)) * packetBudget a.atlas b)
    (fun b => a.law b Set.univ)
    (fun b => a.law b (scalarRecoveryEvent a.atlas a.offset a.tangent b (out b)))
    (ENNReal.ofReal (p.N k ^ (-η))) (a.budget_le_one hp)
    (fun b h => twice_recovered_mass (hsuccess b h))
  apply a.retained_mass.trans (hb.trans ?_)
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  rw [a.recovered_mass_eq out]
  apply Finset.sum_le_sum
  intro b _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (a.original_recovery_mass b (out b)) zero_le

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
