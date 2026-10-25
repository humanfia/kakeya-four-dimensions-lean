import Submission.Obl.k4_scalar_marked_packet_recovery.AssignmentMass
import Submission.Obl.k4_scalar_marked_packet_recovery.MassNumerics

namespace Submission.Obl.k4_scalar_marked_packet_recovery

open Set MeasureTheory
open scoped ENNReal

/-- The geometric clauses of a packet, at loss factor `E` and error scale `a`. -/
def PacketGeometry {α : Type*} (E a β t₀ q : ℝ) (b : α → Coeff) (A : Set α)
    (u v : ℝ) (P : MvPolynomial (Fin 2) ℝ) : Prop :=
  |u| + |v| ≤ E ∧ P.totalDegree ≤ 2 ∧
    (∀ t ∈ Icc t₀ (t₀ + q), ∀ w ∈ Icc (-1 : ℝ) 1,
      |MvPolynomial.eval ![t, u + t * v + β * w] P| ≤ E) ∧
    ∀ l ∈ A, ∀ t ∈ Icc t₀ (t₀ + q),
      |b l 0 + t * b l 1 - u - t * v| ≤ E * β ∧
      |b l 2 + t * b l 3 + t ^ 2 * b l 4 -
        MvPolynomial.eval ![t, b l 0 + t * b l 1] P| ≤ E * a

/-- The complete mass assembly; only geometric stability remains as an input. -/
theorem recover_system {α : Type} [MeasurableSpace α]
    {N K d s m c η ε : ℝ} (hN : 1 ≤ N) (hK : 0 < K) (hη : 0 ≤ η)
    (hηε : η ≤ ε) (hgap : 4 * K * (N ^ η) ^ 3 ≤ N ^ ε)
    {H J n : ℕ} (hJ : 0 < J) (μ : Measure (α × ℝ)) (b : α → Coeff)
    (tag : α → Fin H) (htag : Measurable tag) (b₀ : Fin H → Coeff)
    (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (mark : Fin H → Fin J → Bool)
    (hmark : ∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤
      μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z})
    (angular : Bool) (β t₀ q : ℝ) (A : Fin n → Set Label)
    (hq : N ^ (-η) ≤ q) (ht₀ : 0 ≤ t₀) (htq : t₀ + q ≤ 1)
    (hβ : N ^ (-m) / N ^ η ≤ β) (hβ' : β ≤ N ^ η)
    (hang : angular = true → N ^ (-η) ≤ β)
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hfloor : ∀ i, ENNReal.ofReal (q * c * (N ^ (-s)) ^ d * β / N ^ η) ≤
      MarkedLaw (N ^ (-m)) H J b₀ w mark (A i ×ˢ Icc t₀ (t₀ + q)))
    (hmass : ENNReal.ofReal (N ^ (-η)) ≤ MarkedLaw (N ^ (-m)) H J b₀ w mark
      {p | (∃ i, p.1 ∈ A i) ∧ p.2 ∈ Icc t₀ (t₀ + q)})
    (hgeometry : ∀ u : Coeff, (∀ e, u e ∈ Icc (0 : ℝ) (N ^ (-m))) →
      ∀ i, ∃ (u' v' : ℝ) (P' : MvPolynomial (Fin 2) ℝ),
        PacketGeometry (N ^ ε) (N ^ (-s)) β t₀ q b
          (originalAssignment b₀ tag u (A i)) u' v' P') :
    BlockOutput N d s m c ε angular α μ b := by
  classical
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hσ : 0 < N ^ (-m) := Real.rpow_pos_of_pos hN0 _
  have hL : 0 < N ^ η := Real.rpow_pos_of_pos hN0 _
  have hE : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 _
  have hLE : N ^ η ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN hηε
  have hq' : (N ^ η)⁻¹ ≤ q := by simpa only [Real.rpow_neg hN0.le] using hq
  let C := c * (N ^ (-s)) ^ d * β
  let Q := MarkedLaw (N ^ (-m)) H J b₀ w mark
  have hbudget0 : (n : ℝ≥0∞) * ENNReal.ofReal (q * C / N ^ η) ≤ 1 := by
    apply packet_floor_budget Q (fun i => A i ×ˢ Icc t₀ (t₀ + q))
      (fun i => (hA i).prod measurableSet_Icc) ?_ ?_
      (markedLaw_mass_le_one hσ hJ b₀ w mark hw hw1)
    · intro i j hij
      exact Set.disjoint_left.mpr fun p hp hp' => Set.disjoint_left.mp (hdisj hij) hp.1 hp'.1
    · intro i
      convert hfloor i using 1
      congr 1
      dsimp [C]
      ring
  have hbudget := scaled_packet_budget hL hE hK hq' hgap hbudget0
  rw [← Real.rpow_neg hN0.le] at hbudget
  have hmass' : ENNReal.ofReal (N ^ (-η)) ≤ Q ((⋃ i, A i) ×ˢ (univ : Set ℝ)) := by
    apply hmass.trans (measure_mono ?_)
    intro p hp
    exact ⟨mem_iUnion.mpr hp.1, mem_univ _⟩
  obtain ⟨jitter, hjitter, n', e, he, hf, hm⟩ := recover_assignment_mass hσ hK hJ
    μ tag htag b₀ w hw mark hmark A hA hdisj (Real.rpow_pos_of_pos hN0 _) hmass' hbudget
  choose u' v' P' hgeom using fun i : Fin n' => hgeometry jitter hjitter (e i)
  refine ⟨n', β, t₀, q, fun i => originalAssignment b₀ tag jitter (A (e i)),
    u', v', P', ?_, ht₀, htq, ?_, hβ'.trans hLE, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hηε)).trans hq
  · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) hL hLE).trans hβ
  · intro ha
    exact (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hηε)).trans (hang ha)
  · intro i
    exact measurableSet_originalAssignment b₀ htag jitter (hA (e i))
  · intro i j hij
    exact originalAssignment_disjoint b₀ tag jitter (hdisj (he.ne hij))
  · intro i
    exact ⟨(hgeom i).1, (hgeom i).2.1, (hgeom i).2.2.1, (hgeom i).2.2.2, hf i⟩
  · apply le_trans ?_ hm
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_neg hN0.le]
    simpa only [Real.rpow_neg hN0.le] using
      retained_mass_bound (Real.one_le_rpow hN hη) hK hgap

end Submission.Obl.k4_scalar_marked_packet_recovery
