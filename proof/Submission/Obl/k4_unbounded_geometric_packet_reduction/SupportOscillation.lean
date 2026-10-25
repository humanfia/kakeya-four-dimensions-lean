import Submission.Obl.k4_unbounded_geometric_packet_reduction.PacketInterfaces
import Submission.Obl.k4_unbounded_geometric_packet_reduction.SupportCounting

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction

open MeasureTheory Filter

noncomputable section

/-- The earlier-label certificate after applying native oscillation.  It
retains a global original-budget mass estimate and counts labels within each
projected base cell. -/
structure OscillationPieces (N χ d s m : ℝ) (C Cpart : ℕ)
    (R : Fin C → ENNReal) (μ : Fin C → Measure Inc)
    (b : Fin C → Traj → Fin 5 → ℝ) where
  labels : ℕ
  parts : Fin labels → ℕ
  piece : Fin C → (e : Fin labels) → Fin (parts e) → Set Inc
  tags : Fin C → (Fin 2 → ℤ) → Finset (Fin labels)
  measurable : ∀ a e i, MeasurableSet (piece a e i)
  tag_bound : ∀ a q, ((tags a q).card : ℝ) ≤ N ^ (d * s + χ)
  listed : ∀ a e i p, p ∈ piece a e i →
    e ∈ tags a (scalarZ (b a p.1) p.2 (N ^ (-m)))
  part_bound : ∀ e, (parts e : ℝ) ≤ (N ^ χ) ^ Cpart
  native_oscillation : ∀ a e i p, p ∈ piece a e i → ∀ p', p' ∈ piece a e i →
    scalarZ (b a p.1) p.2 (N ^ (-m)) = scalarZ (b a p'.1) p'.2 (N ^ (-m)) →
    |scalarX (b a p.1) p.2 - scalarX (b a p'.1) p'.2| ≤
      2 * (N ^ χ) ^ Cpart * N ^ (-s + χ)
  retained : (∑ a, R a * μ a Set.univ) ≤
    (∑ a, R a * μ a (⋃ e, ⋃ i, piece a e i)) + ENNReal.ofReal (N ^ (-χ))

/-- Native oscillation is applied to the shared earlier laws, before any
packet conditioning.  Its exponent is fixed before all scalar tolerances. -/
theorem StableNativeOscillation.support_pieces (hV : StableNativeOscillation) :
    ∃ Cpart : ℕ, 1 ≤ Cpart ∧
      ∀ (N χ d s m : ℝ) (C : ℕ) (R : Fin C → ENNReal)
        (μ : Fin C → Measure Inc) (b : Fin C → Traj → Fin 5 → ℝ),
      2 ≤ N → χ ≤ s → SupportCertificate N χ d s m C R μ b →
        Nonempty (OscillationPieces N χ d s m C Cpart R μ b) := by
  classical
  obtain ⟨Cpart, hCpart, hV⟩ := hV 1
  refine ⟨Cpart, hCpart, ?_⟩
  intro N χ d s m C R μ b hN hχ hcert
  obtain ⟨J, w, Λ, P, S, tag, A, z, hw, hK, hdata, hA, hdom, hsignal,
    htags, hclose⟩ := hcert
  have hNpos : 0 < N := by linarith
  have ha : 0 < N ^ (-s + χ) := Real.rpow_pos_of_pos hNpos _
  have ha1 : N ^ (-s + χ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hpart e := hV (N ^ χ) (N ^ (-s + χ)) (P e) (S e) (Λ e)
    hK ha ha1 (hdata e).2.1 (hdata e).2.2.1 (hdata e).1
    (hdata e).2.2.2.1 (hdata e).2.2.2.2
  choose n E hn hEm hEd hBad hOsc using hpart
  let piece (a : Fin C) (e : Fin J) (i : Fin (n e)) : Set Inc :=
    {p | p ∈ A a ∧ tag a p = e ∧ z a e p ∈ E e i}
  let lists (a : Fin C) (q : Fin 2 → ℤ) : Finset (Fin J) :=
    Finset.univ.filter (fun e => ∃ p ∈ A a,
      scalarZ (b a p.1) p.2 (N ^ (-m)) = q ∧ tag a p = e)
  let bad (e : Fin J) : Set (EuclideanSpace ℝ (Fin 4)) := (⋃ i, E e i)ᶜ
  have hbadm e : MeasurableSet (bad e) := (MeasurableSet.iUnion (hEm e)).compl
  have hbad e : Λ e (bad e) ≤ ENNReal.ofReal (N ^ (-χ)) := by
    simpa only [pow_one, Real.rpow_neg hNpos.le] using hBad e
  have hglobal := weighted_tagged_exception_le μ Λ R w A tag z
    (fun a => (hA a).2.2.2.2) bad hbadm (ENNReal.ofReal (N ^ (-χ))) hw hbad hdom
  refine ⟨{
    labels := J
    parts := n
    piece := piece
    tags := lists
    measurable := ?_
    tag_bound := htags
    listed := ?_
    part_bound := hn
    native_oscillation := ?_
    retained := ?_ }⟩
  · intro a e i
    exact (hA a).2.2.1.inter
      (((measurableSet_singleton e).preimage (hA a).2.1).inter
        ((hEm e i).preimage ((hA a).2.2.2.2 e)))
  · intro a e i p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp.1, rfl, hp.2.1⟩
  · intro a e i p hp p' hp' hcell
    have htag : tag a p = tag a p' := hp.2.1.trans hp'.2.1.symm
    have hbase := hclose a p hp.1 p' hp'.1 htag hcell
    have hh := hOsc e i (z a e p) hp.2.2 (z a e p') hp'.2.2
    have hbase' : ‖base4 (z a e p) - base4 (z a e p')‖ ≤ N ^ (-s + χ) := by
      simpa only [hp.2.1] using hbase
    rw [hsignal a p hp.1, hsignal a p' hp'.1, hp.2.1, hp'.2.1]
    apply hh.trans
    have hnonneg : 0 ≤ (N ^ χ) ^ Cpart := pow_nonneg (Real.rpow_nonneg hNpos.le _) _
    calc
      _ ≤ (N ^ χ) ^ Cpart * (N ^ (-s + χ) + N ^ (-s + χ)) := by
        apply mul_le_mul_of_nonneg_left _ hnonneg
        apply add_le_add le_rfl
        simpa only [base4] using hbase'
      _ = _ := by ring
  · have hlocal a : μ a Set.univ ≤
        μ a (⋃ e, ⋃ i, piece a e i) +
          μ a {p | p ∈ A a ∧ z a (tag a p) p ∈ bad (tag a p)} := by
      have hcover : Set.univ ⊆
          ((⋃ e, ⋃ i, piece a e i) ∪
            {p | p ∈ A a ∧ z a (tag a p) p ∈ bad (tag a p)}) ∪ (A a)ᶜ := by
        intro p _
        by_cases hp : p ∈ A a
        · by_cases hz : z a (tag a p) p ∈ ⋃ i, E (tag a p) i
          · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
            exact Or.inl (Or.inl (Set.mem_iUnion.mpr
              ⟨tag a p, Set.mem_iUnion.mpr ⟨i, hp, rfl, hi⟩⟩))
          · exact Or.inl (Or.inr ⟨hp, hz⟩)
        · exact Or.inr hp
      calc
        _ ≤ μ a _ := measure_mono hcover
        _ ≤ (μ a (⋃ e, ⋃ i, piece a e i) +
            μ a {p | p ∈ A a ∧ z a (tag a p) p ∈ bad (tag a p)}) + μ a (A a)ᶜ :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
        _ = _ := by rw [(hA a).2.2.2.1, add_zero]
    calc
      _ ≤ ∑ a, R a * (μ a (⋃ e, ⋃ i, piece a e i) +
          μ a {p | p ∈ A a ∧ z a (tag a p) p ∈ bad (tag a p)}) :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hlocal a) zero_le)
      _ = (∑ a, R a * μ a (⋃ e, ⋃ i, piece a e i)) +
          ∑ a, R a * μ a {p | p ∈ A a ∧ z a (tag a p) p ∈ bad (tag a p)} := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl hglobal

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
