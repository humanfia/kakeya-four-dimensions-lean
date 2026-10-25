import Submission.Obl.k4_finite_positive_mixed_cover_realization.StripAtlas
import Submission.Obl.k4_finite_positive_mixed_cover_realization.ActualAlignmentMass
import Submission.Obl.k4_quadratic_finite_greedy_cover.Terminal

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory Set Submission.Lib.K4XInterface

lemma CoverData.usedStripPiece_raw_injective {W : ℕ} {p : PathData W}
    (c : CoverData p) (width : ℝ) :
    Function.Injective (fun q : c.UsedStripPiece width => (q.val.1, q.val.2.val)) := by
  intro q q' h
  have ha : q.val.1 = q'.val.1 := congrArg (fun t : Fin c.n × ℤ => t.1) h
  have hz : q.val.2.val = q'.val.2.val := congrArg (fun t : Fin c.n × ℤ => t.2) h
  exact Subtype.ext (Prod.ext ha (Subtype.ext hz))

open Classical in
/-- Geometric midpoint pieces cover every retained analytical incidence with
its unchanged world weight. Enlarging to the formatted output incidences can
only increase the original mass. -/
lemma CoverData.Valid.stripPieces_mass
    {W m Mp Dp Mg Dg j : ℕ} {p : PathData W} {c : CoverData p}
    {ℓ Nk L κ₁ δ₀ σ d₁ ρ gain ε width gap : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hc : c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε) (ht : c.time = false)
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hwidth : 0 < width) (normal : Fin p.C → Plane) (bias : Fin p.C → ℝ) :
    (∑ a : Fin c.n, ENNReal.ofReal (ω (p.world (c.old a))) *
      ((ν (p.world (c.old a))).prod volume) (c.alignedWitness normal bias gap j a)) ≤
      ∑ q : c.UsedStripPiece width, ENNReal.ofReal (ω (p.world (c.old q.val.1))) *
        ((ν (p.world (c.old q.val.1))).prod volume)
          (c.pieceIncidence width gap j normal bias q.val.1 q.val.2.val) := by
  classical
  let A (q : c.UsedStripPiece width) : Set Incidence :=
    c.pieceIncidence width gap j normal bias q.val.1 q.val.2.val ∩ c.interior q.val.1
  have hm (q : c.UsedStripPiece width) : MeasurableSet (A q) :=
    (hc.pieceIncidence_measurable hp j normal bias q.val.1 q.val.2.val).inter
      (hc.interior_measurable q.val.1)
  have hdisj (q q' : c.UsedStripPiece width) (hne : q ≠ q') (ha : q.val.1 = q'.val.1) :
      Disjoint (A q) (A q') := by
    have hpairs : (q.val.1, q.val.2.val) ≠ (q'.val.1, q'.val.2.val) :=
      fun heq => hne (c.usedStripPiece_raw_injective width heq)
    have hlines := hc.stripPieces_disjoint ht hp (width := width)
      q.val.1 q'.val.1 q.val.2.val q'.val.2.val hpairs
      (by rw [ha]) (by rw [ha])
    apply Set.disjoint_left.mpr
    intro v hv hv'
    exact Set.disjoint_left.mp hlines hv.1.1.2 hv'.1.1.2
  have hset (a : Fin c.n) : {v | ∃ q : c.UsedStripPiece width, q.val.1 = a ∧ v ∈ A q} =
      c.alignedWitness normal bias gap j a := by
    ext v
    constructor
    · rintro ⟨q, hqa, hv⟩
      have hinside := hv.2
      have htable := hv.1.2
      rw [hqa] at hinside htable
      exact ⟨hinside, htable⟩
    · intro hv
      have hvline := (hc.counted_support a hv.1.1).2.1
      obtain ⟨q, hqa, hvpiece⟩ := hc.stripPiece_coverage ht hp hwidth a v.1 hvline
      refine ⟨q, hqa, ?_⟩
      refine ⟨⟨⟨?_, hvpiece⟩, ?_⟩, ?_⟩
      · simpa only [hqa] using hc.interior_subset_old hp a hv.1
      · simpa only [hqa] using hv.2
      · simpa only [hqa] using hv.1
  have heq := k4_quadratic_finite_greedy_cover.weighted_assignment_union
    (fun a : Fin c.n => (ν (p.world (c.old a))).prod volume)
    (fun a : Fin c.n => ENNReal.ofReal (ω (p.world (c.old a))))
    (fun _ : c.UsedStripPiece width => True) (fun q => q.val.1) A
    (fun q _ => hm q) (fun q q' _ _ hne ha => hdisj q q' hne ha)
  simp only [true_and, ite_true] at heq
  simp_rw [hset] at heq
  apply heq.le.trans
  apply Finset.sum_le_sum
  intro q _
  exact mul_le_mul' le_rfl (measure_mono (show A q ⊆
    c.pieceIncidence width gap j normal bias q.val.1 q.val.2.val from inter_subset_left))

end Submission.Obl.k4_finite_positive_mixed_cover_realization
