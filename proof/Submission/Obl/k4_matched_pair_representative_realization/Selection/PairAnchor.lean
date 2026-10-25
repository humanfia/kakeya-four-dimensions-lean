/- Adapted within this LOT tree from o190/x0630, commit adb2f45f4ccde121d91c5954051b6c45263cd6de,
Submission/Obl/k4_pair_bin_atlas_assembly/PairAnchor.lean. Existing provenance comments are retained below. -/
import Submission.Obl.k4_matched_pair_representative_realization.Selection.PairFacts
import Submission.Obl.k4_matched_pair_representative_realization.Selection.ListSafeAnchor

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open Set MeasureTheory
open scoped ENNReal

namespace PairData

variable {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε : ℝ}
    (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε)

noncomputable def pairMass (G : Fin p.m → Set PairPoint) : ℝ≥0∞ :=
  ∑ s, ENNReal.ofReal (ωk (p.world s) * (2 : ℝ) ^ p.T) * p.pairLaw s (G s)

theorem pairMass_finite (hν : ∀ w, IsProbabilityMeasure (νk w)) : p.pairMass p.H ≠ ∞ :=
  ENNReal.sum_ne_top.mpr fun s _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (p.pairLaw_finite hν s)

/-- The original successful pair mass has a common safe anchor, after an
error at most `κ / N^a` times that original mass. -/
theorem exists_safe_anchor {Cs : ℕ} (hsafe : SafeProbability Cs)
    (hNk : 0 < Nk) (hA : 2 ≤ Nk ^ a)
    (hν : ∀ w, IsProbabilityMeasure (νk w)) :
    ∃ θ ∈ anchorDomain, ∃ G : Fin p.m → Set PairPoint,
      (∀ s, MeasurableSet (G s)) ∧ (∀ s, G s ⊆ p.H s) ∧
      (∀ s, ∀ v ∈ G s, ∀ s' ∈ p.sourceList s v,
        Nk ^ (-a) ≤ |MvPolynomial.eval (fun n => p.sourceBase s v n) (disc (p.P s'))| →
        SafeFor ((Nk ^ a) ^ (-(Cs : ℝ))) (disc (p.P s)) (disc (p.P s'))
          (p.sourceBase s v) θ.1 θ.2) ∧
      p.pairMass p.H ≤ p.pairMass G +
        ENNReal.ofReal (p.κ * (Nk ^ a)⁻¹) * p.pairMass p.H := by
  classical
  letI : ∀ s, SFinite (p.pairLaw s) := fun s => by
    letI := hν (p.world s)
    dsimp [pairLaw]
    infer_instance
  let K : ℕ := ⌊p.κ⌋₊
  have hK (s : Fin p.m) (v : PairPoint) (hv : v ∈ p.H s) :
      (p.sourceList s v).card ≤ K := Nat.le_floor (p.sourceList_size s v)
  have hprob (s : Fin p.m) (v : PairPoint) (hv : v ∈ p.H s)
      (s' : Fin p.m) (hs' : s' ∈ p.sourceList s v)
      (hval : (Nk ^ a)⁻¹ ≤
        |MvPolynomial.eval (fun n => p.sourceBase s v n) (disc (p.P s'))|) :
      anchorLaw {θ | ¬ SafeFor ((Nk ^ a) ^ (-(Cs : ℝ))) (disc (p.P s))
        (disc (p.P s')) (p.sourceBase s v) θ.1 θ.2} ≤ ENNReal.ofReal (Nk ^ a)⁻¹ := by
    apply hsafe (Nk ^ a) hA (disc (p.P s)) (disc (p.P s'))
      (p.tests s).2.2.2.1 (p.tests s').2.2.2.1
      (p.tests s).2.2.2.2 (p.tests s').2.2.2.2 (p.sourceBase s v)
      (p.sourceBase_norm s hv) _ hval
    simpa only [Real.rpow_neg hNk.le] using p.source_discriminant s hv
  obtain ⟨θ, hθ, G, hG, hGH, hGs, hm⟩ := exists_list_safe_anchor
    p.pairLaw p.H (fun s => (p.pairs s).1) (p.pairLaw_finite hν)
    (fun s => ENNReal.ofReal (ωk (p.world s) * (2 : ℝ) ^ p.T))
    (fun _ => ENNReal.ofReal_ne_top) (fun s => disc (p.P s))
    p.sourceBase p.measurable_sourceBase p.sourceList p.measurable_sourceList_membership
    K hK ((Nk ^ a) ^ (-(Cs : ℝ))) (Nk ^ a)⁻¹ (ENNReal.ofReal (Nk ^ a)⁻¹) hprob
  refine ⟨θ, hθ, G, hG, hGH, ?_, ?_⟩
  · intro s v hv s' hs' hval
    apply hGs s v hv s' hs'
    simpa only [Real.rpow_neg hNk.le] using hval
  · have hκ : 0 ≤ p.κ := by linarith [p.κ_one]
    have hKe : (K : ℝ≥0∞) ≤ ENNReal.ofReal p.κ := by
      simpa only [ENNReal.ofReal_natCast] using
        ENNReal.ofReal_le_ofReal (Nat.floor_le hκ)
    have he : (K : ℝ≥0∞) * ENNReal.ofReal (Nk ^ a)⁻¹ ≤
        ENNReal.ofReal (p.κ * (Nk ^ a)⁻¹) := by
      rw [ENNReal.ofReal_mul hκ]
      gcongr
    apply hm.trans
    change p.pairMass G + (K : ℝ≥0∞) * ENNReal.ofReal (Nk ^ a)⁻¹ * p.pairMass p.H ≤ _
    gcongr

end PairData
end Submission.Obl.k4_matched_pair_representative_realization.Selection
