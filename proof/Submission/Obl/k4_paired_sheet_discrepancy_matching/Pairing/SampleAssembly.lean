/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/SampleAssembly.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.SampleAgreement
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.EntryBudget
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Assembly

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MeasureTheory Set Metric

abbrev PairedAt (Nk : ℝ) (Wk : ℕ) (ωk : Fin Wk → ℝ)
    (νk : Fin Wk → Measure (ℕ × (Fin 6 → ℝ)))
    (Ek : Fin Wk → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (Bk : Fin Wk → ℝ)
    (L out h : ℝ) (M D : ℕ) (ε : ℝ) : Prop :=
  PairedSample (fun _ => Nk) (fun _ => Wk) (fun _ => ωk) (fun _ => νk)
    (fun _ => Ek) (fun _ => Bk) L out h M D ε 0

namespace NormalizationStep.TestedSample

variable {cv : Prop} {lam Nk : ℝ} {Wk : ℕ}
  {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
  {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
  {L dc a h : ℝ} {M D : ℕ} {ε : ℝ}
  (s : TestedSample cv lam Nk Wk ωk νk Ek Bk L dc a h M D ε)

def goodSource (out : ℝ) (i : Fin s.m) (v : PairPoint) : Prop :=
  ∃ i' ∈ s.lst (s.γ (s.frame i)) (obs (Bk (s.γ (s.frame i))) (δ Nk L) (v.1, v.2.2)),
    s.frame i' = s.frame i ∧
      localPair Nk out (δ Nk L) ((2 : ℝ) ^ s.T) (s.P i) (s.P i')
        (s.baseAt (s.frame i) v)
        (base s.T (s.j (s.frame i) : ℝ) s.κ (s.c (s.frame i)) (s.u (s.frame i))
          (s.Q (s.frame i)) v.1)
        (fun t => Bk (s.γ (s.frame i)) * (x v.1 t) 3) v.2.1 (s.block (s.frame i))

def badSource (out : ℝ) (i : Fin s.m) : Set PairPoint :=
  FinitePairLaw.row s.H i ∩ {v | ¬ s.goodSource out i v}

def badActive (out : ℝ) : Set s.Active :=
  Subtype.val ⁻¹' {p : Fin s.m × PairPoint | ¬ s.goodSource out p.1 p.2}

theorem weight_normalization (hω : ∀ γ, 0 ≤ ωk γ) (b : Fin s.J) :
    ENNReal.ofReal (s.frameWeight b) * ENNReal.ofReal ((2 : ℝ) ^ s.T) ^ 2 =
      ENNReal.ofReal (ωk (s.γ b) * (2 : ℝ) ^ s.T) := by
  rw [← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (s.frameWeight_nonneg hω b)]
  congr 1
  dsimp [frameWeight]
  field_simp

theorem pairMeasure_univ_eq (hω : ∀ γ, 0 ≤ ωk γ) :
    s.pairMeasure univ = ∑ i, ENNReal.ofReal (ωk (s.γ (s.frame i)) * (2 : ℝ) ^ s.T) *
      ((νk (s.γ (s.frame i))).prod (volume.prod volume)) (FinitePairLaw.row s.H i) := by
  rw [pairMeasure, FinitePairLaw.supportedLaw_univ _ _ _ (fun i j => (s.hH i j).1)]
  apply Finset.sum_congr rfl
  intro i _
  rw [frameLaw, Measure.smul_apply, smul_eq_mul, ← mul_assoc, s.weight_normalization hω]

theorem pairMeasure_bad_eq (hω : ∀ γ, 0 ≤ ωk γ) (out : ℝ) :
    s.pairMeasure (s.badActive out) = ∑ i,
      ENNReal.ofReal (ωk (s.γ (s.frame i)) * (2 : ℝ) ^ s.T) *
        ((νk (s.γ (s.frame i))).prod (volume.prod volume)) (s.badSource out i) := by
  rw [pairMeasure, FinitePairLaw.supportedLaw_apply _ _ _ (fun i j => (s.hH i j).1)]
  apply Finset.sum_congr rfl
  intro i _
  have himage : Subtype.val '' s.badActive out =
      {p : Fin s.m × PairPoint | ¬ s.goodSource out p.1 p.2} ∩ FinitePairLaw.active s.H := by
    rw [badActive, image_preimage_eq_inter_range, Subtype.range_val]
  have hpre : (fun v => (i, v)) ⁻¹' (Subtype.val '' s.badActive out) = s.badSource out i := by
    rw [himage]
    ext v
    simp only [badSource, FinitePairLaw.active, mem_preimage, mem_inter_iff, mem_setOf_eq]
    exact and_comm
  rw [hpre, frameLaw, Measure.smul_apply, smul_eq_mul, ← mul_assoc, s.weight_normalization hω]

/-- The final masks delete the outer-measure bad set from each unchanged
source row. All spatial frames, source predicates and witness lists are kept. -/
theorem pairedAt_of_bad_bound (hcv : cv) (hω : ∀ γ, 0 ≤ ωk γ)
    (hωsum : ∑ γ, ωk γ = 1) (hNk : 1 ≤ Nk) (ha : 0 < a)
    {εout : ℝ} (hεout : ε ≤ εout)
    {out : ℝ} (haout : a ≤ out) (h2out : 2 * a ≤ out)
    (Xbad : ENNReal) (hXbad : Xbad ≠ ⊤)
    (hbad : s.pairMeasure (s.badActive out) ≤ Xbad)
    (hcover : ENNReal.ofReal s.κ⁻¹ + Xbad ≤ s.pairMeasure univ) :
    PairedAt Nk Wk ωk νk Ek Bk L out h M D εout := by
  have hNkpos : 0 < Nk := zero_lt_one.trans_le hNk
  apply pairedSample_of_entries s.κ s.κ_one
    (s.κ_le.trans (Real.rpow_le_rpow_of_exponent_le hNk hεout)) s.T
    (s.hT.trans (Real.rpow_le_rpow_of_exponent_le hNk (by linarith : h + ε ≤ h + εout)))
    (Fr := Fin s.J) (En := Fin s.m)
    (by simpa only [Fintype.card_fin] using s.hJ)
    (by simpa only [Fintype.card_fin] using s.hm)
    s.γ s.j s.c s.u s.Q s.hframe s.frame s.P _ s.S s.hS s.hdisj
    s.lst s.hlst s.hlstfmt (FinitePairLaw.row s.H) _ s.β _ _ Xbad hXbad _ _
  · intro i
    have hP := s.hP i
    have hcvP := hP.2.2 hcv
    exact ⟨hP.1, hP.2.1, hcvP.1, hcvP.2.1,
      fun d => (hcvP.2.2 d).trans (Real.rpow_le_rpow_of_exponent_le hNk haout)⟩
  · intro i
    refine ⟨FinitePairLaw.measurableSet_row s.H (fun i j => (s.hH i j).1) i, ?_⟩
    intro v hv
    obtain ⟨j, hj⟩ := mem_iUnion.mp hv
    have hs := (s.hH i j).2 v hj
    exact ⟨hs.1, hs.2.1, hs.2.2.1⟩
  · intro i
    exact ⟨(s.hβ i).1, fun U hU => s.frameLaw_row_density i U hU⟩
  · exact (s.beta_budget hω hωsum hNkpos).trans (Real.rpow_le_rpow_of_exponent_le hNk h2out)
  · exact (s.pairMeasure_bad_eq hω out) ▸ hbad
  · exact (s.pairMeasure_univ_eq hω) ▸ hcover

end NormalizationStep.TestedSample

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
