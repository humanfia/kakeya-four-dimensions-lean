import Submission.Obl.k4_matching_gap_regularization.Binning
import Submission.Obl.k4_matching_gap_regularization.Data
import Submission.Obl.k4_matching_gap_regularization.Measurability

set_option autoImplicit false

namespace Submission.Obl.k4_matching_gap_regularization

open MeasureTheory Set
open scoped ENNReal

/-- At a fixed precision, finite power bands regularize one sufficiently
large bad matching. -/
lemma regularize_bad {D J m : ℕ} (hDJ : D ≤ J) (hm : 0 < m)
    {d η N : ℝ} (hN : 1 ≤ N) (hη : η ≤ 1 / (m : ℝ))
    (hsize : 2 * N ^ η ≤ N ^ (1 / (m : ℝ)))
    (hcard : ((2 * m + 1 : ℕ) : ℝ) ^ (J + 1) ≤ N ^ (1 / (m : ℝ)))
    (hbad : Bad D J d η N) :
    ∃ β : ℕ → ℝ, Admissible D J β ∧ Gap J d β (2 / (m : ℝ)) N := by
  classical
  rcases hbad with ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, hbase, hbad⟩
  have hbase_orig := hbase
  obtain ⟨hn₁, hn₂, hf₁, hf₂, hb₁, hb₂, hp₁, hp₂, hs₁, hs₂, hμ, hm₁, hm₂⟩ := hbase
  letI : IsProbabilityMeasure μ := hμ
  let g : Fin (J + 1) → ((Fin n₁ × Fin n₂) × ℝ) → ℝ := fun j p =>
    |localDeriv j.val (f₁ p.1.1) p.2 - localDeriv j.val (f₂ p.1.2) p.2|
  have hg : ∀ j, Measurable (g j) := fun j =>
    measurable_localGap f₁ f₂ hf₁ hf₂ (by omega)
  have hbad_ae : ∀ᵐ p ∂μ, p ∈ BadSet D η N f₁ f₂ := (ae_iff).2 hbad
  have hgap : ∀ᵐ p ∂μ, (∀ j, g j p ≤ N ^ (1 / (m : ℝ))) ∧
      ∃ j : Fin (J + 1), (1 ≤ j.val ∧ j.val ≤ D) ∧ N ^ (-(1 / (m : ℝ))) ≤ g j p := by
    filter_upwards [hbad_ae] with p hp
    refine ⟨?_, ?_⟩
    · intro j
      dsimp [g]
      rw [localDeriv_eq hp.1, localDeriv_eq hp.1]
      calc
        |iteratedDeriv j.val (f₁ p.1.1) p.2 - iteratedDeriv j.val (f₂ p.1.2) p.2| ≤
            |iteratedDeriv j.val (f₁ p.1.1) p.2| + |iteratedDeriv j.val (f₂ p.1.2) p.2| := abs_sub _ _
        _ ≤ N ^ η + N ^ η := add_le_add (hb₁ _ _ (by omega) _ hp.1) (hb₂ _ _ (by omega) _ hp.1)
        _ ≤ N ^ (1 / (m : ℝ)) := by linarith
    · obtain ⟨j, hj₁, hjD, hjgap⟩ := hp.2.2
      refine ⟨⟨j, by omega⟩, ⟨hj₁, hjD⟩, ?_⟩
      dsimp [g]
      rw [localDeriv_eq hp.1, localDeriv_eq hp.1]
      exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans hjgap
  obtain ⟨b, ν, hb, hbzero, hνprob, hνdom, hband⟩ :=
    regularize_gaps μ g hg (fun j => 1 ≤ j.val ∧ j.val ≤ D) hm hN hgap
  let β : ℕ → ℝ := fun j => if hj : j ≤ J then b ⟨j, by omega⟩ else 0
  have hβ : Admissible D J β := by
    constructor
    · intro j hj₁ hjJ
      simpa [β, hjJ] using hb ⟨j, by omega⟩
    · obtain ⟨j, ⟨hj₁, hjD⟩, hjzero⟩ := hbzero
      refine ⟨j.val, hj₁, hjD, ?_⟩
      simpa [β, show j.val ≤ J by omega] using hjzero
  have hC : ((2 * m + 1) ^ (J + 1) : ℝ≥0∞) ≤ ENNReal.ofReal (N ^ (1 / (m : ℝ))) := by
    have hc := ENNReal.ofReal_le_ofReal hcard
    rw [← Nat.cast_pow, ENNReal.ofReal_natCast] at hc
    exact_mod_cast hc
  have hdom : ∀ E : Set ((Fin n₁ × Fin n₂) × ℝ),
      ν E ≤ ENNReal.ofReal (N ^ (1 / (m : ℝ))) * μ E := by
    intro E
    exact (hνdom E).trans (mul_le_mul' (by simpa using hC) le_rfl)
  have hδ : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hδtwo : 1 / (m : ℝ) ≤ 2 / (m : ℝ) := by
    calc
      1 / (m : ℝ) ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := le_add_of_nonneg_right hδ
      _ = 2 / (m : ℝ) := by ring
  have hadd : 1 / (m : ℝ) + η ≤ 2 / (m : ℝ) := by
    calc
      1 / (m : ℝ) + η ≤ 1 / (m : ℝ) + 1 / (m : ℝ) := add_le_add le_rfl hη
      _ = 2 / (m : ℝ) := by ring
  have hbase' : Base J d (2 / (m : ℝ)) N f₁ f₂ π₁ π₂ ν :=
    base_enlarge hN (hη.trans hδtwo) hadd hdom hνprob hbase_orig
  have hbadν : ∀ᵐ p ∂ν, p ∈ BadSet D η N f₁ f₂ :=
    (ae_iff).2 (null_of_bounded hdom hbad)
  have htime : μ {p | p.2 = (1 : ℝ)} = 0 :=
    time_singleton_null μ (fun p => p.1.1) (fun p => p.2)
      (fun i => ENNReal.ofReal (N ^ η * π₁ i)) hm₁ 1
  have hne : ∀ᵐ p ∂ν, p.2 ≠ (1 : ℝ) :=
    (ae_iff).2 (by simpa using null_of_bounded hdom htime)
  refine ⟨β, hβ, n₁, n₂, f₁, f₂, π₁, π₂, ν, hbase', (ae_iff).1 ?_⟩
  filter_upwards [hbadν, hband, hne] with p hp hb' hne'
  refine ⟨⟨hp.1.1, lt_of_le_of_ne hp.1.2 hne'⟩,
    hp.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN (add_le_add le_rfl (hη.trans hδtwo))), ?_⟩
  intro j hj₁ hjJ
  have hbj : Band N (1 / (m : ℝ)) (β j)
      |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2| := by
    simpa [g, β, hjJ, localDeriv_eq hp.1] using hb' ⟨j, by omega⟩
  refine ⟨hbj.1.trans (Real.rpow_le_rpow_of_exponent_le hN (add_le_add le_rfl hδtwo)), ?_⟩
  intro hjcut
  exact (Real.rpow_le_rpow_of_exponent_le hN (sub_le_sub_left hδtwo _)).trans (hbj.2 hjcut)

end Submission.Obl.k4_matching_gap_regularization
