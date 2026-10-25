import Submission.Obl.k4_matching_homogeneous_records.Input
import Submission.Obl.k4_matching_homogeneous_records.Offsets

namespace Submission.Obl.k4_matching_homogeneous_records

open Set MeasureTheory

lemma rawRecords_of_gap {D J q : ℕ} {d N η ε : ℝ} {β : ℕ → ℝ}
    (hD : 1 ≤ D) (hDJ : D ≤ J)
    (hz : ∃ i, 1 ≤ i ∧ i ≤ D ∧ β i = 0)
    (hN : 1 ≤ N) (hq : 1 ≤ q) (hη : 0 ≤ η) (hηε : η ≤ ε)
    (hbudget : (2 * ((4 * (J + 2) + 5 : ℕ) : ℝ) ^ ((q + 1) * (J + 1))) *
        N ^ (d + radius J β 1 + (((q + 1) * (J + 1) + 1 : ℕ) : ℝ) * η) ≤
      N ^ (d + radius J β 1 + ε))
    (hgap : Gap J d β η N) : RawRecords J d β q ε N := by
  classical
  rcases hgap with ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, hn₁, hn₂, hf₁, hf₂, hder₁, hder₂,
    hπ₁, hπ₂, hsum₁, hsum₂, hprob, hmarg₁, hmarg₂, hgood⟩
  obtain ⟨T, hT, hTm, hTzero⟩ := exists_measurable_superset_of_null hgood
  let S := Tᶜ
  have hSgood := compl_subset_compl.mpr hT
  simp only [compl_compl] at hSgood
  have hStime : ∀ p ∈ S, p.2 ∈ Ico (0 : ℝ) 1 := fun p hp => (hSgood hp).1
  have hSzero : μ Sᶜ = 0 := by simpa only [S, compl_compl] using hTzero
  let h : ℕ → ℕ := fun k => dyadicHeight N (radius J β ((k : ℝ) / (q : ℝ)))
  let w : ℕ → ℕ → ℝ := fun k j => N ^ accuracy J β j ((k : ℝ) / (q : ℝ))
  let F := recordCode q J f₁ f₂ h w
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNp : 0 < N := by linarith
  have hmono (a b : ℕ) (hab : a ≤ b) (hb : b ≤ q) : h a ≤ h b := by
    apply dyadicHeight_mono hN
    apply radius_mono (hD.trans hDJ)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) hqR.le
  have hbounds (k : ℕ) (hk : k ≤ q) :
      N ^ radius J β ((k : ℝ) / q) ≤ (2 : ℝ) ^ h k ∧
      (2 : ℝ) ^ h k ≤ 2 * N ^ radius J β ((k : ℝ) / q) :=
    dyadicHeight_bounds hN (radius_nonneg hDJ hz (by positivity))
  have hoff (p) (hp : p ∈ S) (v) (hv : v ≤ q) (j) (hj : j ≤ J) :
      jetOffset f₁ f₂ h w v j p ∈ Finset.Icc (-(offsetCutoff J N η : ℤ)) (offsetCutoff J N η : ℤ) := by
    apply gap_jetOffset_mem hDJ hz hN hq f₁ f₂ hf₁ hf₂ hder₁ hder₂ p
      ⟨(hSgood hp).1, (hSgood hp).2.1, fun i hi hiJ => ((hSgood hp).2.2 i hi hiJ).1⟩ v j hv hj
  have hcount := recordCode_count q J (offsetCutoff J N η) f₁ f₂ h w S hStime
    (fun v hv => hmono v q hv le_rfl) hoff
  have hcountR : ((F q '' S).ncard : ℝ) ≤
      (n₁ : ℝ) * (2 : ℝ) ^ h q * ((2 * offsetCutoff J N η + 1 : ℕ) : ℝ) ^ ((q + 1) * (J + 1)) := by
    exact_mod_cast hcount.2
  have hhq : (2 : ℝ) ^ h q ≤ 2 * N ^ radius J β 1 := by
    simpa only [div_self (ne_of_gt hqR)] using (hbounds q le_rfl).2
  have hcount' : ((F q '' S).ncard : ℝ) ≤ N ^ (d + radius J β 1 + ε) := by
    calc
      _ ≤ (n₁ : ℝ) * (2 : ℝ) ^ h q * ((2 * offsetCutoff J N η + 1 : ℕ) : ℝ) ^ ((q + 1) * (J + 1)) := hcountR
      _ ≤ N ^ (d + η) * (2 * N ^ radius J β 1) *
          (((4 * (J + 2) + 5 : ℕ) : ℝ) * N ^ η) ^ ((q + 1) * (J + 1)) := by
        gcongr
        exact offsetCutoff_bound hN hη
      _ = (2 * ((4 * (J + 2) + 5 : ℕ) : ℝ) ^ ((q + 1) * (J + 1))) *
          N ^ (d + radius J β 1 + (((q + 1) * (J + 1) + 1 : ℕ) : ℝ) * η) := by
        rw [mul_pow]
        calc
          _ = (2 * ((4 * (J + 2) + 5 : ℕ) : ℝ) ^ ((q + 1) * (J + 1))) *
              (N ^ (d + η) * N ^ radius J β 1 * (N ^ η) ^ ((q + 1) * (J + 1))) := by ring
          _ = _ := by
            rw [← Real.rpow_mul_natCast hNp.le, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
            congr 2
            push_cast
            ring
      _ ≤ _ := hbudget
  refine ⟨n₁, n₂, f₁, f₂, π₁, π₂, μ, h, F, S, ?_⟩
  refine ⟨hn₁.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    hn₂.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), hf₁, hf₂, ?_, ?_,
    hπ₁, hπ₂, hsum₁, hsum₂, hprob, ?_, ?_, hTm.compl, hSzero, ?_, hmono, hbounds,
    ?_, ?_, hcount'⟩
  · intro i j hj t ht
    exact (hder₁ i j hj t ht).trans (Real.rpow_le_rpow_of_exponent_le hN hηε)
  · intro i j hj t ht
    exact (hder₂ i j hj t ht).trans (Real.rpow_le_rpow_of_exponent_le hN hηε)
  · intro i E hE
    apply (hmarg₁ i E hE).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN hηε) (hπ₁ i)
  · intro i E hE
    apply (hmarg₂ i E hE).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN hηε) (hπ₂ i)
  · intro p hp
    have hp' := hSgood hp
    refine ⟨hp'.1, hp'.2.1.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), ?_⟩
    intro j hj hjJ
    refine ⟨(hp'.2.2 j hj hjJ).1.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)), ?_⟩
    intro hjβ
    exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith)).trans ((hp'.2.2 j hj hjJ).2 hjβ)
  · intro k hk
    exact ⟨measurable_recordCode q J f₁ f₂ h w k, hcount.1 k hk⟩
  · intro k hk x hx y hy
    exact recordCode_eq_iff q J f₁ f₂ h w hk x y

end Submission.Obl.k4_matching_homogeneous_records
