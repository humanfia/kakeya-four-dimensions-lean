import Submission.Obl.k4_row_parent_contact_candidates.RowContact

/-! Either a power-small row skew gives a strip candidate, or the inverse skew
can be included in a subpower budget on the original sequence. -/

namespace Submission.Obl.k4_row_parent_contact_candidates

open scoped Submission.Obl.k4_row_parent_contact_candidates.ZoomInput

open MeasureTheory Set Filter
open PreparedModel

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- A power-small skew leaves positive room for a deeper strip candidate. -/
theorem result_of_power_small_skew {p : Parameters} (hp : p.Valid)
    {a : PreparedModel α} (ha : a.Valid p) {r e c : ℝ}
    (hr : 0 < r) (hrU : r < p.U) (he : 0 < e) (hc : 0 < c)
    (M : ℕ → ℝ) (hM1 : ∀ k, 1 ≤ M k) (hM : Subpower p.N M)
    (hfreq : ∃ᶠ k in atTop,
      ∃ RP : RowParent p a k r (M k * p.N k ^ (-e)) (M k),
        |RP.lam| ≤ M k * p.N k ^ (-c)) : a.Result p := by
  have hℓ : 0 < p.ell := hp.2.2.2.2.2.2.2.1
  have hκ : 0 < p.kappa := hp.2.2.2.2.2.1
  let t : ℝ := min ((p.U - r) / 3) (min c e / (p.ell + 1))
  have ht : 0 < t := lt_min (by linarith) (div_pos (lt_min hc he) (by linarith))
  have htU : t ≤ (p.U - r) / 3 := min_le_left _ _
  have hte : (p.ell + 1) * t ≤ min c e := by
    have ht' : t ≤ min c e / (p.ell + 1) := min_le_right _ _
    have h := (le_div_iff₀ (by linarith : 0 < p.ell + 1)).mp ht'
    nlinarith
  apply result_of_rowParents_gap hp ha (s := r + t) (v := t) (e₀ := e) (c := c)
    hr (by linarith) ht (by linarith)
    (by nlinarith [min_le_left c e, mul_pos hκ ht])
    (by nlinarith [min_le_right c e]) M
    (fun k => zero_lt_one.trans_le (hM1 k)) hM hfreq

/-- In the absence of candidates, choose frequent row parents whose nonzero
skew and inverse skew are controlled by one enlarged subpower constant. -/
theorem nondegenerate_rowParents_of_not_result {p : Parameters} (hp : p.Valid)
    {a : PreparedModel α} (ha : a.Valid p) (hnot : ¬ a.Result p) {r e : ℝ}
    (hr : 0 < r) (hrU : r < p.U) (he : 0 < e)
    (M : ℕ → ℝ) (hM1 : ∀ k, 1 ≤ M k) (hM : Subpower p.N M)
    (hfreq : ∃ᶠ k in atTop,
      Nonempty (RowParent p a k r (M k * p.N k ^ (-e)) (M k))) :
    ∃ M' : ℕ → ℝ, (∀ k, 1 ≤ M' k) ∧ Subpower p.N M' ∧
      ∃ᶠ k in atTop,
        ∃ RP : RowParent p a k r (M' k * p.N k ^ (-e)) (M' k),
          RP.lam ≠ 0 ∧ |RP.lam⁻¹| ≤ M' k := by
  classical
  have hsmall (c : ℝ) (hc : 0 < c) : ∀ᶠ k in atTop,
      ∀ RP : RowParent p a k r (M k * p.N k ^ (-e)) (M k),
        p.N k ^ (-c) < |RP.lam| := by
    by_contra h
    have hbad : ∃ᶠ k in atTop,
        ∃ RP : RowParent p a k r (M k * p.N k ^ (-e)) (M k),
          |RP.lam| ≤ p.N k ^ (-c) := by
      simpa only [Filter.not_eventually, not_forall, not_lt] using h
    apply hnot
    apply result_of_power_small_skew hp ha hr hrU he hc M hM1 hM
    refine hbad.mono ?_
    rintro k ⟨RP, hRP⟩
    exact ⟨RP, hRP.trans
      (le_mul_of_one_le_left (Real.rpow_nonneg (hp.N_pos k).le _) (hM1 k))⟩
  let extra : ℕ → ℝ := fun k =>
    if h : Nonempty (RowParent p a k r (M k * p.N k ^ (-e)) (M k)) then
      max 1 |(Classical.choice h).lam⁻¹| else 1
  have hextra1 : ∀ k, 1 ≤ extra k := by
    intro k
    dsimp only [extra]
    split_ifs
    · exact le_max_left _ _
    · rfl
  have hextrasub : Subpower p.N extra := by
    intro ε hε
    filter_upwards [hsmall ε hε] with k hk
    have hNε : 1 ≤ p.N k ^ ε := Real.one_le_rpow (by linarith [hp.1 k]) hε.le
    dsimp only [extra]
    split_ifs with h
    · apply max_le hNε
      rw [abs_inv]
      have hInv := inv_anti₀ (Real.rpow_pos_of_pos (hp.N_pos k) (-ε))
        (hk (Classical.choice h)).le
      simpa only [Real.rpow_neg (hp.N_pos k).le, inv_inv] using hInv
    · exact hNε
  let M' : ℕ → ℝ := fun k => M k + extra k
  have hMM' : ∀ k, M k ≤ M' k := fun k =>
    le_add_of_nonneg_right (zero_le_one.trans (hextra1 k))
  have hM'1 : ∀ k, 1 ≤ M' k := fun k => (hM1 k).trans (hMM' k)
  have hM'sub : Subpower p.N M' := Subpower.add hp.N_pos hp.2.1 hM hextrasub
  refine ⟨M', hM'1, hM'sub, ?_⟩
  refine (hfreq.and_eventually (hsmall 1 one_pos)).mono ?_
  rintro k ⟨h, hk⟩
  let RP := Classical.choice h
  have hM0 : 0 < M k := zero_lt_one.trans_le (hM1 k)
  have hE : M k * p.N k ^ (-e) ≤ M' k * p.N k ^ (-e) :=
    mul_le_mul_of_nonneg_right (hMM' k) (Real.rpow_nonneg (hp.N_pos k).le _)
  refine ⟨RP.mono hE hM0 (hMM' k), ?_, ?_⟩
  · change RP.lam ≠ 0
    exact abs_pos.mp ((Real.rpow_pos_of_pos (hp.N_pos k) (-1)).trans (hk RP))
  · change |RP.lam⁻¹| ≤ M' k
    have hle : |RP.lam⁻¹| ≤ extra k := by
      dsimp only [extra]
      rw [dif_pos h]
      exact le_max_right _ _
    exact hle.trans (le_add_of_nonneg_left (zero_le_one.trans (hM1 k)))

end

end Submission.Obl.k4_row_parent_contact_candidates
