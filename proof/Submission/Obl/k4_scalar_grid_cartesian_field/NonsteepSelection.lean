import Submission.Obl.k4_scalar_grid_cartesian_field.GlobalSteepMass

namespace Submission.Obl.k4_scalar_grid_cartesian_field

open Set MeasureTheory Filter MvPolynomial

/-- A subpower transverse cutoff makes the global steep mass smaller than any given
original graph-mass floor. Both retained partial derivatives have one subpower bound. -/
theorem exists_nonsteep_selection (data : Data) (hs : scaleHyp data) (hb : baseHyp data)
    (hcap : capHyp data) (hpacket : packetHyp data) (H : ℕ → ℝ) (hH : subpower data H) :
    ∃ (Q L : ℕ → ℝ), subpower data Q ∧ subpower data L ∧
      (∀ k, 2 * data.K k ≤ L k ∧ 3000 * data.K k ^ 3 ≤ L k) ∧
      ∀ᶠ k in atTop,
        (∀ g : Fin (data.W k), MeasurableSet (steepWorld data k g (Q k))) ∧
        ((∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) *
          data.ρ k g (steepWorld data k g (Q k))) ≤ ENNReal.ofReal (1 / (8 * H k))) ∧
        ∀ (i : Fin (data.n k 1)) (x : Incidence), x.1 ∈ data.A k 1 i →
          x.2 ∈ I data (data.T k 1) (data.j k 1 i) →
          (∀ e, |x.1.2 e| ≤ data.K k) → x ∉ steepWorld data k (data.γ k 1 i) (Q k) →
          ∀ e, |eval ![x.2, scalarY x.1 x.2] (pderiv e (data.F k 1 i))| ≤ L k := by
  have hN : ∀ k, 0 < data.N k := fun k => by linarith [hs.1 k]
  have hN₁ : ∀ k, 1 ≤ data.N k := fun k => by linarith [hs.1 k]
  have hK := hs.2.2.1
  have hS : 0 < data.S := hs.2.2.2.2.2.2.2
  have hκone : data.κ ≤ 1 := hs.2.2.2.2.2.2.1
  have hKH : SubpowerLoss data.N (fun k => data.K k * H k) :=
    Submission.Obl.k4_tempered_grid_selection.subpower_mul hN hK hH
  let P : ℝ → ℕ → Prop := fun b k =>
    (∑ g : Fin (data.W k), ENNReal.ofReal (data.ω k g) *
      data.ρ k g (steepWorld data k g (data.N k ^ (2 * b)))) ≤ ENNReal.ofReal (1 / (8 * H k))
  have hP (b : ℝ) (hbpos : 0 < b) : ∀ᶠ k in atTop, P b k := by
    have hnum := eventually_polynomial_subpower_le hN₁ hs.2.1 hKH
      (by norm_num : (1 : ℝ) ≤ 3200000) 12 (mul_pos hS hbpos)
    filter_upwards [global_steep_mass_bound data hs hb hcap hpacket hbpos, hnum] with k hk hn
    exact hk.trans (ENNReal.ofReal_le_ofReal
      (steep_loss_le_inverse_floor (hN k) (hK.1 k) (hH.1 k) hn))
  obtain ⟨b, hbpos, _, hbsub, hgood⟩ := exists_subpower_accuracy hN₁ P hP
  let Q : ℕ → ℝ := fun k => data.N k ^ (2 * b k)
  let L : ℕ → ℝ := fun k => nonsteepBudget (data.K k) (Q k)
  have hQone (k : ℕ) : 1 ≤ Q k := Real.one_le_rpow (hN₁ k) (by have hbk := hbpos k; positivity)
  have hQsub : subpower data Q := by
    have heq : Q = (fun k => 1 * (data.N k ^ b k) ^ 2) := by
      funext k
      dsimp [Q]
      rw [one_mul, ← Real.rpow_mul_natCast (hN k).le]
      congr 1
      ring
    rw [heq]
    exact Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial
      hN₁ hs.2.1 hbsub le_rfl 2
  have hKQ : SubpowerLoss data.N (fun k => data.K k * Q k) :=
    Submission.Obl.k4_tempered_grid_selection.subpower_mul hN hK hQsub
  have hLsub : subpower data L :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_polynomial hN₁ hs.2.1 hKQ
      (by norm_num : (1 : ℝ) ≤ 10000) 3
  refine ⟨Q, L, hQsub, hLsub, ?_, ?_⟩
  · intro k
    have hbounds := nonsteepBudget_bounds (hK.1 k) (hQone k)
    exact ⟨hbounds.2.1, hbounds.2.2.1⟩
  · filter_upwards [hgood, original_packet_facts_eventually data hs hb hpacket] with k hk hp
    refine ⟨fun g => measurableSet_steepWorld data k hp g (Q k), hk, ?_⟩
    intro i x hxA hxI hxcoeff hxgood e
    have htrans : |eval ![x.2, scalarY x.1 x.2] (pderiv 1 (data.F k 1 i))| ≤ Q k := by
      by_contra hnot
      apply hxgood
      exact ⟨i, rfl, hxA, hxI, hxcoeff, le_of_lt (lt_of_not_ge hnot)⟩
    have hdir := (hp i).directional_bound (hs.1 k) hκone x.1 hxA hxcoeff x.2 hxI
    have hfirst := first_partial_of_directional (by linarith [hK.1 k] : 0 ≤ data.K k)
      hdir (hxcoeff 1) htrans
    have hbounds := nonsteepBudget_bounds (hK.1 k) (hQone k)
    fin_cases e
    · exact hfirst.trans hbounds.2.2.2.2
    · exact htrans.trans hbounds.2.2.2.1

end Submission.Obl.k4_scalar_grid_cartesian_field
