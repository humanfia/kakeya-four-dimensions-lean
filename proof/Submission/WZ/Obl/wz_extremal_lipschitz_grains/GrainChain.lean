-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainChain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.GrainFine
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TwoScaleBridge

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **Cube bounds at finitely many scales**: refinements of an extremal family whose fine set has
the two-scale cube bound at each requested scale `t i`, `i < K`. -/
theorem cube_bounds_chain {σ : ℝ} (hTS : TwoScaleTheoremP σ) (K : ℕ) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
      ∃ η d1 : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Family η δ n x v Y → Separated η δ n x v →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
        ∀ t : ℕ → ℝ, (∀ i < K, δ ^ (1 - ε) ≤ t i ∧ t i ≤ δ ^ (2 * ε)) →
        ∃ Y' : Fin n → Set Space, (∀ i, Y' i ⊆ Y i) ∧ Family ε δ n x v Y' ∧
          ∀ i < K, ∃ τc : ℝ, t i ≤ τc ∧ τc ≤ δ ^ (-ε) * t i ∧
            ∀ c : Space, ∀ r : ℝ, τc ≤ r →
              volume ((⋃ j, Y' j) ∩ closedBall c r) ≤
                ENNReal.ofReal (54880000 * (r / τc) ^ 4 * τc ^ (3 - σ - ε) * δ ^ (σ - 2 * ε)) := by
  induction K with
  | zero =>
    intro ε hε _
    refine ⟨ε, 1, hε, le_rfl, one_pos, ?_⟩
    intro δ _ _ _ n x v Y hF _ _ t _
    exact ⟨Y, fun i => subset_rfl, hF, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ K ih =>
    intro ε hε hε10
    obtain ⟨η1, dA, hη1, hdA, hA⟩ := hTS ε hε
    set ε' := min ε η1 with hε'
    have hε'0 : 0 < ε' := lt_min hε hη1
    obtain ⟨η, d2, hη, hηε', hd2, hprev⟩ := ih ε' hε'0 ((min_le_left _ _).trans hε10)
    obtain ⟨d3, hd3, hcut⟩ := exists_power_cutoff hε (by norm_num : (0:ℝ) < 1 / 4)
    refine ⟨η, min (min dA d2) d3, hη, hηε'.trans (min_le_left _ _),
      lt_min (lt_min hdA hd2) hd3, ?_⟩
    intro δ hδ hδd' hδ100 n x v Y hF hS hV t ht
    have hδd : δ ≤ min dA d2 := hδd'.trans (min_le_left _ _)
    have hδ3 : δ ≤ d3 := hδd'.trans (min_le_right _ _)
    have hδ1 : δ ≤ 1 := by linarith
    have hε'ε : ε' ≤ ε := min_le_left _ _
    have hε'η : ε' ≤ η1 := min_le_right _ _
    obtain ⟨Y1, hY1Y, hF1, hb1⟩ := hprev δ hδ (hδd.trans (min_le_right _ _)) hδ100 n x v Y
      hF hS hV t (fun i hi => by
        obtain ⟨h1, h2⟩ := ht i (by omega)
        exact ⟨(Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans h1,
          h2.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))⟩)
    have hsub1 : (⋃ i, Y1 i) ⊆ ⋃ i, Y i := iUnion_mono hY1Y
    -- the new scale `t K`
    obtain ⟨htK1, htK2⟩ := ht K (Nat.lt_succ_self K)
    have hη' : η ≤ η1 := hηε'.trans hε'η
    obtain ⟨τc, hτ1, hτ2, hTSA⟩ := hA δ hδ (hδd.trans (min_le_left _ _)) hδ100 n x v Y1
      (hF1.mono_error hδ hδ1 hε'η) (hS.mono_error hδ hδ1 hη')
      ((measure_mono hsub1).trans (hV.trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))))) (t K) htK1
      (htK2.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))
    have hτ0 : 0 < τc := (Real.rpow_pos_of_pos hδ _).trans_le (htK1.trans hτ1)
    have hδτ : δ ≤ τc := by
      have : δ ≤ δ ^ (1 - ε) := by
        calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
          _ ≤ δ ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
      exact this.trans (htK1.trans hτ1)
    have hτ4 : τc ≤ 1 / 4 := by
      have h1 : τc ≤ δ ^ (-ε) * δ ^ (2 * ε) := hτ2.trans (mul_le_mul_of_nonneg_left htK2
        (Real.rpow_nonneg hδ.le _))
      rw [← Real.rpow_add hδ, show -ε + 2 * ε = ε by ring] at h1
      exact h1.trans (hcut δ hδ hδ3)
    obtain ⟨Y2, hY2Y1, hY2m, hY2mass, -, hcube⟩ := volume_ball_le_of_twoScale hδ hδτ hτ4 hF.1
      hF.2.1 (fun i => (hY1Y i).trans (hF.2.2.2.2.2.1 i)) hTSA
    have hsub2 : (⋃ i, Y2 i) ⊆ ⋃ i, Y1 i := iUnion_mono hY2Y1
    refine ⟨Y2, fun i => (hY2Y1 i).trans (hY1Y i), ?_, ?_⟩
    · refine ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, hY2m,
        fun i => (hY2Y1 i).trans ((hY1Y i).trans (hF.2.2.2.2.2.1 i)), ?_⟩
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hY2mass
      have : δ ^ ε ≤ δ ^ ε' := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hε'ε
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      gcongr
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
      · obtain ⟨τ', h1, h2, h3⟩ := hb1 i hlt
        refine ⟨τ', h1, h2.trans ?_, fun c r hr => (measure_mono
          (inter_subset_inter_left _ hsub2)).trans ((h3 c r hr).trans ?_)⟩
        · apply mul_le_mul_of_nonneg_right _ ((Real.rpow_nonneg hδ.le _).trans
            (ht i (by omega)).1)
          exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
        · have hτ'0 : 0 < τ' := (Real.rpow_pos_of_pos hδ _).trans_le
            ((ht i (by omega)).1.trans h1)
          have hτ'1 : τ' ≤ 1 := by
            have := h2.trans (mul_le_mul_of_nonneg_left (ht i (by omega)).2
              (Real.rpow_nonneg hδ.le _))
            rw [← Real.rpow_add hδ] at this
            exact this.trans (Real.rpow_le_one hδ.le hδ1 (by linarith))
          apply ENNReal.ofReal_le_ofReal
          have e1 : τ' ^ (3 - σ - ε') ≤ τ' ^ (3 - σ - ε) :=
            Real.rpow_le_rpow_of_exponent_ge hτ'0 hτ'1 (by linarith)
          have e2 : δ ^ (σ - 2 * ε') ≤ δ ^ (σ - 2 * ε) :=
            Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
          have p1 : 0 ≤ 54880000 * (r / τ') ^ 4 := by positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left e1 p1) e2 (Real.rpow_nonneg hδ.le _)
            (mul_nonneg p1 (Real.rpow_nonneg hτ'0.le _))
      · subst heq
        refine ⟨τc, hτ1, hτ2.trans ?_, fun c r hr => (measure_mono
          (inter_subset_inter_left _ subset_rfl)).trans ((hcube c r hr).trans ?_)⟩
        · exact mul_le_mul_of_nonneg_right le_rfl ((Real.rpow_nonneg hδ.le _).trans htK1)
        · apply ENNReal.ofReal_le_ofReal
          have hτ1' : τc ≤ 1 := by linarith
          have e1 : τc ^ (3 - σ - ε) ≤ τc ^ (3 - σ - ε) := le_rfl
          exact le_rfl

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
