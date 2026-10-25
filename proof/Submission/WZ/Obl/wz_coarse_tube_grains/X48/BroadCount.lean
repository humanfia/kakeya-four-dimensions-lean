-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.X48.BroadCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.X48.Defs
import Submission.WZ.Obl.wz_transverse_brush_selection.Geometry
import Submission.WZ.Obl.wz_separated_cover_refinement.Arithmetic

noncomputable section

namespace WangZahlLot.Obl.wz_coarse_tube_grains.X48

open Set MeasureTheory

/-- If every shaded point has a transverse partner, the density of the
shadings forces a lower bound on the number of tubes. -/
theorem card_lower_of_transverse_cover {δ b lam : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} {S : Finset (Fin n)}
    (hδ : 0 < δ) (hb : 0 < b) (hb1 : b ≤ 1) (_hlam : 0 ≤ lam)
    (hS : S.Nonempty) (hv : ∀ i ∈ S, ‖v i‖ = 1)
    (hY : ∀ i ∈ S, Y i ⊆ T δ (x i) (v i))
    (hmass : O (lam * S.card * δ ^ 2) ≤ ∑ i ∈ S, μ (Y i))
    (hcover : ∀ j ∈ S, ∀ p ∈ Y j, ∃ i ∈ S, p ∈ Y i ∧
      b ≤ min ‖v i - v j‖ ‖v i + v j‖) :
    lam * b ≤ 4096 * S.card * δ := by
  classical
  have hvol : ∀ j ∈ S, μ (Y j) ≤ (S.card : ENNReal) * O (4096 * δ ^ 3 / b) := by
    intro j hj
    let W : Fin n → Set V := fun i =>
      if b ≤ min ‖v i - v j‖ ‖v i + v j‖ then
        T δ (x i) (v i) ∩ T δ (x j) (v j) else ∅
    have hsub : Y j ⊆ ⋃ i ∈ S, W i := by
      intro p hp
      obtain ⟨i, hi, hpi, hsep⟩ := hcover j hj p hp
      exact Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem hi
        (by simpa only [W, ite_eq_left hsep, Set.mem_inter_iff] using
          And.intro (hY i hi hpi) (hY j hj hp)))
    calc
      μ (Y j) ≤ μ (⋃ i ∈ S, W i) := measure_mono hsub
      _ ≤ ∑ i ∈ S, μ (W i) := measure_biUnion_finset_le S W
      _ ≤ ∑ _i ∈ S, O (4096 * δ ^ 3 / b) := by
        apply Finset.sum_le_sum
        intro i hi
        dsimp only [W]
        split_ifs with hs
        · exact WangZahlLot.Obl.wz_transverse_brush_selection.transverse_intersection_volume
            hδ hb hb1 (hv i hi) (hv j hj) hs
        · simp only [measure_empty]; exact bot_le
      _ = _ := by simp [nsmul_eq_mul]
  have ht := hmass.trans (Finset.sum_le_sum hvol)
  have he : (∑ _i ∈ S, (S.card : ENNReal) * O (4096 * δ ^ 3 / b)) =
      O ((S.card : ℝ) * (S.card * (4096 * δ ^ 3 / b))) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg S.card)]
  rw [he] at ht
  have htr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp ht
  have hs : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS.card_pos
  apply (mul_le_mul_iff_right₀ (mul_pos hs (sq_pos_of_pos hδ))).mp
  calc
    ((S.card : ℝ) * δ ^ 2) * (lam * b) = (lam * S.card * δ ^ 2) * b := by ring
    _ ≤ ((S.card : ℝ) * (S.card * (4096 * δ ^ 3 / b))) * b :=
      mul_le_mul_of_nonneg_right htr hb.le
    _ = ((S.card : ℝ) * δ ^ 2) * (4096 * S.card * δ) := by
      field_simp [ne_of_gt hb]

/-- A strict angular nonconcentration bound supplies the transverse partner
required by the preceding geometric count. -/
theorem card_lower_of_broad {δ b lam t : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} {S : Finset (Fin n)}
    (hδ : 0 < δ) (hb : 0 < b) (hb1 : b ≤ 1) (hlam : 0 ≤ lam)
    (ht : t < 1) (hS : S.Nonempty) (hv : ∀ i ∈ S, ‖v i‖ = 1)
    (hY : ∀ i ∈ S, Y i ⊆ T δ (x i) (v i))
    (hmass : O (lam * S.card * δ ^ 2) ≤ ∑ i ∈ S, μ (Y i))
    (hbr : ∀ p u, ‖u‖ = 1 →
      q n {i | i ∈ S ∧ p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ b} ≤
        t * q n {i | i ∈ S ∧ p ∈ Y i}) :
    lam * b ≤ 4096 * S.card * δ := by
  classical
  apply card_lower_of_transverse_cover hδ hb hb1 hlam hS hv hY hmass
  intro j hj p hp
  by_contra hn
  have hnear : {i | i ∈ S ∧ p ∈ Y i ∧ min ‖v i - v j‖ ‖v i + v j‖ ≤ b} =
      {i | i ∈ S ∧ p ∈ Y i} := by
    ext i
    constructor
    · exact fun hi => ⟨hi.1, hi.2.1⟩
    · intro hi
      refine ⟨hi.1, hi.2, le_of_lt (lt_of_not_ge ?_)⟩
      intro he
      exact hn ⟨i, hi.1, hi.2, he⟩
  have hc : 0 < q n {i | i ∈ S ∧ p ∈ Y i} := by
    change 0 < (({i : Fin n | i ∈ S ∧ p ∈ Y i} : Set (Fin n)).ncard : ℝ)
    apply Nat.cast_pos.mpr
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨j, hj, hp⟩
  have hh := hbr p (v j) (hv j hj)
  rw [hnear] at hh
  nlinarith

/-- Power-law angular broadness, together with average shading density,
forces at least a power-loss multiple of `ρ / δ` tubes. -/
theorem card_lower_power_broad {δ ρ β η : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} {S : Finset (Fin n)}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hβ : 0 < β) (hη : 0 < η) (hS : S.Nonempty)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hY : ∀ i ∈ S, Y i ⊆ T δ (x i) (v i))
    (hmass : O (δ ^ η * S.card * δ ^ 2) ≤ ∑ i ∈ S, μ (Y i))
    (hbr : ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-η) * (r / ρ) ^ β * q n {i | i ∈ S ∧ p ∈ Y i}) :
    δ ^ (η + 2 * η / β) * ρ ≤ 4096 * S.card * δ := by
  let b := ρ * δ ^ (2 * η / β)
  have ha : 0 < 2 * η / β := by positivity
  have hb : 0 < b := mul_pos hρ (Real.rpow_pos_of_pos hδ _)
  have hpow1 : δ ^ (2 * η / β) ≤ 1 :=
    Real.rpow_le_one hδ.le hδ1.le ha.le
  have hbρ : b ≤ ρ := by dsimp [b]; nlinarith
  have hb1 : b ≤ 1 := hbρ.trans hρ1
  have hdη : δ ^ η < 1 := Real.rpow_lt_one hδ.le hδ1 hη
  have he : δ ^ (η + 2 * η / β) * ρ = δ ^ η * b := by
    rw [Real.rpow_add hδ]
    dsimp [b]
    ring
  rw [he]
  by_cases hδb : δ ≤ b
  · apply card_lower_of_broad hδ hb hb1 (Real.rpow_nonneg hδ.le _) hdη hS hv hY hmass
    intro p u hu
    have hc : δ ^ (-η) * (b / ρ) ^ β = δ ^ η := by
      have he' : b / ρ = δ ^ (2 * η / β) := by
        dsimp [b]
        field_simp [ne_of_gt hρ]
      rw [he', ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
      congr 1
      field_simp [ne_of_gt hβ]
      ring
    simpa only [hc] using hbr p u b hu hδb hbρ
  · have hbδ : b ≤ δ := (lt_of_not_ge hδb).le
    have hs : (1 : ℝ) ≤ S.card := by exact_mod_cast Nat.succ_le_of_lt hS.card_pos
    calc
      δ ^ η * b ≤ b := by nlinarith [Real.rpow_pos_of_pos hδ η]
      _ ≤ δ := hbδ
      _ ≤ 4096 * S.card * δ := by nlinarith

/-- Absorbing the fixed transverse-intersection constant gives the cardinal
bound used before choosing a grain length. -/
theorem card_lower_power_broad_budget {δ ρ β η ε : ℝ} {n : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} {S : Finset (Fin n)}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hβ : 0 < β) (hη : 0 < η) (hS : S.Nonempty)
    (hbudget : η + 2 * η / β ≤ ε / 2)
    (hsmall : 16384 * δ ^ (ε / 2) ≤ 1)
    (hv : ∀ i ∈ S, ‖v i‖ = 1) (hY : ∀ i ∈ S, Y i ⊆ T δ (x i) (v i))
    (hmass : O (δ ^ η * S.card * δ ^ 2) ≤ ∑ i ∈ S, μ (Y i))
    (hbr : ∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
      q n {i | i ∈ S ∧ p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
        δ ^ (-η) * (r / ρ) ^ β * q n {i | i ∈ S ∧ p ∈ Y i}) :
    4 * δ ^ ε * (ρ / δ) ≤ S.card := by
  have hc := card_lower_power_broad hδ hδ1 hρ hρ1 hβ hη hS hv hY hmass hbr
  have he : δ ^ ε = δ ^ (η + 2 * η / β) * δ ^ (ε - (η + 2 * η / β)) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hr : δ ^ (ε - (η + 2 * η / β)) ≤ δ ^ (ε / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1.le (by linarith)
  have hd : 16384 * δ ^ ε ≤ δ ^ (η + 2 * η / β) := by
    rw [he]
    nlinarith [Real.rpow_pos_of_pos hδ (η + 2 * η / β)]
  have hg : 16384 * δ ^ ε * ρ ≤ 4096 * S.card * δ :=
    (mul_le_mul_of_nonneg_right hd hρ.le).trans hc
  calc
    4 * δ ^ ε * (ρ / δ) = (4 * δ ^ ε * ρ) / δ := by ring
    _ ≤ S.card := (div_le_iff₀ hδ).mpr (by nlinarith)

/-- The constants in the cardinal part of the one-coarse-tube grains lemma
can be chosen before the scale and tube family. -/
theorem exists_broad_card_parameters (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ η d₀ : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ ρ : ℝ, 0 < δ → δ ≤ d₀ → δ ≤ ρ → ρ ≤ 1 →
      ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V) (S : Finset (Fin n)),
        S.Nonempty → (∀ i ∈ S, ‖v i‖ = 1) →
        (∀ i ∈ S, Y i ⊆ T δ (x i) (v i)) →
        O (δ ^ η * S.card * δ ^ 2) ≤ ∑ i ∈ S, μ (Y i) →
        (∀ p u r, ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
          q n {i | i ∈ S ∧ p ∈ Y i ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
            δ ^ (-η) * (r / ρ) ^ β * q n {i | i ∈ S ∧ p ∈ Y i}) →
        4 * δ ^ ε * (ρ / δ) ≤ S.card := by
  let η := ε * β / (4 * (β + 2))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η ≤ ε := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_pos hε hβ]
  have hbudget : η + 2 * η / β ≤ ε / 2 := by
    have he : η + 2 * η / β = ε / 4 := by
      dsimp [η]
      field_simp
    rw [he]
    linarith
  obtain ⟨d, hd, hcut⟩ :=
    WangZahlLot.Obl.wz_separated_cover_refinement.exists_rpow_cutoff
      (show 0 < ε / 2 by positivity) (show (0 : ℝ) < 1 / 16384 by norm_num)
  refine ⟨η, min d (1 / 100), hη, hηε, lt_min hd (by norm_num), min_le_right _ _, ?_⟩
  intro δ ρ hδ hδd hδρ hρ1 n x v Y S hS hv hY hmass hbr
  have hδ1 : δ < 1 := lt_of_le_of_lt (hδd.trans (min_le_right _ _)) (by norm_num)
  have hsmall : 16384 * δ ^ (ε / 2) ≤ 1 := by
    have hc := hcut δ hδ (hδd.trans (min_le_left _ _))
    linarith
  exact card_lower_power_broad_budget hδ hδ1 (hδ.trans_le hδρ) hρ1 hβ hη hS
    hbudget hsmall hv hY hmass hbr

end WangZahlLot.Obl.wz_coarse_tube_grains.X48
