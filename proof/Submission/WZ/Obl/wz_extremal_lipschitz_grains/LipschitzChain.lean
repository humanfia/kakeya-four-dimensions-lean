-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.LipschitzChain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.LipschitzStep
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.CoarsePlaneMap
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TopScale
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.WeakPlaneExamples
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.ParityCubes

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- The count in `lipschitz_step` in closed form: when `δ ≤ ρc`, `2 ρc ≤ ρ0 ≤ 1`, `1 ≤ Bf` and
`0 < Cc`, the retained mass fraction is at least `(A / (Bf Cc))² ρ0³ / 2⁴⁰`. -/
theorem lipschitz_step_count_le {δ ρ0 ρc A Bf Cc : ℝ} (hδ : 0 < δ) (hδρc : δ ≤ ρc)
    (hρ0 : 2 * ρc ≤ ρ0) (hρ01 : ρ0 ≤ 1) (hBf1 : 1 ≤ Bf) (hCc : 0 < Cc) :
    (A / (Bf * Cc)) ^ 2 * ρ0 ^ 3 / 2 ^ 40 *
      ((8 * ((8 * ⌊Cc⌋₊) ^ 2 * (2 * (⌊2 * (4 * (δ + ρc / 2) / ((ρ0 - 2 * (ρc / 2)) / 2)) /
          ρc⌋₊ + 3) ^ 3)) : ℕ) : ℝ) ≤ A ^ 2 / (2 * (⌈Bf⌉₊ : ℝ) ^ 2) := by
  have hρc : 0 < ρc := hδ.trans_le hδρc
  have hρ0p : 0 < ρ0 := by linarith
  have hBf0 : 0 < Bf := by linarith
  -- the cell count
  set X := 2 * (4 * (δ + ρc / 2) / ((ρ0 - 2 * (ρc / 2)) / 2)) / ρc with hX
  have hXle : X ≤ 48 / ρ0 := by
    rw [hX]
    have h1 : (ρ0 - 2 * (ρc / 2)) / 2 ≥ ρ0 / 4 := by linarith
    have h2 : 4 * (δ + ρc / 2) ≤ 6 * ρc := by linarith
    have h3 : 4 * (δ + ρc / 2) / ((ρ0 - 2 * (ρc / 2)) / 2) ≤ 6 * ρc / (ρ0 / 4) := by
      apply div_le_div₀ (by positivity) h2 (by positivity) h1
    calc 2 * (4 * (δ + ρc / 2) / ((ρ0 - 2 * (ρc / 2)) / 2)) / ρc
        ≤ 2 * (6 * ρc / (ρ0 / 4)) / ρc := by gcongr
      _ = 48 / ρ0 := by field_simp; ring
  have hX0 : 0 ≤ X := by rw [hX]; apply div_nonneg _ hρc.le; apply mul_nonneg (by norm_num);
                          apply div_nonneg (by linarith); linarith
  have hfl : ((⌊X⌋₊ : ℕ) : ℝ) + 3 ≤ 51 / ρ0 := by
    have := Nat.floor_le hX0
    have h51 : 3 ≤ 3 / ρ0 := by rw [le_div_iff₀ hρ0p]; nlinarith
    calc ((⌊X⌋₊ : ℕ) : ℝ) + 3 ≤ 48 / ρ0 + 3 / ρ0 := by linarith
      _ = 51 / ρ0 := by ring
  have hCfl : ((⌊Cc⌋₊ : ℕ) : ℝ) ≤ Cc := Nat.floor_le hCc.le
  have hBce : (⌈Bf⌉₊ : ℝ) ≤ 2 * Bf := by
    have := Nat.ceil_lt_add_one hBf0.le
    linarith
  have hK : ((8 * ((8 * ⌊Cc⌋₊) ^ 2 * (2 * (⌊X⌋₊ + 3) ^ 3)) : ℕ) : ℝ) ≤
      2 ^ 11 * Cc ^ 2 * (51 / ρ0) ^ 3 := by
    push_cast
    have h1 : ((⌊Cc⌋₊ : ℕ) : ℝ) ^ 2 ≤ Cc ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hCfl 2
    have h2 : (((⌊X⌋₊ : ℕ) : ℝ) + 3) ^ 3 ≤ (51 / ρ0) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hfl 3
    nlinarith [sq_nonneg Cc, pow_pos (div_pos (by norm_num : (0:ℝ) < 51) hρ0p) 3]
  have hlhs : (A / (Bf * Cc)) ^ 2 * ρ0 ^ 3 / 2 ^ 40 * (2 ^ 11 * Cc ^ 2 * (51 / ρ0) ^ 3) ≤
      A ^ 2 / (8 * Bf ^ 2) := by
    have e : (A / (Bf * Cc)) ^ 2 * ρ0 ^ 3 / 2 ^ 40 * (2 ^ 11 * Cc ^ 2 * (51 / ρ0) ^ 3) =
        A ^ 2 / Bf ^ 2 * (51 ^ 3 / 2 ^ 29) := by
      field_simp
    rw [e]
    have : A ^ 2 / Bf ^ 2 * (51 ^ 3 / 2 ^ 29) ≤ A ^ 2 / Bf ^ 2 * (1 / 8) := by
      apply mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    calc _ ≤ A ^ 2 / Bf ^ 2 * (1 / 8) := this
      _ = A ^ 2 / (8 * Bf ^ 2) := by field_simp
  have hR : A ^ 2 / (8 * Bf ^ 2) ≤ A ^ 2 / (2 * (⌈Bf⌉₊ : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left (sq_nonneg A)
    · have : (1 : ℝ) ≤ ⌈Bf⌉₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
        intro h; rw [Nat.ceil_eq_zero] at h; linarith)
      positivity
    · have h := pow_le_pow_left₀ (by positivity) hBce 2
      nlinarith
  calc (A / (Bf * Cc)) ^ 2 * ρ0 ^ 3 / 2 ^ 40 *
        ((8 * ((8 * ⌊Cc⌋₊) ^ 2 * (2 * (⌊X⌋₊ + 3) ^ 3)) : ℕ) : ℝ)
      ≤ (A / (Bf * Cc)) ^ 2 * ρ0 ^ 3 / 2 ^ 40 * (2 ^ 11 * Cc ^ 2 * (51 / ρ0) ^ 3) := by
        apply mul_le_mul_of_nonneg_left hK; positivity
    _ ≤ A ^ 2 / (8 * Bf ^ 2) := hlhs
    _ ≤ _ := hR

/-- `TwoScaleAt` with the grid side and the radius of the underlying level cover pinned to the
coarse scale (`ρc / 16 ≤ s ≤ ρc`, `ρc / 16 ≤ ρ0`). -/
def TwoScaleAtP (σ ε δ ρc : ℝ) (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) : Prop :=
  ∃ (Y' : Fin n → Set Space) (k : ℕ) (z w : Fin k → Space) (Yt : Fin k → Set Space)
    (a : Fin n → Fin k) (s : ℝ) (M : Fin k → Finset (Fin 3 → ℤ)),
    (∀ i, Y' i ⊆ Y i) ∧ (∀ i, MeasurableSet (Y' i)) ∧
    ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) ≤ ∑ i, volume (Y' i) ∧
    Family ε ρc k z w Yt ∧ Separated ε ρc k z w ∧
    volume (⋃ j, Yt j) ≤ ENNReal.ofReal (ρc ^ (σ - ε)) ∧
    (∀ i, (1 - 4 * ρc) • Y' i ⊆ Yt (a i)) ∧
    (∀ i, (Y' i).Nonempty → min ‖v i - w (a i)‖ ‖v i + w (a i)‖ ≤ ρc / 2) ∧
    0 < s ∧ ρc / 16 ≤ s ∧ s ≤ ρc ∧ (∀ j, Yt j = ⋃ m ∈ M j, gridCube s m) ∧
    (∀ p, p ∈ (⋃ i, Y' i) → δ ^ (2 - σ + ε) * (n : ℝ) ≤ (fineMult Y' p : ℝ)) ∧
    (∀ j p, ({i | a i = j ∧ p ∈ Y' i}.ncard : ℝ) ≤
      (δ / ρc) ^ (2 - σ - ε) * ((n : ℝ) / (k : ℝ))) ∧
    (∀ q, (fineMult Yt q : ℝ) ≤ ρc ^ (2 - σ - ε) * (k : ℝ)) ∧
    (∀ q, q ∈ (⋃ j, Yt j) → ρc ^ (2 - σ + ε) * (k : ℝ) ≤ (fineMult Yt q : ℝ)) ∧
    (∀ j, ∀ m ∈ M j, ∃ i, a i = j ∧ ∃ p ∈ Y' i, (1 - 4 * ρc) • p ∈ gridCube s m) ∧
    (∃ (ρ0 : ℝ) (z0 w0 : Fin k → Space), δ ≤ ρ0 ∧ ρc / 16 ≤ ρ0 ∧ ρ0 ≤ ρc ∧
      (∀ j, ‖w0 j‖ = 1) ∧
      (∀ i, (Y' i).Nonempty → tube δ (x i) (v i) ⊆ tube ρ0 (z0 (a i)) (w0 (a i))) ∧
      (∀ i j j', tube δ (x i) (v i) ⊆ dilatedTube ρ0 (z0 j) (w0 j) →
        tube δ (x i) (v i) ⊆ dilatedTube ρ0 (z0 j') (w0 j') → j = j')) ∧
    -- (P2) balanced fibres
    (∀ j, ({i | a i = j ∧ (Y' i).Nonempty}.ncard : ℝ) ≤ δ ^ (-ε) * ((n : ℝ) / (k : ℝ))) ∧
    -- (P3) balanced cover: comparable fine density in every coarse cube
    (∃ θ : ℝ, 0 < θ ∧ ∀ j, ∀ m ∈ M j,
      ENNReal.ofReal θ * volume (gridCube s m) ≤
        volume ((⋃ i, (1 - 4 * ρc) • Y' i) ∩ gridCube s m) ∧
      volume ((⋃ i, (1 - 4 * ρc) • Y' i) ∩ gridCube s m) ≤
        ENNReal.ofReal (δ ^ (-ε) * θ) * volume (gridCube s m))

/-- `TwoScaleTheorem` with the pinned interface. -/
def TwoScaleTheoremP (σ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η d0 : ℝ, 0 < η ∧ 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ (1 / 100 : ℝ) →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
      Family η δ n x v Y → Separated η δ n x v →
      volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
      ∀ r : ℝ, δ ^ (1 - ε) ≤ r → r ≤ δ ^ ε →
        ∃ ρc : ℝ, r ≤ ρc ∧ ρc ≤ δ ^ (-ε) * r ∧ TwoScaleAtP σ ε δ ρc n x v Y

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- `A / (B Cc) = δ ^ (2 ε)` for the standard multiplicity bounds of a two-scale decomposition. -/
theorem standard_ratio {σ ε δ ρc : ℝ} {n k : ℕ} (hδ : 0 < δ) (hρc : 0 < ρc) (hn : 0 < n)
    (hk : 0 < k) :
    δ ^ (2 - σ + ε) * (n : ℝ) /
      ((δ / ρc) ^ (2 - σ - ε) * ((n : ℝ) / (k : ℝ)) * (ρc ^ (2 - σ - ε) * (k : ℝ))) =
      δ ^ (2 * ε) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (δ / ρc) ^ (2 - σ - ε) * ρc ^ (2 - σ - ε) = δ ^ (2 - σ - ε) := by
    rw [Real.div_rpow hδ.le hρc.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hρc _).ne']
  have h2 : δ ^ (2 - σ + ε) = δ ^ (2 - σ - ε) * δ ^ (2 * ε) := by
    rw [← Real.rpow_add hδ]; ring_nf
  have hd : 0 < δ ^ (2 - σ - ε) := Real.rpow_pos_of_pos hδ _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hBC : (δ / ρc) ^ (2 - σ - ε) * ((n : ℝ) / (k : ℝ)) * (ρc ^ (2 - σ - ε) * (k : ℝ)) =
      δ ^ (2 - σ - ε) * (n : ℝ) := by
    calc (δ / ρc) ^ (2 - σ - ε) * ((n : ℝ) / (k : ℝ)) * (ρc ^ (2 - σ - ε) * (k : ℝ))
        = ((δ / ρc) ^ (2 - σ - ε) * ρc ^ (2 - σ - ε)) * ((n : ℝ) / (k : ℝ) * k) := by ring
      _ = _ := by rw [h1, div_mul_cancel₀ _ hkR.ne']
  rw [hBC, h2]
  field_simp

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- Points of a nonempty frozen family: some shading is nonempty. -/
theorem Family.exists_mem {η δ : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (h : Family η δ n x v Y) (hδ : 0 < δ) : ∃ i, ∃ p, p ∈ Y i := by
  by_contra hne
  push Not at hne
  have h0 : ∑ i, volume (Y i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [show Y i = ∅ from Set.eq_empty_iff_forall_notMem.2 (hne i), measure_empty]
  have hpos : (0 : ℝ) < δ ^ η * (n : ℝ) * δ ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast h.1
    positivity
  have := h.2.2.2.2.2.2
  rw [h0] at this
  exact (ENNReal.ofReal_pos.2 hpos).ne' (le_antisymm this zero_le)

/-- A family whose fibre multiplicity is bounded by `B` at a point of a shading has `1 ≤ B`. -/
theorem one_le_of_fibre_bound {n k : ℕ} {Y : Fin n → Set Space} {a : Fin n → Fin k} {B : ℝ}
    (hB : ∀ j p, ({i | a i = j ∧ p ∈ Y i}.ncard : ℝ) ≤ B) {i : Fin n} {p : Space}
    (hp : p ∈ Y i) : 1 ≤ B := by
  have hne : ({l | a l = a i ∧ p ∈ Y l} : Set (Fin n)).Nonempty := ⟨i, rfl, hp⟩
  have h1 : 1 ≤ ({l | a l = a i ∧ p ∈ Y l}.ncard) :=
    Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (Set.toFinite _)).2 hne).ne'
  exact le_trans (by exact_mod_cast h1) (hB (a i) p)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **One Lipschitz scale** (sticky Lemma 4.5 / Corollary 4.6 on the pinned interface).  An
`η`-extremal family with a plane map of precision `δ` has an `ε`-extremal refinement on which the
plane map varies by less than `2 ρc` between points closer than `ρc / 16`, for some coarse scale
`ρc ∈ [t, δ^(-ε) t]`, for any requested `t ∈ [δ^(1-ε), δ^ε]`. -/
theorem lipschitz_scale_step {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2) (hTS : TwoScaleTheoremP σ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ∃ η d1 : ℝ, 0 < η ∧ η ≤ ε ∧ 0 < d1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d1 → δ ≤ 1 / 100 →
      ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (V : Space → Space),
        Family η δ n x v Y → Separated η δ n x v →
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) →
        Measurable V → (∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) →
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) →
        ∀ t : ℝ, δ ^ (1 - ε) ≤ t → t ≤ δ ^ ε →
        ∃ Y' : Fin n → Set Space, (∀ i, Y' i ⊆ Y i) ∧ Family ε δ n x v Y' ∧
          ∃ ρc : ℝ, t ≤ ρc ∧ ρc ≤ δ ^ (-ε) * t ∧
            ∀ p ∈ ⋃ i, Y' i, ∀ q ∈ ⋃ i, Y' i, dist p q < ρc / 16 →
              dist (V p) (V q) < 2 * ρc := by
  -- parameters
  set κ := ε / 8 with hκ
  set ερ := σ * ε / 64 with hερ
  have hκ0 : 0 < κ := by positivity
  have hερ0 : 0 < ερ := by positivity
  have hερε : ερ ≤ ε / 32 := by rw [hερ]; nlinarith
  obtain ⟨ηρ, dρ, hηρ, hdρ, hTSρ⟩ := hTS ερ hερ0
  set εβ := min ερ ηρ with hεβ
  have hεβ0 : 0 < εβ := lt_min hερ0 hηρ
  have hεβρ : εβ ≤ ερ := min_le_left _ _
  have hεβη : εβ ≤ ηρ := min_le_right _ _
  obtain ⟨ηβ, dβ, hηβ, hdβ, hTSβ⟩ := hTS εβ hεβ0
  set η := min (min ηβ ηρ) ε with hη
  have hη0 : 0 < η := lt_min (lt_min hηβ hηρ) hε
  have hηβ' : η ≤ ηβ := (min_le_left _ _).trans (min_le_left _ _)
  have hηρ' : η ≤ ηρ := (min_le_left _ _).trans (min_le_right _ _)
  have hηε : η ≤ ε := min_le_right _ _
  -- cutoffs
  have he1 : 0 < ε - 5 * ερ - 3 * κ := by rw [hκ]; linarith
  have he2 : 0 < ε - ερ - κ := by rw [hκ]; linarith
  have he3 : 0 < σ * ε / 16 := by positivity
  obtain ⟨c1, hc1, hcut1⟩ := exists_power_cutoff he1 (by norm_num : (0:ℝ) < 1 / 2 ^ 52)
  obtain ⟨c2, hc2, hcut2⟩ := exists_power_cutoff he2 (by norm_num : (0:ℝ) < 1 / 32)
  obtain ⟨c3, hc3, hcut3⟩ := exists_power_cutoff he3 (by norm_num : (0:ℝ) < 1 / 112)
  refine ⟨η, min (min dρ dβ) (min (min c1 c2) c3), hη0, hηε,
    lt_min (lt_min hdρ hdβ) (lt_min (lt_min hc1 hc2) hc3), ?_⟩
  intro δ hδ hδd1 hδ100 n x v Y V hFam hSep hvol hVm hVu hVp t ht1 ht2
  have hδρ : δ ≤ dρ := hδd1.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδβ : δ ≤ dβ := hδd1.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδc1 : δ ≤ c1 := hδd1.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδc2 : δ ≤ c2 := hδd1.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδc3 : δ ≤ c3 := hδd1.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ1 : δ ≤ 1 := by linarith
  have hn : 0 < n := hFam.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- the β-level decomposition at angle scale `δ ^ κ`
  have hβr1 : δ ^ (1 - εβ) ≤ δ ^ κ :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by rw [hκ]; linarith)
  have hβr2 : δ ^ κ ≤ δ ^ εβ :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by rw [hκ]; linarith)
  obtain ⟨ρβ, hρβ1, hρβ2, hTSAβ⟩ := hTSβ δ hδ hδβ hδ100 n x v Y
    (hFam.mono_error hδ hδ1 hηβ') (hSep.mono_error hδ hδ1 hηβ')
    (hvol.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)))) (δ ^ κ) hβr1 hβr2
  obtain ⟨Y1, k1, z1, w1, Yt1, a1, s1, M1, hY1Y, hY1m, hY1mass, hFam1, hSep1, hvol1, hcontr1,
    hdir1, hs1, hs1lo, hs1hi, hYt1, hfine1, hfib1, hcoarse1, hclo1, hR1β,
    ⟨ρ0, z0, w0, hδρ0, hρ0lo, hρ0hi, hw0, hcov1, hsep1⟩, -⟩ := hTSAβ
  have hρβpos : 0 < ρβ := (Real.rpow_pos_of_pos hδ _).trans_le hρβ1
  -- the ρ-level decomposition at the requested scale `t`
  have hY1T : ∀ i, Y1 i ⊆ tube δ (x i) (v i) := fun i => (hY1Y i).trans (hFam.2.2.2.2.2.1 i)
  have hFamY1 : Family ηρ δ n x v Y1 := by
    refine ⟨hn, hFam.2.1, hFam.2.2.1, hFam.2.2.2.1, hY1m, hY1T, ?_⟩
    apply le_trans (ENNReal.ofReal_le_ofReal _) hY1mass
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hεβη) hnR.le) (sq_nonneg _)
  have hvolY1 : volume (⋃ i, Y1 i) ≤ ENNReal.ofReal (δ ^ (σ - ηρ)) :=
    (measure_mono (iUnion_mono hY1Y)).trans (hvol.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))))
  have htr1 : δ ^ (1 - ερ) ≤ t :=
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans ht1
  have htr2 : t ≤ δ ^ ερ :=
    ht2.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  obtain ⟨ρc, hρc1, hρc2, hTSAρ⟩ := hTSρ δ hδ hδρ hδ100 n x v Y1 hFamY1
    (hSep.mono_error hδ hδ1 hηρ') hvolY1 t htr1 htr2
  obtain ⟨Y2, k, z, w, Yt, a, s, M, hY2Y1, hY2m, hY2mass, hFamc, hSepc, hvolc, hcontr,
    hdir, hs, hslo, hshi, hYt, hfine, hfib, hcoarse, hclo, hR1, -⟩ := hTSAρ
  have hk : 0 < k := hFamc.1
  have hk1 : 0 < k1 := hFam1.1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1R : (0 : ℝ) < k1 := by exact_mod_cast hk1
  -- scale facts
  have hδκ : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ _
  have hρβle : ρβ ≤ δ ^ (κ - εβ) := by
    rw [show κ - εβ = -εβ + κ by ring, Real.rpow_add hδ]; exact hρβ2
  have hκεβ : 0 ≤ κ - εβ := by rw [hκ]; linarith
  have hρβ1' : ρβ ≤ 1 := hρβle.trans (Real.rpow_le_one hδ.le hδ1 hκεβ)
  have hρc0 : 0 < ρc := (Real.rpow_pos_of_pos hδ _).trans_le (htr1.trans hρc1)
  have hδρc : δ ≤ ρc := by
    have : δ ≤ δ ^ (1 - ε) := by
      calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
        _ ≤ δ ^ (1 - ε) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    exact this.trans (ht1.trans hρc1)
  have hρcup : ρc ≤ δ ^ (ε - ερ) := by
    calc ρc ≤ δ ^ (-ερ) * t := hρc2
      _ ≤ δ ^ (-ερ) * δ ^ ε := mul_le_mul_of_nonneg_left ht2 (Real.rpow_nonneg hδ.le _)
      _ = δ ^ (ε - ερ) := by rw [← Real.rpow_add hδ]; ring_nf
  have hc2' : δ ^ (ε - ερ - κ) ≤ 1 / 32 := hcut2 δ hδ hδc2
  have hρc32 : ρc ≤ δ ^ κ / 32 := by
    calc ρc ≤ δ ^ (ε - ερ) := hρcup
      _ = δ ^ (ε - ερ - κ) * δ ^ κ := by rw [← Real.rpow_add hδ]; ring_nf
      _ ≤ 1 / 32 * δ ^ κ := mul_le_mul_of_nonneg_right hc2' hδκ.le
      _ = δ ^ κ / 32 := by ring
  have hρ0β : δ ^ κ / 16 ≤ ρ0 := by linarith
  have h2ρc : 2 * ρc ≤ ρ0 := by linarith
  have hρ01 : ρ0 ≤ 1 := hρ0hi.trans hρβ1'
  have hδκ1 : δ ^ κ ≤ 1 := Real.rpow_le_one hδ.le hδ1 hκ0.le
  have hlam : 0 < 1 - 4 * ρc := by linarith
  -- multiplicity bounds
  set A := δ ^ (2 - σ + ερ) * (n : ℝ) with hA
  set B1 := (δ / ρβ) ^ (2 - σ - εβ) * ((n : ℝ) / (k1 : ℝ)) with hB1
  set Bf := (δ / ρc) ^ (2 - σ - ερ) * ((n : ℝ) / (k : ℝ)) with hBf
  set Cc := ρc ^ (2 - σ - ερ) * (k : ℝ) with hCc
  have hA0 : 0 < A := mul_pos (Real.rpow_pos_of_pos hδ _) hnR
  have hB10 : 0 ≤ B1 := mul_nonneg (Real.rpow_nonneg (div_nonneg hδ.le hρβpos.le) _)
    (div_nonneg hnR.le hk1R.le)
  have hCc0 : 0 < Cc := mul_pos (Real.rpow_pos_of_pos hρc0 _) hkR
  obtain ⟨i2, p2, hp2⟩ : ∃ i, ∃ p, p ∈ Y2 i := by
    by_contra hne
    push Not at hne
    have h0 : ∑ i, volume (Y2 i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [show Y2 i = ∅ from Set.eq_empty_iff_forall_notMem.2 (hne i), measure_empty]
    rw [h0] at hY2mass
    have hpos : (0 : ℝ) < δ ^ ερ * (n : ℝ) * δ ^ 2 := by positivity
    exact (ENNReal.ofReal_pos.2 hpos).ne' (le_antisymm hY2mass zero_le)
  have hBf1 : 1 ≤ Bf := one_le_of_fibre_bound hfib hp2
  -- robust transversality budget
  have hk1low := counting_constant_ge_one hρβpos hρβ1' hk1 hFam1.2.1
    (hSep1.global_frostman hρβpos hρβ1' hk1 hFam1.2.2.1)
  have hB1A : B1 ≤ A / 2 := by
    have hnk : (n : ℝ) / k1 ≤ 56 * (n : ℝ) * ρβ ^ (-εβ) * ρβ ^ 2 := by
      rw [div_le_iff₀ hk1R]
      calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
        _ ≤ (n : ℝ) * (56 * ρβ ^ (-εβ) * (k1 : ℝ) * ρβ ^ 2) :=
            mul_le_mul_of_nonneg_left hk1low hnR.le
        _ = 56 * (n : ℝ) * ρβ ^ (-εβ) * ρβ ^ 2 * (k1 : ℝ) := by ring
    have hpow : (δ / ρβ) ^ (2 - σ - εβ) * (ρβ ^ (-εβ) * ρβ ^ 2) =
        δ ^ (2 - σ - εβ) * ρβ ^ σ := by
      rw [Real.div_rpow hδ.le hρβpos.le, show ρβ ^ 2 = ρβ ^ (2 : ℝ) by norm_cast,
        ← Real.rpow_add hρβpos]
      have : ρβ ^ (-εβ + 2) = ρβ ^ (2 - σ - εβ) * ρβ ^ σ := by
        rw [← Real.rpow_add hρβpos]; ring_nf
      rw [this]
      field_simp
    have hρβσ : ρβ ^ σ ≤ δ ^ (σ * (κ - εβ)) := by
      calc ρβ ^ σ ≤ (δ ^ (κ - εβ)) ^ σ := Real.rpow_le_rpow hρβpos.le hρβle hσ.le
        _ = δ ^ (σ * (κ - εβ)) := by rw [← Real.rpow_mul hδ.le]; ring_nf
    have hexp : ερ + εβ + σ * ε / 16 ≤ σ * (κ - εβ) := by
      have h1 : σ * εβ ≤ σ * ερ := mul_le_mul_of_nonneg_left hεβρ hσ.le
      have h2 : σ * ερ ≤ 2 * ερ := mul_le_mul_of_nonneg_right hσ2 hερ0.le
      have h3 : ερ = σ * ε / 64 := hερ
      have h4 : σ * κ = σ * ε / 8 := by rw [hκ]; ring
      have h5 : σ * (κ - εβ) = σ * κ - σ * εβ := by ring
      rw [h5]
      linarith
    have hc3' : δ ^ (σ * ε / 16) ≤ 1 / 112 := hcut3 δ hδ hδc3
    have hδσ : δ ^ (σ * (κ - εβ)) ≤ δ ^ (ερ + εβ) / 112 := by
      calc δ ^ (σ * (κ - εβ)) ≤ δ ^ (ερ + εβ + σ * ε / 16) :=
            Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
        _ = δ ^ (ερ + εβ) * δ ^ (σ * ε / 16) := Real.rpow_add hδ _ _
        _ ≤ δ ^ (ερ + εβ) * (1 / 112) :=
            mul_le_mul_of_nonneg_left hc3' (Real.rpow_nonneg hδ.le _)
        _ = δ ^ (ερ + εβ) / 112 := by ring
    have hsplit : δ ^ (2 - σ + ερ) = δ ^ (2 - σ - εβ) * δ ^ (ερ + εβ) := by
      rw [← Real.rpow_add hδ]; ring_nf
    calc B1 ≤ (δ / ρβ) ^ (2 - σ - εβ) * (56 * (n : ℝ) * ρβ ^ (-εβ) * ρβ ^ 2) :=
          mul_le_mul_of_nonneg_left hnk (Real.rpow_nonneg (div_nonneg hδ.le hρβpos.le) _)
      _ = 56 * (n : ℝ) * ((δ / ρβ) ^ (2 - σ - εβ) * (ρβ ^ (-εβ) * ρβ ^ 2)) := by ring
      _ = 56 * (n : ℝ) * (δ ^ (2 - σ - εβ) * ρβ ^ σ) := by rw [hpow]
      _ ≤ 56 * (n : ℝ) * (δ ^ (2 - σ - εβ) * (δ ^ (ερ + εβ) / 112)) := by
          gcongr; exact hρβσ.trans hδσ
      _ = A / 2 := by rw [hA, hsplit]; ring
  -- one Lipschitz step
  obtain ⟨E', hE'm, hE'sub, hmass, hvar⟩ := lipschitz_step (k := k) (k1 := k1) (δ := δ)
    (ρ0 := ρ0) (ρc := ρc) (s := s) (lam := 1 - 4 * ρc) (A := A) (B1 := B1) (Bf := Bf) (Cc := Cc)
    (x := x) (v := v) (Y1 := Y1) (Y2 := Y2) hFam.2.1 hY2m (fun i => (hY2Y1 i).trans (hY1T i))
    hY2Y1 hVm (fun p hp => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 hp
      exact hVu p (mem_iUnion.2 ⟨i, hY1Y i (hY2Y1 i hi)⟩))
    (fun i p hp => hVp i p (hY1Y i (hY2Y1 i hp))) (a1 := a1) (z0 := z0) (w0 := w0) hw0 hδρ0 hδ
    hcov1 hsep1 hfib1 (a := a) (w := w) hFamc.2.1 (Yt := Yt) (M := M) hs hlam hYt hcontr hdir
    hfine hfib hcoarse hρc0 (by linarith) ⟨hB10, hB1A⟩ hA0
    (le_trans zero_le_one hBf1) hCc0.le hBf1
  -- the refined family
  refine ⟨fun i => Y2 i ∩ E', fun i => inter_subset_left.trans ((hY2Y1 i).trans (hY1Y i)),
    ⟨hn, hFam.2.1, hFam.2.2.1, hFam.2.2.2.1, fun i => (hY2m i).inter hE'm,
      fun i => inter_subset_left.trans ((hY2Y1 i).trans (hY1T i)), ?_⟩, ρc, hρc1, ?_, ?_⟩
  · -- mass
    obtain ⟨j0, q0, hq0⟩ := hFamc.exists_mem hρc0
    have hCc1 : 1 ≤ Cc := by
      have h1 : 1 ≤ fineMult Yt q0 :=
        Nat.one_le_iff_ne_zero.2 ((Set.ncard_pos (Set.toFinite _)).2 ⟨j0, hq0⟩).ne'
      exact le_trans (by exact_mod_cast h1) (hcoarse q0)
    set K : ℕ := 8 * ((8 * ⌊Cc⌋₊) ^ 2 * (2 * (⌊2 * (4 * (δ + ρc / 2) / ((ρ0 - 2 * (ρc / 2)) / 2)) /
          ρc⌋₊ + 3) ^ 3)) with hK
    have hK0 : K ≠ 0 := by
      have : 1 ≤ ⌊Cc⌋₊ := Nat.le_floor (by exact_mod_cast hCc1)
      rw [hK]; positivity
    set frac := (A / (Bf * Cc)) ^ 2 * ρ0 ^ 3 / 2 ^ 40 with hfrac
    have hfrac0 : 0 ≤ frac :=
      div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (hδ.le.trans hδρ0) 3)) (by norm_num)
    have hcount := lipschitz_step_count_le (A := A) hδ hδρc h2ρc hρ01 hBf1 hCc0
    have hstep : (K : ℝ≥0∞) * (ENNReal.ofReal frac * massMeasure Y2 (⋃ i, Y2 i)) ≤
        (K : ℝ≥0∞) * massMeasure Y2 E' := by
      calc (K : ℝ≥0∞) * (ENNReal.ofReal frac * massMeasure Y2 (⋃ i, Y2 i))
          = ENNReal.ofReal (frac * K) * massMeasure Y2 (⋃ i, Y2 i) := by
            rw [ENNReal.ofReal_mul hfrac0, ENNReal.ofReal_natCast]; ring
        _ ≤ ENNReal.ofReal (A ^ 2 / (2 * (⌈Bf⌉₊ : ℝ) ^ 2)) * massMeasure Y2 (⋃ i, Y2 i) := by
            gcongr
        _ ≤ (K : ℝ≥0∞) * massMeasure Y2 E' := hmass
    have hfin : (K : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top K
    have hK0' : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK0
    have hmass' := (ENNReal.mul_le_mul_iff_right hK0' hfin).1 hstep
    rw [massMeasure_apply hY2m hE'm, massMeasure_apply hY2m (MeasurableSet.iUnion hY2m)] at hmass'
    have hU : ∀ i, Y2 i ∩ ⋃ j, Y2 j = Y2 i := fun i => inter_eq_left.2 (subset_iUnion Y2 i)
    simp only [hU] at hmass'
    -- arithmetic
    have hratio : A / (Bf * Cc) = δ ^ (2 * ερ) := by
      have := standard_ratio (σ := σ) (ε := ερ) hδ hρc0 hn hk
      rw [hA, hBf, hCc]
      convert this using 2
    have hρ03 : δ ^ (3 * κ) / 4096 ≤ ρ0 ^ 3 := by
      have h1 : (δ ^ κ / 16) ^ 3 ≤ ρ0 ^ 3 := pow_le_pow_left₀ (by positivity) hρ0β 3
      have h2 : (δ ^ κ / 16) ^ 3 = δ ^ (3 * κ) / 4096 := by
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; norm_num; ring_nf
      linarith
    have hc1' : δ ^ (ε - 5 * ερ - 3 * κ) ≤ 1 / 2 ^ 52 := hcut1 δ hδ hδc1
    have hfinal : δ ^ ε * (n : ℝ) * δ ^ 2 ≤ frac * (δ ^ ερ * (n : ℝ) * δ ^ 2) := by
      have e1 : frac * (δ ^ ερ * (n : ℝ) * δ ^ 2) =
          (δ ^ (2 * ερ)) ^ 2 * ρ0 ^ 3 / 2 ^ 40 * δ ^ ερ * ((n : ℝ) * δ ^ 2) := by
        rw [hfrac, hratio]; ring
      have e2 : (δ ^ (2 * ερ)) ^ 2 * δ ^ ερ = δ ^ (5 * ερ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]; norm_num; ring_nf
      have e3 : δ ^ ε = δ ^ (ε - 5 * ερ - 3 * κ) * (δ ^ (5 * ερ) * δ ^ (3 * κ)) := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]; ring_nf
      have hnd : 0 ≤ (n : ℝ) * δ ^ 2 := by positivity
      have hlow : δ ^ ε ≤ δ ^ (5 * ερ) * ρ0 ^ 3 / 2 ^ 40 := by
        rw [e3]
        have hp : 0 ≤ δ ^ (5 * ερ) := Real.rpow_nonneg hδ.le _
        calc δ ^ (ε - 5 * ερ - 3 * κ) * (δ ^ (5 * ερ) * δ ^ (3 * κ))
            ≤ 1 / 2 ^ 52 * (δ ^ (5 * ερ) * δ ^ (3 * κ)) :=
              mul_le_mul_of_nonneg_right hc1' (by positivity)
          _ = δ ^ (5 * ερ) * (δ ^ (3 * κ) / 4096) / 2 ^ 40 := by ring
          _ ≤ δ ^ (5 * ερ) * ρ0 ^ 3 / 2 ^ 40 := by gcongr
      calc δ ^ ε * (n : ℝ) * δ ^ 2 = δ ^ ε * ((n : ℝ) * δ ^ 2) := by ring
        _ ≤ δ ^ (5 * ερ) * ρ0 ^ 3 / 2 ^ 40 * ((n : ℝ) * δ ^ 2) :=
            mul_le_mul_of_nonneg_right hlow hnd
        _ = (δ ^ (2 * ερ)) ^ 2 * δ ^ ερ * ρ0 ^ 3 / 2 ^ 40 * ((n : ℝ) * δ ^ 2) := by rw [e2]
        _ = _ := by rw [e1]; ring
    calc ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2)
        ≤ ENNReal.ofReal (frac * (δ ^ ερ * (n : ℝ) * δ ^ 2)) := ENNReal.ofReal_le_ofReal hfinal
      _ = ENNReal.ofReal frac * ENNReal.ofReal (δ ^ ερ * (n : ℝ) * δ ^ 2) :=
          ENNReal.ofReal_mul hfrac0
      _ ≤ ENNReal.ofReal frac * ∑ i, volume (Y2 i) := by gcongr
      _ ≤ ∑ i, volume (Y2 i ∩ E') := hmass'
  · calc ρc ≤ δ ^ (-ερ) * t := hρc2
      _ ≤ δ ^ (-ε) * t := by
          apply mul_le_mul_of_nonneg_right _ ((Real.rpow_nonneg hδ.le _).trans ht1)
          exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  · intro p hp q hq hpq
    obtain ⟨i, hi⟩ := mem_iUnion.1 hp
    obtain ⟨j, hj⟩ := mem_iUnion.1 hq
    apply hvar p hi.2 q hj.2
    have hlam1 : 1 - 4 * ρc ≤ 1 := by linarith
    calc dist p q < ρc / 16 := hpq
      _ ≤ s := hslo
      _ ≤ s / (1 - 4 * ρc) := le_div_self hs.le hlam hlam1

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- `coarse_plane_map` on the pinned interface, exposing the grid side. -/
theorem coarse_plane_mapP {σ ε δ ρc : ℝ} {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hn : 0 < n) (hδ : 0 < δ) (hρc : 0 < ρc)
    (hTS : TwoScaleAtP σ ε δ ρc n x v Y) {V : Space → Space} (hVm : Measurable V)
    (hVu : ∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1)
    (hVp : ∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ ρc / 2) :
    ∃ (k : ℕ) (z w : Fin k → Space) (Yt Yt'' : Fin k → Set Space) (Vt : Space → Space) (s : ℝ),
      Family ε ρc k z w Yt ∧ Separated ε ρc k z w ∧
      volume (⋃ j, Yt j) ≤ ENNReal.ofReal (ρc ^ (σ - ε)) ∧
      (∀ j, Yt'' j ⊆ Yt j) ∧ (∀ j, MeasurableSet (Yt'' j)) ∧
      (∀ q, δ ^ (2 * ε) * incidence Yt q ≤ incidence Yt'' q) ∧ Measurable Vt ∧
      (∀ q ∈ ⋃ j, Yt'' j, ‖Vt q‖ = 1) ∧
      (∀ j q, q ∈ Yt'' j → |inner ℝ (w j) (Vt q)| ≤ ρc) ∧
      0 < s ∧ ρc / 16 ≤ s ∧ s ≤ ρc ∧ (∀ q q', cubeIndex s q = cubeIndex s q' → Vt q = Vt q') := by
  obtain ⟨Y', k, z, w, Yt, a, s, M, hY'Y, hY'm, hY'mass, hFam, hSep, hvol, hcontr, hdir, hs,
    hslo, hshi, hYt, hfine, hfib, hcoarse, -, hR1, -⟩ := hTS
  have hk : 0 < k := hFam.1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set A := δ ^ (2 - σ + ε) * (n : ℝ) with hAdef
  set B := (δ / ρc) ^ (2 - σ - ε) * ((n : ℝ) / (k : ℝ)) with hBdef
  set Cc := ρc ^ (2 - σ - ε) * (k : ℝ) with hCdef
  have hB : 0 < B := mul_pos (Real.rpow_pos_of_pos (div_pos hδ hρc) _) (div_pos hnR hkR)
  have hC : 0 < Cc := mul_pos (Real.rpow_pos_of_pos hρc _) hkR
  have hA : 0 ≤ A := mul_nonneg (Real.rpow_nonneg hδ.le _) hnR.le
  have hABC : A / (B * Cc) = δ ^ (2 * ε) := by
    have := standard_ratio (σ := σ) (ε := ε) hδ hρc hn hk
    rw [hAdef, hBdef, hCdef]
    convert this using 2
  have hVu' : ∀ p ∈ ⋃ i, Y' i, ‖V p‖ = 1 := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.1 hp
    exact hVu p (mem_iUnion.2 ⟨i, hY'Y i hi⟩)
  obtain ⟨Yt'', Vt, hsub, hmeas, hinc, hVtm, hVtu, hVtp, hcube⟩ :=
    strong_plane_map (v := v) (Y' := Y') (w := w) (Yt := Yt) (a := a) (s := s) (ρc := ρc)
      (lam := 1 - 4 * ρc) (A := A) (B := B) (Cc := Cc) hs hYt hcontr hR1
      (fun i hi => by rw [norm_sub_rev, add_comm]; exact hdir i hi)
      (fun p hp => by rw [incidence_eq_fineMult]; exact hfine p hp)
      hfib (fun q => by rw [incidence_eq_fineMult]; exact hcoarse q)
      V hVm hVu' (fun i p hp => hVp i p (hY'Y i hp)) hA hB hC
  refine ⟨k, z, w, Yt, Yt'', Vt, s, hFam, hSep, hvol, hsub, hmeas, ?_, hVtm, hVtu, hVtp, hs,
    hslo, hshi, hcube⟩
  intro q
  rw [← hABC]
  exact hinc q

/-- Pointwise incidence domination integrates to shading-mass domination. -/
theorem shadingMass_le_of_incidence {n : ℕ} {Y Z : Fin n → Set Space} {c : ℝ}
    (hY : ∀ i, MeasurableSet (Y i)) (hYf : ∀ i, volume (Y i) ≠ ∞)
    (hZ : ∀ i, MeasurableSet (Z i)) (hZf : ∀ i, volume (Z i) ≠ ∞)
    (h : ∀ q, c * incidence Y q ≤ incidence Z q) : c * shadingMass Y ≤ shadingMass Z := by
  rw [← integral_incidence hY hYf, ← integral_incidence hZ hZf, ← integral_const_mul]
  exact integral_mono ((integrable_incidence hY hYf).const_mul c) (integrable_incidence hZ hZf) h

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **Examples with a cube-constant plane map** (sticky Lemmas 4.3 and 4.4 combined): arbitrarily
small `ε`-extremal families at a scale `δ` with a measurable plane map of precision `δ`, unit on
the shaded union and constant on the grid cubes of a side `s ∈ [δ / 16, δ]`. -/
theorem cube_plane_examples {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2)
    (hbelow : ∀ t : ℝ, t < σ → Examples t) (habove : ∀ t : ℝ, σ < t → ¬ Examples t)
    (hTS : TwoScaleTheoremP σ) (ε d0 : ℝ) (hε : 0 < ε) (hd0 : 0 < d0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
      ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (V : Space → Space) (s : ℝ),
        Family ε δ n x v Y ∧ Separated ε δ n x v ∧
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - ε)) ∧
        Measurable V ∧ (∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) ∧
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) ∧
        0 < s ∧ δ / 16 ≤ s ∧ s ≤ δ ∧ (∀ q q', cubeIndex s q = cubeIndex s q' → V q = V q') := by
  set ε' := min ε 1 with hε'
  have hε'0 : 0 < ε' := lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set ε1 := σ * ε' / 1024 with hε1
  have hε10 : 0 < ε1 := by positivity
  have hε1σ : ε1 ≤ σ / 1024 := by rw [hε1]; nlinarith
  have hε1ε : ε1 ≤ ε := by
    have : σ * ε' ≤ 2 * ε' := mul_le_mul_of_nonneg_right hσ2 hε'0.le
    rw [hε1]; linarith
  obtain ⟨η1, d1, hη1, hd1, hTS1⟩ := hTS ε1 hε10
  -- cutoffs on the fine scale
  obtain ⟨c1, hc1, hcut1⟩ := exists_power_cutoff (a := σ * ε' / 512) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 2)
  obtain ⟨c2, hc2, hcut2⟩ := exists_power_cutoff (a := σ / 128) (by positivity)
    (by positivity : (0:ℝ) < min d0 (1 / 100) / 2)
  obtain ⟨c3, hc3, hcut3⟩ := exists_power_cutoff (a := σ / 128) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 2)
  obtain ⟨δf, hδf, hδf0, hδf100, n, x, v, Y, hFam, hSep, -, hvol, P, hPm, hPu, hPp⟩ :=
    weak_plane_examples hσ hbelow habove η1 (min (min d1 c1) (min c2 c3)) hη1
      (lt_min (lt_min hd1 hc1) (lt_min hc2 hc3))
  have hδfd1 : δf ≤ d1 := hδf0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδfc1 : δf ≤ c1 := hδf0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδfc2 : δf ≤ c2 := hδf0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδfc3 : δf ≤ c3 := hδf0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδf1 : δf ≤ 1 := by linarith
  have hn : 0 < n := hFam.1
  -- the requested coarse scale
  set r := 2 * δf ^ (σ / 64) with hr
  have hq3 : δf ^ (σ / 128) ≤ 1 / 2 := hcut3 δf hδf hδfc3
  have hσ64 : δf ^ (σ / 64) = δf ^ (σ / 128) * δf ^ (σ / 128) := by
    rw [← Real.rpow_add hδf]; ring_nf
  have hr1 : δf ^ (1 - ε1) ≤ r := by
    have : δf ^ (1 - ε1) ≤ δf ^ (σ / 64) :=
      Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by nlinarith)
    have h0 : 0 ≤ δf ^ (σ / 64) := Real.rpow_nonneg hδf.le _
    rw [hr]; linarith
  have hr2 : r ≤ δf ^ ε1 := by
    have h1 : δf ^ (σ / 64) = δf ^ (σ / 64 - ε1) * δf ^ ε1 := by
      rw [← Real.rpow_add hδf]; ring_nf
    have h2 : δf ^ (σ / 64 - ε1) ≤ δf ^ (σ / 128) :=
      Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by linarith)
    have h3 : 0 ≤ δf ^ ε1 := Real.rpow_nonneg hδf.le _
    rw [hr, h1]; nlinarith
  obtain ⟨ρc, hρc1, hρc2, hTSA⟩ := hTS1 δf hδf hδfd1 hδf100 n x v Y hFam hSep hvol r hr1 hr2
  have hr0 : 0 < r := by positivity
  have hρc0 : 0 < ρc := hr0.trans_le hρc1
  have hρcup : ρc ≤ 2 * δf ^ (σ / 128) := by
    calc ρc ≤ δf ^ (-ε1) * r := hρc2
      _ = 2 * δf ^ (σ / 64 - ε1) := by
          rw [hr, show σ / 64 - ε1 = -ε1 + σ / 64 by ring, Real.rpow_add hδf]; ring
      _ ≤ 2 * δf ^ (σ / 128) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδf hδf1 (by linarith))
            (by norm_num)
  have hq2 : δf ^ (σ / 128) ≤ min d0 (1 / 100) / 2 := hcut2 δf hδf hδfc2
  have hρcd : ρc ≤ min d0 (1 / 100) := by linarith
  have hρc1' : ρc ≤ 1 := hρcd.trans ((min_le_right _ _).trans (by norm_num))
  obtain ⟨k, z, w, Yt, Yt'', Vt, s, hFamc, hSepc, hvolc, hsub, hmeas, hinc, hVtm, hVtu, hVtp,
    hs, hslo, hshi, hcube⟩ := coarse_plane_mapP hn hδf hρc0 hTSA hPm hPu
      (fun i p hp => (hPp i p hp).trans (by linarith))
  refine ⟨ρc, hρc0, hρcd.trans (min_le_left _ _), hρcd.trans (min_le_right _ _), k, z, w, Yt'',
    Vt, s, ?_, hSepc.mono_error hρc0 hρc1' (by linarith), ?_, hVtm, hVtu, hVtp, hs, hslo, hshi,
    hcube⟩
  · -- mass of the refined coarse shadings
    apply hFamc.of_subsets_mass hsub hmeas
    have hfin := hFamc.shading_finite
    have hfin'' : ∀ j, volume (Yt'' j) ≠ ∞ := fun j =>
      ne_top_of_le_ne_top (hfin j) (measure_mono (hsub j))
    have h1 := shadingMass_le_of_incidence hFamc.2.2.2.2.1 hfin hmeas hfin'' hinc
    have h2 := hFamc.mass_lower hρc0
    have hkey : ρc ^ ε ≤ δf ^ (2 * ε1) * ρc ^ ε1 := by
      have e1 : ρc ^ ε = ρc ^ (ε - ε1) * ρc ^ ε1 := by
        rw [← Real.rpow_add hρc0]; ring_nf
      have hε1' : ε1 ≤ ε' / 512 := by rw [hε1]; nlinarith
      have h3 : ρc ^ (ε - ε1) ≤ ρc ^ (ε' / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' (by linarith)
      have h4 : ρc ^ (ε' / 2) ≤ (2 * δf ^ (σ / 128)) ^ (ε' / 2) :=
        Real.rpow_le_rpow hρc0.le hρcup (by positivity)
      have h5 : (2 * δf ^ (σ / 128)) ^ (ε' / 2) = 2 ^ (ε' / 2) * δf ^ (σ * ε' / 256) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hδf.le _), ← Real.rpow_mul hδf.le]
        ring_nf
      have h6 : (2 : ℝ) ^ (ε' / 2) ≤ 2 := by
        calc (2 : ℝ) ^ (ε' / 2) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2
      have h7 : δf ^ (σ * ε' / 256) = δf ^ (σ * ε' / 512) * δf ^ (2 * ε1) := by
        rw [← Real.rpow_add hδf, hε1]; ring_nf
      have h8 : δf ^ (σ * ε' / 512) ≤ 1 / 2 := hcut1 δf hδf hδfc1
      have h9 : ρc ^ (ε - ε1) ≤ δf ^ (2 * ε1) := by
        have hp : 0 ≤ δf ^ (2 * ε1) := Real.rpow_nonneg hδf.le _
        calc ρc ^ (ε - ε1) ≤ 2 ^ (ε' / 2) * δf ^ (σ * ε' / 256) := by rw [← h5]; linarith
          _ ≤ 2 * (1 / 2 * δf ^ (2 * ε1)) := by
              rw [h7]; gcongr
          _ = δf ^ (2 * ε1) := by ring
      rw [e1]
      exact mul_le_mul_of_nonneg_right h9 (Real.rpow_nonneg hρc0.le _)
    have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    calc ρc ^ ε * (k : ℝ) * ρc ^ 2 ≤ δf ^ (2 * ε1) * ρc ^ ε1 * (k : ℝ) * ρc ^ 2 := by gcongr
      _ = δf ^ (2 * ε1) * (ρc ^ ε1 * (k : ℝ) * ρc ^ 2) := by ring
      _ ≤ δf ^ (2 * ε1) * shadingMass Yt := by
          gcongr
      _ ≤ shadingMass Yt'' := h1
  · exact (measure_mono (iUnion_mono hsub)).trans (hvolc.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hρc0 hρc1' (by linarith))))

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- An `ε`-extremal family at scale `δ` with a cube-constant plane map of precision `δ` that has
been made Lipschitz at the scales `δ ^ (j / N)`, `1 ≤ j ≤ m`. -/
def LipschitzStage (σ : ℝ) (N m : ℕ) (ε δ : ℝ) (n : ℕ) (x v : Fin n → Space)
    (Y : Fin n → Set Space) (V : Space → Space) (s : ℝ) : Prop :=
  Family ε δ n x v Y ∧ Separated ε δ n x v ∧ volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - ε)) ∧
  Measurable V ∧ (∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) ∧
  (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) ∧
  0 < s ∧ δ / 16 ≤ s ∧ s ≤ δ ∧ (∀ q q', cubeIndex s q = cubeIndex s q' → V q = V q') ∧
  ∀ j : ℕ, 1 ≤ j → j ≤ m → ∃ ρc : ℝ, δ ^ ((j : ℝ) / N) ≤ ρc ∧ ρc ≤ δ ^ ((j : ℝ) / N - ε) ∧
    ∀ p ∈ ⋃ i, Y i, ∀ q ∈ ⋃ i, Y i, dist p q < ρc / 16 → dist (V p) (V q) < 2 * ρc

/-- **Iterated Lipschitz scales** (sticky Lemma 4.7, the iteration). -/
theorem lipschitz_stages {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2)
    (hbelow : ∀ t : ℝ, t < σ → Examples t) (habove : ∀ t : ℝ, σ < t → ¬ Examples t)
    (hTS : TwoScaleTheoremP σ) (N : ℕ) (hN : 2 ≤ N) :
    ∀ m : ℕ, m ≤ N - 1 → ∀ ε d0 : ℝ, 0 < ε → ε ≤ 1 / (10 * N) → 0 < d0 →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
        ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (V : Space → Space) (s : ℝ),
          LipschitzStage σ N m ε δ n x v Y V s := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  intro m
  induction m with
  | zero =>
    intro _ ε d0 hε _ hd0
    obtain ⟨δ, hδ, hδd0, hδ100, n, x, v, Y, V, s, hF, hS, hvol, hVm, hVu, hVp, hs, hslo, hshi,
      hcube⟩ := cube_plane_examples hσ hσ2 hbelow habove hTS ε d0 hε hd0
    exact ⟨δ, hδ, hδd0, hδ100, n, x, v, Y, V, s, hF, hS, hvol, hVm, hVu, hVp, hs, hslo, hshi,
      hcube, fun j hj1 hj0 => absurd hj0 (by omega)⟩
  | succ m ih =>
    intro hm ε d0 hε hεN hd0
    have hε10 : ε ≤ 1 / 10 := by
      have : 1 / (10 * (N : ℝ)) ≤ 1 / 10 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
      linarith
    obtain ⟨η, d1, hη, hηε, hd1, hstep⟩ := lipschitz_scale_step hσ hσ2 hTS hε hε10
    obtain ⟨δ, hδ, hδd, hδ100, n, x, v, Y, V, s, hF, hS, hvol, hVm, hVu, hVp, hs, hslo, hshi,
      hcube, hscales⟩ := ih (by omega) η (min d0 d1) hη (hηε.trans hεN) (lt_min hd0 hd1)
    have hδ1 : δ ≤ 1 := by linarith
    have hδd1 : δ ≤ d1 := hδd.trans (min_le_right _ _)
    -- the new scale
    set t := δ ^ (((m + 1 : ℕ) : ℝ) / N) with ht
    have hNpos : (0 : ℝ) < N := by linarith
    have hεN' : ε ≤ 1 / N := by
      calc ε ≤ 1 / (10 * N) := hεN
        _ ≤ 1 / N := div_le_div_of_nonneg_left (by norm_num) hNpos (by linarith)
    have hm1 : (((m + 1 : ℕ) : ℝ)) ≤ N - 1 := by
      have : m + 1 ≤ N - 1 := hm
      have h2 : ((m + 1 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h2; simpa using h2
    have hm0 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have ht1 : δ ^ (1 - ε) ≤ t := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      rw [div_le_iff₀ hNpos]
      have : ε * N ≤ 1 := by rw [le_div_iff₀ hNpos] at hεN'; linarith
      nlinarith
    have ht2 : t ≤ δ ^ ε := by
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      rw [le_div_iff₀ hNpos]
      have : ε * N ≤ 1 := by rw [le_div_iff₀ hNpos] at hεN'; linarith
      linarith
    obtain ⟨Y', hY'Y, hF', ρc, hρc1, hρc2, hvar⟩ := hstep δ hδ hδd1 hδ100 n x v Y V hF hS hvol
      hVm hVu hVp t ht1 ht2
    have hsubU : (⋃ i, Y' i) ⊆ ⋃ i, Y i := iUnion_mono hY'Y
    refine ⟨δ, hδ, hδd.trans (min_le_left _ _), hδ100, n, x, v, Y', V, s, hF',
      hS.mono_error hδ hδ1 hηε, ?_, hVm, fun p hp => hVu p (hsubU hp),
      fun i p hp => hVp i p (hY'Y i hp), hs, hslo, hshi, hcube, ?_⟩
    · exact (measure_mono hsubU).trans (hvol.trans (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))))
    · intro j hj1 hjm
      rcases Nat.lt_or_ge j (m + 1) with hlt | hge
      · obtain ⟨ρ, hρ1, hρ2, hρv⟩ := hscales j hj1 (by omega)
        refine ⟨ρ, hρ1, hρ2.trans (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)), ?_⟩
        intro p hp q hq hpq
        exact hρv p (hsubU hp) q (hsubU hq) hpq
      · have hj : j = m + 1 := by omega
        subst hj
        refine ⟨ρc, hρc1, ?_, hvar⟩
        calc ρc ≤ δ ^ (-ε) * t := hρc2
          _ = δ ^ (((m + 1 : ℕ) : ℝ) / N - ε) := by
              rw [ht, ← Real.rpow_add hδ]; ring_nf

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **Extremal examples with a Lipschitz plane map** (sticky Lemma 4.8): arbitrarily small
`ε`-extremal families at a scale `δ` with a measurable plane map of precision `δ`, unit on the
shaded union and `δ ^ (-ε)`-Lipschitz there. -/
theorem lipschitz_plane_examples {σ : ℝ} (hσ : 0 < σ) (hσ2 : σ ≤ 2)
    (hbelow : ∀ t : ℝ, t < σ → Examples t) (habove : ∀ t : ℝ, σ < t → ¬ Examples t)
    (hTS : TwoScaleTheoremP σ) (ε d0 : ℝ) (hε : 0 < ε) (hd0 : 0 < d0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
      ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (V : Space → Space),
        Family ε δ n x v Y ∧ Separated ε δ n x v ∧
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - ε)) ∧
        Measurable V ∧ (∀ p ∈ ⋃ i, Y i, ‖V p‖ = 1) ∧
        (∀ i p, p ∈ Y i → |inner ℝ (v i) (V p)| ≤ δ) ∧
        ∀ p ∈ ⋃ i, Y i, ∀ q ∈ ⋃ i, Y i, dist (V p) (V q) ≤ δ ^ (-ε) * dist p q := by
  classical
  set N : ℕ := ⌈4 / ε⌉₊ + 2 with hNdef
  have hN : 2 ≤ N := by omega
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNinv : 1 / (N : ℝ) ≤ ε / 4 := by
    have h1 : 4 / ε ≤ (N : ℝ) := by
      have := Nat.le_ceil (4 / ε)
      have h2 : ((⌈4 / ε⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (show ⌈4 / ε⌉₊ ≤ N by omega)
      linarith
    rw [div_le_iff₀ hNpos]
    rw [div_le_iff₀ hε] at h1
    linarith
  set ε0 := min (ε / 4) (1 / (10 * N)) with hε0
  have hε00 : 0 < ε0 := lt_min (by positivity) (by positivity)
  have hε0a : ε0 ≤ ε / 4 := min_le_left _ _
  have hε0b : ε0 ≤ 1 / (10 * N) := min_le_right _ _
  have hε0N : ε0 ≤ 1 / N := hε0b.trans (div_le_div_of_nonneg_left (by norm_num) hNpos
    (by linarith))
  obtain ⟨c1, hc1, hcut1⟩ := exists_power_cutoff (a := ε / 2) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 32)
  obtain ⟨c2, hc2, hcut2⟩ := exists_power_cutoff (a := 1 / (N : ℝ)) (by positivity)
    (by norm_num : (0:ℝ) < 1 / 16)
  obtain ⟨δ, hδ, hδd, hδ100, n, x, v, Y, V, s, hF, hS, hvol, hVm, hVu, hVp, hs, hslo, hshi,
    hcube, hscales⟩ := lipschitz_stages hσ hσ2 hbelow habove hTS N hN (N - 1) le_rfl ε0
      (min d0 (min c1 c2)) hε00 hε0b (lt_min hd0 (lt_min hc1 hc2))
  have hδ1 : δ ≤ 1 := by linarith
  have hq1 : δ ^ (ε / 2) ≤ 1 / 32 := hcut1 δ hδ (hδd.trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hq2 : δ ^ (1 / (N : ℝ)) ≤ 1 / 16 := hcut2 δ hδ (hδd.trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  -- parity selection at the cube side
  obtain ⟨c, hc⟩ := exists_heavy_parityClass (massMeasure Y) (⋃ i, Y i) s
  set Y'' : Fin n → Set Space := fun i => Y i ∩ parityClass s c with hY''
  have hYm := hF.2.2.2.2.1
  have hpm := measurableSet_parityClass hs c
  have hmass : ∑ i, volume (Y i) ≤ 8 * ∑ i, volume (Y'' i) := by
    have h1 := hc
    rw [massMeasure_apply hYm (MeasurableSet.iUnion hYm),
      massMeasure_apply hYm ((MeasurableSet.iUnion hYm).inter hpm)] at h1
    have e1 : ∀ i, Y i ∩ ⋃ j, Y j = Y i := fun i => inter_eq_left.2 (subset_iUnion Y i)
    have e2 : ∀ i, Y i ∩ ((⋃ j, Y j) ∩ parityClass s c) = Y'' i := by
      intro i; rw [hY'', ← inter_assoc, e1]
    simp only [e1, e2] at h1
    exact h1
  have hsubU : (⋃ i, Y'' i) ⊆ ⋃ i, Y i := iUnion_mono fun i => inter_subset_left
  -- the scales
  let ρf : ℕ → ℝ := fun j => if h : 1 ≤ j ∧ j ≤ N - 1 then Classical.choose (hscales j h.1 h.2)
    else 1
  have hρf : ∀ j, 1 ≤ j → j ≤ N - 1 → δ ^ ((j : ℝ) / N) ≤ ρf j ∧
      ρf j ≤ δ ^ ((j : ℝ) / N - ε0) ∧
      ∀ p ∈ ⋃ i, Y i, ∀ q ∈ ⋃ i, Y i, dist p q < ρf j / 16 → dist (V p) (V q) < 2 * ρf j := by
    intro j hj1 hj2
    have h := Classical.choose_spec (hscales j hj1 hj2)
    simp only [ρf, dif_pos (And.intro hj1 hj2)]
    exact h
  have hρfpos : ∀ j, 1 ≤ j → j ≤ N - 1 → 0 < ρf j := fun j hj1 hj2 =>
    (Real.rpow_pos_of_pos hδ _).trans_le (hρf j hj1 hj2).1
  -- data for the multi-scale assembly
  let s' : ℕ → ℝ := fun j => if j < N - 1 then ρf (j + 1) / 16 else s
  let r' : ℕ → ℝ := fun j => 2 * ρf (j + 1)
  set L := 32 * δ ^ (-(1 / (N : ℝ) + ε0)) with hL
  have hNsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  -- power identities
  have hpow : ∀ a b : ℝ, δ ^ a * δ ^ b = δ ^ (a + b) := fun a b => (Real.rpow_add hδ a b).symm
  have hs'pos : ∀ j, 0 < s' j := by
    intro j
    simp only [s']
    split_ifs with h
    · exact div_pos (hρfpos (j + 1) (by omega) (by omega)) (by norm_num)
    · exact hs
  have hδs : δ ≤ ρf (N - 1) / 16 := by
    have h1 := (hρf (N - 1) (by omega) le_rfl).1
    have h2 : δ ^ (((N - 1 : ℕ) : ℝ) / N) * δ ^ (1 / (N : ℝ)) = δ := by
      rw [hpow, hNsub]
      have : ((N : ℝ) - 1) / N + 1 / N = 1 := by field_simp; ring
      rw [this, Real.rpow_one]
    have h3 : 0 ≤ δ ^ (((N - 1 : ℕ) : ℝ) / N) := Real.rpow_nonneg hδ.le _
    nlinarith
  have hanti : ∀ j, s' (j + 1) ≤ s' j := by
    intro j
    simp only [s']
    by_cases h1 : j + 1 < N - 1
    · have h0 : j < N - 1 := by omega
      rw [if_pos h1, if_pos h0]
      have ha := (hρf (j + 2) (by omega) (by omega)).2.1
      have hb := (hρf (j + 1) (by omega) (by omega)).1
      have hc' : δ ^ (((j + 2 : ℕ) : ℝ) / N - ε0) ≤ δ ^ (((j + 1 : ℕ) : ℝ) / N) := by
        apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
        push_cast
        have : ((j : ℝ) + 2) / N - ε0 - ((j : ℝ) + 1) / N = 1 / N - ε0 := by ring
        linarith
      have : ρf (j + 1 + 1) ≤ ρf (j + 1) := by
        have e : j + 1 + 1 = j + 2 := rfl
        rw [e]; linarith
      linarith
    · rw [if_neg h1]
      by_cases h0 : j < N - 1
      · rw [if_pos h0]
        have hj : j + 1 = N - 1 := by omega
        rw [hj]; linarith
      · rw [if_neg h0]
  have hscale : ∀ j < N - 1, ∀ p ∈ ⋃ i, Y'' i, ∀ q ∈ ⋃ i, Y'' i, dist p q < s' j →
      dist (V p) (V q) ≤ r' j := by
    intro j hj p hp q hq hpq
    simp only [s', if_pos hj] at hpq
    exact ((hρf (j + 1) (by omega) (by omega)).2.2 p (hsubU hp) q (hsubU hq) hpq).le
  have hfin : ∀ p ∈ ⋃ i, Y'' i, ∀ q ∈ ⋃ i, Y'' i, dist p q < s' (N - 1) → V p = V q := by
    intro p hp q hq hpq
    simp only [s', lt_irrefl, if_false] at hpq
    obtain ⟨i, hi⟩ := mem_iUnion.1 hp
    obtain ⟨j, hj⟩ := mem_iUnion.1 hq
    exact hcube p q (cubeIndex_eq_of_parity hs hi.2 hj.2 hpq)
  have hbig : ∀ p ∈ ⋃ i, Y'' i, ∀ q ∈ ⋃ i, Y'' i, dist (V p) (V q) ≤ 2 := by
    intro p hp q hq
    calc dist (V p) (V q) ≤ ‖V p‖ + ‖V q‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
      _ = 2 := by rw [hVu p (hsubU hp), hVu q (hsubU hq)]; norm_num
  have hLpos : 0 ≤ L := by positivity
  have hLs : ∀ ρ a : ℝ, δ ^ a ≤ ρ → 2 * δ ^ (a - 1 / (N : ℝ) - ε0) ≤ L * (ρ / 16) := by
    intro ρ a hρ
    have e : L * (ρ / 16) = 2 * (δ ^ (-(1 / (N : ℝ) + ε0)) * ρ) := by rw [hL]; ring
    rw [e]
    have : δ ^ (a - 1 / (N : ℝ) - ε0) = δ ^ (-(1 / (N : ℝ) + ε0)) * δ ^ a := by
      rw [hpow]; ring_nf
    rw [this]
    have hp : 0 ≤ δ ^ (-(1 / (N : ℝ) + ε0)) := Real.rpow_nonneg hδ.le _
    nlinarith
  have hL0 : 2 ≤ L * s' 0 := by
    have h0 : 0 < N - 1 := by omega
    simp only [s', if_pos h0]
    have h1 := hLs (ρf 1) ((1 : ℕ) / (N : ℝ)) (by exact_mod_cast (hρf 1 le_rfl (by omega)).1)
    have h2 : (1 : ℝ) ≤ δ ^ ((((1 : ℕ) : ℝ) / N) - 1 / (N : ℝ) - ε0) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1
      push_cast; linarith
    push_cast at h1 h2
    linarith
  have hLj : ∀ j < N - 1, r' j ≤ L * s' (j + 1) := by
    intro j hj
    simp only [r', s']
    by_cases h1 : j + 1 < N - 1
    · rw [if_pos h1]
      have h2 := hLs (ρf (j + 1 + 1)) (((j + 2 : ℕ) : ℝ) / N)
        (by have := (hρf (j + 2) (by omega) (by omega)).1; exact this)
      have h3 := (hρf (j + 1) (by omega) (by omega)).2.1
      have e : ((j + 2 : ℕ) : ℝ) / N - 1 / (N : ℝ) - ε0 = ((j + 1 : ℕ) : ℝ) / N - ε0 := by
        push_cast; ring
      rw [e] at h2
      linarith
    · rw [if_neg h1]
      have hj1 : j + 1 = N - 1 := by omega
      rw [hj1]
      have h3 := (hρf (N - 1) (by omega) le_rfl).2.1
      have h2 := hLs (16 * s) 1 (by rw [Real.rpow_one]; linarith)
      have e : (1 : ℝ) - 1 / N - ε0 = ((N - 1 : ℕ) : ℝ) / N - ε0 := by
        rw [hNsub]; field_simp
      rw [e] at h2
      have : L * (16 * s / 16) = L * s := by ring
      linarith
  have hlip := lipschitz_of_scales V (⋃ i, Y'' i) s' r' (N - 1) L hs'pos hanti hscale hfin hbig
    hL0 hLj hLpos
  -- the Lipschitz constant
  have hLε : L ≤ δ ^ (-ε) := by
    have e : δ ^ (-ε) = δ ^ (-(ε - 1 / (N : ℝ) - ε0)) * δ ^ (-(1 / (N : ℝ) + ε0)) := by
      rw [hpow]; ring_nf
    have h1 : δ ^ (ε - 1 / (N : ℝ) - ε0) ≤ 1 / 32 :=
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans hq1
    have h2 : 32 ≤ δ ^ (-(ε - 1 / (N : ℝ) - ε0)) := by
      rw [Real.rpow_neg hδ.le]
      have hp : 0 < δ ^ (ε - 1 / (N : ℝ) - ε0) := Real.rpow_pos_of_pos hδ _
      rw [le_inv_comm₀ (by norm_num) hp]
      linarith
    rw [e, hL]
    have hp : 0 ≤ δ ^ (-(1 / (N : ℝ) + ε0)) := Real.rpow_nonneg hδ.le _
    nlinarith
  refine ⟨δ, hδ, hδd.trans (min_le_left _ _), hδ100, n, x, v, Y'', V, ?_,
    hS.mono_error hδ hδ1 (by linarith), ?_, hVm, fun p hp => hVu p (hsubU hp),
    fun i p hp => hVp i p hp.1, ?_⟩
  · refine ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, fun i => (hYm i).inter hpm,
      fun i => inter_subset_left.trans (hF.2.2.2.2.2.1 i), ?_⟩
    have h1 := hF.2.2.2.2.2.2
    have hq : δ ^ ε * (n : ℝ) * δ ^ 2 * 8 ≤ δ ^ ε0 * (n : ℝ) * δ ^ 2 := by
      have e : δ ^ ε = δ ^ (ε - ε0) * δ ^ ε0 := by rw [hpow]; ring_nf
      have h2 : δ ^ (ε - ε0) ≤ 1 / 8 :=
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)).trans (hq1.trans (by norm_num))
      rw [e]
      have : 0 ≤ δ ^ ε0 * (n : ℝ) * δ ^ 2 := by positivity
      nlinarith
    have h8 : ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) * 8 ≤ ∑ i, volume (Y i) := by
      calc ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2) * 8
          = ENNReal.ofReal (δ ^ ε * (n : ℝ) * δ ^ 2 * 8) := by
            rw [ENNReal.ofReal_mul' (by norm_num : (0:ℝ) ≤ 8)]; norm_num
        _ ≤ ENNReal.ofReal (δ ^ ε0 * (n : ℝ) * δ ^ 2) := ENNReal.ofReal_le_ofReal hq
        _ ≤ _ := h1
    have h9 := h8.trans hmass
    rw [mul_comm (8 : ℝ≥0∞)] at h9
    exact (ENNReal.mul_le_mul_iff_left (by norm_num) (by norm_num)).1 h9
  · exact (measure_mono hsubU).trans (hvol.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))))
  · intro p hp q hq
    exact (hlip p hp q hq).trans (mul_le_mul_of_nonneg_right hLε dist_nonneg)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
