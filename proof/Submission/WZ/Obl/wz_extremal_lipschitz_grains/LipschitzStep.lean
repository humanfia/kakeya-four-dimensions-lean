-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.LipschitzStep.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TwoScaleUse
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.MultiScaleLipschitz

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- **One Lipschitz step from two-scale data** (sticky Lemma 4.5 + Corollary 4.6, unpacked).
The `β`-level cover (`z0, w0` at radius `ρ0`, separation, fibre bound `B1` for `Y1 ⊇ Y2`) gives
robust transversality; the `ρ`-level data (coarse labels `a`, directions `w` within `ρc/2`, grid of
side `s ≥ ρc/16`, contraction `lam`, bounds `A`, `B`, `Cc`) give the cube structure.  The result is
a set `E'` carrying a fixed fraction of the mass of `Y2` on which the plane map varies by less than
`2 ρc` between points closer than `s / lam`. -/
theorem lipschitz_step {n k k1 : ℕ} {δ ρ0 ρc s lam A B1 Bf Cc : ℝ}
    {x v : Fin n → Space} {Y1 Y2 : Fin n → Set Space} (hv : ∀ i, ‖v i‖ = 1)
    (hY2 : ∀ i, MeasurableSet (Y2 i)) (hY2T : ∀ i, Y2 i ⊆ tube δ (x i) (v i))
    (hY21 : ∀ i, Y2 i ⊆ Y1 i)
    {V : Space → Space} (hVm : Measurable V) (hVu : ∀ p ∈ ⋃ i, Y2 i, ‖V p‖ = 1)
    (hVp : ∀ i p, p ∈ Y2 i → |inner ℝ (v i) (V p)| ≤ δ)
    -- β-level cover data
    {a1 : Fin n → Fin k1} {z0 w0 : Fin k1 → Space} (hw0 : ∀ j, ‖w0 j‖ = 1)
    (hδρ0 : δ ≤ ρ0) (hδ : 0 < δ)
    (hcov1 : ∀ i, (Y1 i).Nonempty → tube δ (x i) (v i) ⊆ tube ρ0 (z0 (a1 i)) (w0 (a1 i)))
    (hsep1 : ∀ i j j', tube δ (x i) (v i) ⊆ dilatedTube ρ0 (z0 j) (w0 j) →
      tube δ (x i) (v i) ⊆ dilatedTube ρ0 (z0 j') (w0 j') → j = j')
    (hfib1 : ∀ j p, ({i | a1 i = j ∧ p ∈ Y1 i}.ncard : ℝ) ≤ B1)
    -- ρ-level data
    {a : Fin n → Fin k} {w : Fin k → Space} (hw : ∀ j, ‖w j‖ = 1) {Yt : Fin k → Set Space}
    {M : Fin k → Finset (Fin 3 → ℤ)} (hs : 0 < s) (hlam : 0 < lam)
    (hYt : ∀ j, Yt j = ⋃ m ∈ M j, gridCube s m) (hcontr : ∀ i, lam • Y2 i ⊆ Yt (a i))
    (hdir : ∀ i, (Y2 i).Nonempty → min ‖v i - w (a i)‖ ‖v i + w (a i)‖ ≤ ρc / 2)
    (hA : ∀ p ∈ ⋃ i, Y2 i, A ≤ (fineMult Y2 p : ℝ))
    (hfib : ∀ j p, ({i | a i = j ∧ p ∈ Y2 i}.ncard : ℝ) ≤ Bf)
    (hCc : ∀ q, (fineMult Yt q : ℝ) ≤ Cc)
    -- scale relations
    (hρc : 0 < ρc) (hρcρ0 : ρc < ρ0) (hB1A : 0 ≤ B1 ∧ B1 ≤ A / 2) (hA0 : 0 < A) (hBf : 0 ≤ Bf)
    (hCc0 : 0 ≤ Cc) (hBf1 : 1 ≤ Bf) :
    ∃ E' : Set Space, MeasurableSet E' ∧ E' ⊆ ⋃ i, Y2 i ∧
      ENNReal.ofReal (A ^ 2 / (2 * (⌈Bf⌉₊ : ℝ) ^ 2)) * massMeasure Y2 (⋃ i, Y2 i) ≤
        (8 * ((8 * ⌊Cc⌋₊) ^ 2 * (2 * (⌊2 * (4 * (δ + ρc / 2) / ((ρ0 - 2 * (ρc / 2)) / 2)) /
          ρc⌋₊ + 3) ^ 3)) : ℕ) * massMeasure Y2 E' ∧
      ∀ p ∈ E', ∀ q ∈ E', dist p q < s / lam → dist (V p) (V q) < 2 * ρc := by
  classical
  set sL := s / lam with hsL
  have hsL0 : 0 < sL := div_pos hs hlam
  have hfit : lam * sL = s := by rw [hsL]; field_simp
  -- active labels per fine cube
  have hCcN : ∀ c, (Finset.univ.filter fun j => c ∈ M j).card ≤ ⌊Cc⌋₊ := by
    intro c
    exact Nat.le_floor (card_labels_le hs hYt hCc c)
  have hact : ∀ m, ∃ Act : Finset (Fin k), Act.card ≤ 8 * ⌊Cc⌋₊ ∧
      ∀ p ∈ gridCube sL m, ∀ i ∈ through Y2 p, a i ∈ Act :=
    fun m => card_act_le hs hsL0 hlam hfit.le hYt hcontr hCcN m
  choose Act hActc hAct using hact
  -- fibre bound as a natural number
  have hBN : ∀ j p, ((through Y2 p).filter fun i => a i = j).card ≤ ⌈Bf⌉₊ := by
    intro j p
    have h1 := hfib j p
    rw [ncard_fibre_eq] at h1
    exact_mod_cast h1.trans (Nat.le_ceil Bf)
  have hBN1 : 1 ≤ ⌈Bf⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  -- robust transversality
  have hcone : ∀ p, ∀ i ∈ through Y2 p, (((through Y2 p).filter fun l =>
      min ‖v l - v i‖ ‖v l + v i‖ ≤ ρ0).card : ℝ) ≤ (through Y2 p).card / 2 := by
    intro p i hi
    have hpY : p ∈ ⋃ i, Y2 i := mem_iUnion.2 ⟨i, mem_through.1 hi⟩
    have hfib2 : ∀ j q, ({l | a1 l = j ∧ q ∈ Y2 l}.ncard : ℝ) ≤ B1 := by
      intro j q
      have hsub : {l | a1 l = j ∧ q ∈ Y2 l} ⊆ {l | a1 l = j ∧ q ∈ Y1 l} :=
        fun l hl => ⟨hl.1, hY21 l hl.2⟩
      have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h4 : ({l | a1 l = j ∧ q ∈ Y2 l}.ncard : ℝ) ≤ ({l | a1 l = j ∧ q ∈ Y1 l}.ncard : ℝ) := by
        exact_mod_cast h3
      exact h4.trans (hfib1 j q)
    have h1 := cone_count_le hδ hδρ0 hv hw0 hY2T
      (fun i hi => hcov1 i (hi.mono (hY21 i))) hsep1 hfib2 hB1A.1 p (v i) (hv i)
    rw [ncard_cone_eq] at h1
    have h2 := hA p hpY
    rw [fineMult_eq_card_through] at h2
    linarith [hB1A.2]
  -- direction closeness in the orientation of `lipschitz_one_scale`
  have hdir' : ∀ i, (Y2 i).Nonempty → min ‖w (a i) - v i‖ ‖w (a i) + v i‖ ≤ ρc / 2 := by
    intro i hi
    rw [norm_sub_rev, add_comm]; exact hdir i hi
  have hmult : ∀ p ∈ ⋃ i, Y2 i, A ≤ ((through Y2 p).card : ℝ) := by
    intro p hp; rw [← fineMult_eq_card_through]; exact hA p hp
  obtain ⟨E', hE'm, hE'sub, hmass, hcube⟩ := lipschitz_one_scale (massMeasure Y2) hY2 hv hw hVm hVu
    (e₀ := δ) (d₀ := ρc / 2) (β := ρ0) (s := sL) (r := ρc) (A := A) (B := ⌈Bf⌉₊)
    (Cact := 8 * ⌊Cc⌋₊) hsL0 hρc (by linarith) hA0 hδ.le (by linarith) hVp hdir' hmult
    hcone hBN hBN1 Act hAct hActc
  -- parity selection
  obtain ⟨c, hc⟩ := exists_heavy_parityClass (massMeasure Y2) E' sL
  refine ⟨E' ∩ parityClass sL c, hE'm.inter (measurableSet_parityClass hsL0 c),
    inter_subset_left.trans hE'sub, ?_, ?_⟩
  · calc ENNReal.ofReal (A ^ 2 / (2 * (⌈Bf⌉₊ : ℝ) ^ 2)) * massMeasure Y2 (⋃ i, Y2 i)
        ≤ _ * massMeasure Y2 E' := hmass
      _ ≤ _ * (8 * massMeasure Y2 (E' ∩ parityClass sL c)) := by gcongr
      _ = _ := by push_cast; ring
  · intro p hp q hq hpq
    exact hcube p hp.1 q hq.1 (cubeIndex_eq_of_parity hsL0 hp.2 hq.2 hpq)

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
