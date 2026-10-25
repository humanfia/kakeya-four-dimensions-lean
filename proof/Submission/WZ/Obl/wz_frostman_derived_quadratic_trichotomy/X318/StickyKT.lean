-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyKT.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.StickyIterate
-- Copied from session x0338 (o070 branch, commit ec01e52, file StickyKT.lean), namespace renamed.

/-!
# The Katz–Tao end of the sticky branch

After the level iteration (`iterate_levels`) every level-`k` cell of the refined set `S₁` lies in a
Katz–Tao set with constant `c k`.  `sticky_allScales_of_refined` removes the thin cells with x0305's
`threshold_prune` (threshold `⌊2^(a k) δ^e⌋`) and applies x0305's `allScales_of_prepared`: the
result is the frozen all-scales condition `AllScales ξ` on a set keeping a `1/(2 M₁)` share.
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- A natural number at least `1` and at least `⌊X⌋` is at least `X / 2`. -/
lemma half_le_of_floor_le {X : ℝ} {p : ℕ} (hp : 1 ≤ p) (hfl : ⌊X⌋₊ ≤ p) :
    X / 2 ≤ p := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hfl' : (⌊X⌋₊ : ℝ) ≤ p := by exact_mod_cast hfl
  have h1 := Nat.lt_floor_add_one X
  rcases le_or_gt 2 X with h2 | h2
  · linarith
  · linarith

/-- The cells of `S` at a level where every cell holds at least `2^a` points number at most
`|S| / 2^a`. -/
lemma card_image_mul_le {ι α : Type*} [DecidableEq ι] [DecidableEq α] (S : Finset ι) (κ : ι → α)
    (a : ℕ) (hlow : ∀ i ∈ S, 2 ^ a ≤ pop S κ i) :
    (S.image κ).card * 2 ^ a ≤ S.card := by
  classical
  rw [Finset.card_eq_sum_card_image κ S, Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  apply Finset.sum_le_sum
  intro c hc
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
  exact hlow i hi

open Classical in
/-- **Sticky branch, Katz–Tao end.**  Let `S` be prepared at the levels `k ≤ top`
(`ρ k = 2 δ L^k`): common classes, populations in `[2^(a k), 2^(a k + 1))`, `K`-Frostman.  Let
`S₁ ⊆ S` keep a `1/M₁` share and have every level-`k` cell inside a set that is Katz–Tao with
constant `c k`.  If `2 M₁ (top + 1) δ^e ≤ 1`, `4 δ^(-e) ≤ δ^(-ξ)`, `2 K M₁ ≤ δ^(-ξ)` and
`c k ρ_k² ≤ δ^(-ξ) (2^(a k) δ^e / 2) δ²`, then a set `S₂ ⊆ S₁` keeping a `1/(2 M₁)` share of `S`
satisfies `AllScales ξ`. -/
theorem sticky_allScales_of_refined {δ ξ e K M₁ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hξ : 0 < ξ)
    (hK : 0 ≤ K) (hM₁ : 0 < M₁)
    {L top : ℕ} (hL : 2 ≤ L) (hratio : (L : ℝ) ≤ δ ^ (-ξ)) (htwo : (2 : ℝ) ≤ δ ^ (-ξ))
    (htop1 : 2 * δ * (L : ℝ) ^ top ≤ 1 / 10000) (htop2 : δ ^ ξ ≤ 2 * δ * (L : ℝ) ^ top)
    {m : ℕ} (x v : Fin m → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hT : ∀ i, Tube δ (x i) (v i) ⊆ Metric.ball 0 1)
    (hcan : ∀ i, x i = WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.leftStart δ (x i) (v i)) (hanti : ∀ i j, 1 ≤ ‖v i + v j‖)
    (a : ℕ → ℕ) (S : Finset (Fin m))
    (hcls : ∀ k ≤ top, ∀ i ∈ S, ∀ i' ∈ S, classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i) (v i) =
      classKey 200000 (2 * δ * (L : ℝ) ^ k) (x i') (v i'))
    (hpopS : ∀ k ≤ top, ∀ i ∈ S,
      2 ^ a k ≤ pop S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i ∧
      pop S (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i < 2 ^ (a k + 1))
    (hFS : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((S.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) ≤
        ENNReal.ofReal (K * S.card) * volume W)
    (S₁ : Finset (Fin m)) (hS₁S : S₁ ⊆ S) (hcard₁ : (S.card : ℝ) ≤ M₁ * S₁.card)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hgood : ∀ k ≤ top, ∀ i ∈ S₁, ∃ F' : Finset (Fin m),
      fibre S₁ (fun i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i)) i ⊆ F' ∧
      ∀ W : Set Space, Convex ℝ W →
        ENNReal.ofReal (((F'.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ) * δ ^ 2) ≤
          ENNReal.ofReal (c k) * volume W)
    (hsmall : 2 * M₁ * (((top : ℝ) + 1) * δ ^ e) ≤ 1)
    (hbalc : 4 * δ ^ (-e) ≤ δ ^ (-ξ)) (hKM : 2 * K * M₁ ≤ δ ^ (-ξ))
    (hcρ : ∀ k ≤ top, c k * (2 * δ * (L : ℝ) ^ k) ^ 2 ≤
      δ ^ (-ξ) * ((2 : ℝ) ^ a k * δ ^ e / 2) * δ ^ 2)
    (hSne : S.Nonempty) :
    ∃ S₂ ⊆ S₁, S₂.Nonempty ∧ (S.card : ℝ) ≤ 2 * M₁ * S₂.card ∧
      AllScales ξ δ (fun j => x (S₂.equivFin.symm j).1) (fun j => v (S₂.equivFin.symm j).1) := by
  classical
  set κ : ℕ → Fin m → (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
    fun k i => lineCell (2 * δ * (L : ℝ) ^ k / 20) (x i) (v i) with hκ
  have hL0 : 0 < L := by omega
  have hnest : ∀ j k, j ≤ k → ∀ i i', κ j i = κ j i' → κ k i = κ k i' := by
    intro j k hjk i i' h
    have hm : 0 < L ^ (k - j) := pow_pos hL0 _
    have hs : 0 < 2 * δ * (L : ℝ) ^ j / 20 := by positivity
    have e : 2 * δ * (L : ℝ) ^ k / 20 = ((L ^ (k - j) : ℕ) : ℝ) * (2 * δ * (L : ℝ) ^ j / 20) := by
      push_cast
      rw [show k = j + (k - j) by omega, pow_add]
      simp only [Nat.add_sub_cancel_left]
      ring
    simp only [hκ]
    rw [e]
    exact lineCell_nest hs hm h
  -- thresholds
  set t : ℕ → ℕ := fun k => ⌊(2 : ℝ) ^ a k * δ ^ e⌋₊ with ht
  obtain ⟨S₂, hS₂S₁, hthr, hcard₂⟩ := threshold_prune (top + 1) κ hnest t S₁
  -- the removed mass is small
  have hrem : ∀ k ∈ Finset.range (top + 1), (((S₁.image (κ k)).card * t k : ℕ) : ℝ) ≤
      S.card * δ ^ e := by
    intro k hk
    have hk' : k ≤ top := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have himg : (S₁.image (κ k)).card ≤ (S.image (κ k)).card :=
      Finset.card_le_card (Finset.image_subset_image hS₁S)
    have hcells : ((S.image (κ k)).card : ℝ) * 2 ^ a k ≤ S.card := by
      have := card_image_mul_le S (κ k) (a k) (fun i hi => (hpopS k hk' i hi).1)
      exact_mod_cast this
    have htk : (t k : ℝ) ≤ 2 ^ a k * δ ^ e := Nat.floor_le (by positivity)
    rw [Nat.cast_mul]
    calc ((S₁.image (κ k)).card : ℝ) * t k ≤ (S.image (κ k)).card * (2 ^ a k * δ ^ e) :=
          mul_le_mul (by exact_mod_cast himg) htk (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = ((S.image (κ k)).card * 2 ^ a k) * δ ^ e := by ring
      _ ≤ S.card * δ ^ e := mul_le_mul_of_nonneg_right hcells (by positivity)
  have hsum : ((∑ k ∈ Finset.range (top + 1), (S₁.image (κ k)).card * t k : ℕ) : ℝ) ≤
      ((top : ℝ) + 1) * (S.card * δ ^ e) := by
    rw [Nat.cast_sum]
    calc ∑ k ∈ Finset.range (top + 1), (((S₁.image (κ k)).card * t k : ℕ) : ℝ)
        ≤ ∑ _k ∈ Finset.range (top + 1), (S.card * δ ^ e : ℝ) :=
          Finset.sum_le_sum (fun k hk => hrem k hk)
      _ = ((top : ℝ) + 1) * (S.card * δ ^ e) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hS₂big : (S.card : ℝ) ≤ 2 * M₁ * S₂.card := by
    have h1 : (S₁.card : ℝ) ≤ S₂.card + ((top : ℝ) + 1) * (S.card * δ ^ e) := by
      have := hcard₂
      have h' : (S₁.card : ℝ) ≤ (S₂.card : ℝ) +
          ((∑ k ∈ Finset.range (top + 1), (S₁.image (κ k)).card * t k : ℕ) : ℝ) := by
        exact_mod_cast this
      linarith
    have hX : 2 * M₁ * (((top : ℝ) + 1) * (S.card * δ ^ e)) ≤ S.card := by
      calc 2 * M₁ * (((top : ℝ) + 1) * (S.card * δ ^ e))
          = (2 * M₁ * (((top : ℝ) + 1) * δ ^ e)) * S.card := by ring
        _ ≤ 1 * S.card := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)
        _ = S.card := one_mul _
    have h5 := mul_le_mul_of_nonneg_left h1 hM₁.le
    nlinarith
  have hS₂ne : S₂.Nonempty := by
    rw [← Finset.card_pos]
    have hSpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hSne
    have : (0 : ℝ) < S₂.card := by
      by_contra h0
      push Not at h0
      have : (S.card : ℝ) ≤ 0 := by nlinarith
      linarith
    exact_mod_cast this
  have hS₂S : S₂ ⊆ S := hS₂S₁.trans hS₁S
  -- final populations are at least `2^(a k) δ^e / 2`
  have hpop₂ : ∀ k ≤ top, ∀ i ∈ S₂, (2 : ℝ) ^ a k * δ ^ e / 2 ≤ pop S₂ (κ k) i := by
    intro k hk i hi
    exact half_le_of_floor_le (pop_pos hi) (hthr k (by omega) i hi)
  refine ⟨S₂, hS₂S₁, hS₂ne, hS₂big, ?_⟩
  have hN : 0 < top + 1 := Nat.succ_pos _
  refine allScales_of_prepared hδ hδ1 hξ hL hN hratio htwo (by simpa using htop1)
    (by simpa using htop2) x v hv hT hcan hanti S₂ hS₂ne ?_ ?_ ?_ ?_
  · intro k hk i hi i' hi'
    exact hcls k (by omega) i (hS₂S hi) i' (hS₂S hi')
  · intro k hk i hi i' hi'
    have hk' : k ≤ top := by omega
    have hup : (pop S₂ (κ k) i : ℝ) ≤ 2 ^ (a k + 1) := by
      have h1 : pop S₂ (κ k) i ≤ pop S (κ k) i :=
        Finset.card_le_card (Finset.filter_subset_filter _ hS₂S)
      have h2 := (hpopS k hk' i (hS₂S hi)).2
      have : pop S₂ (κ k) i < 2 ^ (a k + 1) := lt_of_le_of_lt h1 h2
      exact_mod_cast this.le
    have hlow := hpop₂ k hk' i' hi'
    have he' : δ ^ (-e) * δ ^ e = 1 := by
      rw [← Real.rpow_add hδ]; simp
    have heq : (4 * δ ^ (-e)) * (2 ^ a k * δ ^ e / 2) = (2 : ℝ) ^ (a k + 1) := by
      calc (4 * δ ^ (-e)) * (2 ^ a k * δ ^ e / 2) = 2 * 2 ^ a k * (δ ^ (-e) * δ ^ e) := by ring
        _ = (2 : ℝ) ^ (a k + 1) := by rw [he', pow_succ]; ring
    calc (pop S₂ (κ k) i : ℝ) ≤ 2 ^ (a k + 1) := hup
      _ = (4 * δ ^ (-e)) * (2 ^ a k * δ ^ e / 2) := heq.symm
      _ ≤ δ ^ (-ξ) * pop S₂ (κ k) i' := by
          gcongr
  · intro k hk i₀ hi₀ W hW
    have hk' : k ≤ top := by omega
    obtain ⟨F', hF', hKT⟩ := hgood k hk' i₀ (hS₂S₁ hi₀)
    have := fibre_frostman_of_katzTao x v S₂ F' (κ k) i₀ hδ (hc k)
      (fun i hi hκi => hF' (Finset.mem_filter.mpr ⟨hS₂S₁ hi, hκi⟩)) hKT
      (hpop₂ k hk' i₀ hi₀) (hcρ k hk') W hW
    exact this
  · intro W hW
    have hF₂ := frostman_of_subset x v S S₂ hS₂S hK hS₂big hFS W hW
    calc ENNReal.ofReal ((S₂.filter (fun i => Tube δ (x i) (v i) ⊆ W)).card : ℝ)
        ≤ ENNReal.ofReal ((K * (2 * M₁)) * S₂.card) * volume W := hF₂
      _ ≤ ENNReal.ofReal (δ ^ (-ξ) * S₂.card) * volume W := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
          calc K * (2 * M₁) = 2 * K * M₁ := by ring
            _ ≤ δ ^ (-ξ) := hKM

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
