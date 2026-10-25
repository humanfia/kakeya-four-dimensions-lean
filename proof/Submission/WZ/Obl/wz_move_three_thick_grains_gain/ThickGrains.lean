-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_three_thick_grains_gain.ThickGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_three_thick_grains_gain.Box
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.NeighborhoodPowers
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.DenseGrains
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.RegularShading
import Submission.WZ.Obl.wz_tube_packing_bound

set_option linter.unusedVariables false

/-!
# Step 1 of WZ Lemma 8.3 (and 8.2): thick grains give a power gain

`thick_grains_gain`: under `E σ ω`, for `b ∈ (0,1]`, every admissible family at a small error `h`
with any frozen cover `C` and frozen grains `H` whose thickness satisfies `2 δ^(1-b) ≤ a`
has union volume at least `κ δ^(ω - bω/2) (nδ²)(nδ)^(-σ)`.

Taken from session x0423's `ThickGrains.lean` on o153 (branch x0423 of o153, commit 28b8eeb),
rehomed into this namespace. Route (same as x0409's o122 `thick_grains_gain`): keep the
individually dense grains (`dense_individual_refinement`), take a regular half of each at
radius `δ^(1-b)/2` (`convex_regular_subshading_finite`, with the box-ball volume bound
`volume_P_inter_ball`), transfer to the fine shadings (`grain_refinement_transfer`), and apply
the frozen Corollary 5.19 `neighborhood_power_gain`. All four tools are from accepted o095;
the tube count bound is accepted o037.
-/

noncomputable section

namespace WangZahlLot.Obl.wz_move_three_thick_grains_gain

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (assignedFiber fiberBodyCount
  fiberBodyCount_eq_ncard grain_refinement_transfer dense_individual_refinement
  convex_regular_subshading_finite)

theorem ofReal_half : (1 / 2 : ℝ≥0∞) = O (1 / 2 : ℝ) := by
  norm_num [O, ENNReal.ofReal_div_of_pos]

/-- `δ ≤ t^(1/p)` gives `δ^p ≤ t`. -/
theorem rpow_le_of_le_root {δ t p : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) (hp : 0 < p)
    (h : δ ≤ t ^ (1 / p)) : δ ^ p ≤ t := by
  calc δ ^ p ≤ (t ^ (1 / p)) ^ p := Real.rpow_le_rpow hδ h hp.le
    _ = t := by rw [← Real.rpow_mul ht, one_div_mul_cancel hp.ne', Real.rpow_one]

theorem root_pos {t p : ℝ} (ht : 0 < t) : 0 < t ^ (1 / p) := Real.rpow_pos_of_pos ht _

theorem scalar_r6 {δ b : ℝ} (hδ : 0 < δ) (hδb : δ ^ b ≤ 1 / 6) : δ ≤ δ ^ (1 - b) / 6 := by
  have hδbpos : 0 < δ ^ b := Real.rpow_pos_of_pos hδ b
  rw [Real.rpow_sub hδ, Real.rpow_one, div_div, le_div_iff₀ (by positivity)]
  have : δ * (δ ^ b * 6) ≤ δ * 1 := mul_le_mul_of_nonneg_left (by linarith) hδ.le
  linarith

theorem scalar_r8 {δ r : ℝ} (hδ : 0 < δ) (h18 : δ ≤ 1 / 8) (hr6 : δ ≤ r) :
    δ ^ (2 : ℕ) ≤ r / 8 := by
  have : δ * δ ≤ r * (1 / 8) := mul_le_mul hr6 h18 hδ.le (hδ.le.trans hr6)
  nlinarith

theorem scalar_eta {δ η ν : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hνη : ν ≤ η)
    (hδη : δ ^ η ≤ 1 / 128) : 128 * (δ ^ (2 : ℕ)) ^ η ≤ δ ^ ν := by
  have hsq : (δ ^ (2 : ℕ)) ^ η = δ ^ η * δ ^ η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, ← Real.rpow_add hδ]
    ring_nf
  have hpos : 0 ≤ δ ^ η := (Real.rpow_pos_of_pos hδ η).le
  have hνle : δ ^ η ≤ δ ^ ν := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hνη
  rw [hsq]
  calc 128 * (δ ^ η * δ ^ η) = (128 * δ ^ η) * δ ^ η := by ring
    _ ≤ 1 * δ ^ η := mul_le_mul_of_nonneg_right (by linarith) hpos
    _ ≤ δ ^ ν := by linarith

theorem scalar_nmax {δ C₀ : ℝ} {n : ℕ} (hδ : 0 < δ) (hC₀ : 0 < C₀) (hn : (0 : ℝ) < n)
    (hp : (n : ℝ) * δ ^ 4 ≤ C₀) (hδ196 : δ ^ (196 : ℝ) ≤ 1 / C₀) :
    (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) := by
  have hδ4 : 0 < δ ^ (4 : ℕ) := by positivity
  have h196 : 0 < δ ^ (196 : ℝ) := Real.rpow_pos_of_pos hδ _
  have hδ196' : δ ^ (196 : ℝ) * C₀ ≤ 1 := by
    rw [le_div_iff₀ hC₀] at hδ196
    linarith
  have hrw : (δ ^ (2 : ℕ)) ^ (-100 : ℝ) = (δ ^ (196 : ℝ) * δ ^ (4 : ℕ))⁻¹ := by
    have h1 : (δ ^ (2 : ℕ)) ^ (-100 : ℝ) = δ ^ (-200 : ℝ) := by
      rw [← Real.rpow_natCast δ 2, ← Real.rpow_mul hδ.le]; norm_num
    have h2 : δ ^ (196 : ℝ) * δ ^ (4 : ℕ) = δ ^ (200 : ℝ) := by
      rw [← Real.rpow_natCast δ 4, ← Real.rpow_add hδ]; norm_num
    rw [h1, h2, Real.rpow_neg hδ.le]
  rw [hrw, le_inv_comm₀ hn (by positivity), inv_eq_one_div, le_div_iff₀ hn]
  have : δ ^ (196 : ℝ) * δ ^ (4 : ℕ) * n = δ ^ (196 : ℝ) * (n * δ ^ 4) := by ring
  rw [this]
  calc δ ^ (196 : ℝ) * (n * δ ^ 4) ≤ δ ^ (196 : ℝ) * C₀ := mul_le_mul_of_nonneg_left hp h196.le
    _ ≤ 1 := hδ196'

theorem scalar_mass {δ h ν : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhν : h ≤ ν / 4) (hh0 : 0 ≤ h)
    (hδν2 : δ ^ (ν / 2) ≤ 1 / 8) : δ ^ ν ≤ 1 / 4 / 2 * (δ ^ h * δ ^ h) := by
  have hν2h : δ ^ (ν / 2) ≤ δ ^ (2 * h) := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hsplitν : δ ^ ν = δ ^ (ν / 2) * δ ^ (ν / 2) := by
    rw [← Real.rpow_add hδ]; ring_nf
  have h2h : δ ^ h * δ ^ h = δ ^ (2 * h) := by rw [← Real.rpow_add hδ]; ring_nf
  rw [hsplitν, h2h]
  have hp : 0 ≤ δ ^ (ν / 2) := (Real.rpow_pos_of_pos hδ _).le
  calc δ ^ (ν / 2) * δ ^ (ν / 2) ≤ (1 / 8) * δ ^ (2 * h) := mul_le_mul hδν2 hν2h hp (by norm_num)
    _ = 1 / 4 / 2 * δ ^ (2 * h) := by norm_num

theorem scalar_density {δ h ν : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhν : h ≤ ν / 4) (hν0 : 0 < ν)
    (hδ5ν : δ ^ (5 * ν) ≤ 1 / 256000) : δ ^ (6 * ν) ≤ δ ^ h / 256000 := by
  have hsp : δ ^ (6 * ν) = δ ^ (5 * ν) * δ ^ ν := by
    rw [← Real.rpow_add hδ]; ring_nf
  have hνh : δ ^ ν ≤ δ ^ h := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hp : 0 ≤ δ ^ ν := (Real.rpow_pos_of_pos hδ _).le
  rw [hsp]
  calc δ ^ (5 * ν) * δ ^ ν ≤ (1 / 256000) * δ ^ h := mul_le_mul hδ5ν hνh hp (by norm_num)
    _ = δ ^ h / 256000 := by ring

/-- WZ Lemma 8.2/8.3, Step 1: grains of thickness at least `2δ^(1-b)` give a power gain.
Any frozen cover `C` (with any trailing proposition) and frozen grains `H` (any length bound,
any local coefficient) at a small error `h` suffice. -/
theorem thick_grains_gain {σ ω : ℝ} (hσ : 0 ≤ σ) (hσ2 : σ ≤ 1 / 2) (hω : 0 < ω) (hE : E σ ω)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ κ h₀ d₀ : ℝ, 0 < κ ∧ 0 < h₀ ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
    ∀ δ h : ℝ, 0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ h₀ →
    ∀ (n : ℕ) (x v : Fin n → V) (Y : Fin n → Set V), A δ h (δ ^ (-h)) (δ ^ (-h)) n x v Y →
    ∀ (S : Finset (Fin n)) (Z : Fin n → Set V) (ρ : ℝ) (N : ℕ) (y w : Fin N → V)
      (f : Fin n → Fin N) (bb : Prop), C δ h n x v Y S Z ρ N y w f bb →
    ∀ a c b' g : ℝ, H δ h n x v S Z ρ N y w f a c b' g → 2 * δ ^ (1 - b) ≤ a →
    O (κ * δ ^ (ω - b * ω / 2) * (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ μ (⋃ i, Y i) := by
  obtain ⟨κ, η, d₁, hκ, hη, hd₁, hd₁small, NPG⟩ :=
    WangZahlLot.Obl.wz_clustered_cover_volume_gain.neighborhood_power_gain hσ hσ2 hω hE
      (b * ω / 8) (by positivity)
  obtain ⟨C₀, hC₀, hpack⟩ := WangZahlLot.wz_tube_packing_bound
  set ν : ℝ := min η (b * ω / 56) with hν
  have hν0 : 0 < ν := lt_min hη (by positivity)
  have hνη : ν ≤ η := min_le_left _ _
  have hνb : ν ≤ b * ω / 56 := min_le_right _ _
  have hC₀' : 0 < min 1 (1 / C₀) := lt_min one_pos (by positivity)
  set t₁ : ℝ := (1 / 6 : ℝ) ^ (1 / b)
  set t₂ : ℝ := (1 / 128 : ℝ) ^ (1 / η)
  set t₃ : ℝ := (min 1 (1 / C₀)) ^ (1 / (196 : ℝ))
  set t₄ : ℝ := (1 / 256000 : ℝ) ^ (1 / (5 * ν))
  set t₅ : ℝ := (1 / 8 : ℝ) ^ (1 / (ν / 2))
  set d₀ : ℝ := min (min (1 / 100) d₁) (min (min t₁ t₂) (min t₃ (min t₄ t₅))) with hd₀
  have hd₀pos : 0 < d₀ :=
    lt_min (lt_min (by norm_num) hd₁) (lt_min (lt_min (root_pos (by norm_num))
      (root_pos (by norm_num))) (lt_min (root_pos hC₀') (lt_min (root_pos (by norm_num))
        (root_pos (by norm_num)))))
  refine ⟨κ, ν / 4, d₀, hκ, by positivity, hd₀pos, (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  intro δ h hδ hδd₀ hh0 hhν n x v Y hA S Z ρ N y w f bb hC a c b' g hH ha
  -- smallness of δ
  have hδ100 : δ ≤ 1 / 100 := hδd₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδ100.trans (by norm_num)
  have hδd₁ : δ ≤ d₁ := hδd₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδt₁ : δ ≤ t₁ := hδd₀.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδt₂ : δ ≤ t₂ := hδd₀.trans ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδt₃ : δ ≤ t₃ := hδd₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδt₄ : δ ≤ t₄ := hδd₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hδt₅ : δ ≤ t₅ := hδd₀.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hδb : δ ^ b ≤ 1 / 6 := rpow_le_of_le_root hδ.le (by norm_num) hb hδt₁
  have hδη : δ ^ η ≤ 1 / 128 := rpow_le_of_le_root hδ.le (by norm_num) hη hδt₂
  have hδ196 : δ ^ (196 : ℝ) ≤ min 1 (1 / C₀) :=
    rpow_le_of_le_root hδ.le hC₀'.le (by norm_num) hδt₃
  have hδ5ν : δ ^ (5 * ν) ≤ 1 / 256000 := rpow_le_of_le_root hδ.le (by norm_num) (by positivity) hδt₄
  have hδν2 : δ ^ (ν / 2) ≤ 1 / 8 := rpow_le_of_le_root hδ.le (by norm_num) (by positivity) hδt₅
  -- unpack the cover and the grains
  obtain ⟨hZ, hZmass, hw, hTsub, hF, hbb, hbal, hX, hmultC⟩ := hC
  obtain ⟨L, z, e, Hg, γ, m, hda, hab, hbc, hc1, hgeom, hdisj, hunion, hmass, hmult, hcross,
    hb'c, hcount⟩ := hH
  set s : ℝ := δ ^ (1 - b) / 2 with hs
  have hs0 : 0 < s := by positivity
  have has : 4 * s ≤ a := by rw [hs]; linarith
  have ha0 : 0 < a := by linarith
  have hρc0 : 0 < ρ * c := lt_of_lt_of_le ha0 hab
  have hc0 : 0 < c := lt_of_lt_of_le hρc0 hbc
  set U : Fin L → Set V := fun j => P a (ρ * c) c (z j) (e j) with hU
  have hUvol : ∀ j, volume (U j) = O (a * (ρ * c) * c) := fun j =>
    volume_P ha0.le hρc0.le hc0.le (z j) (e j)
  have hHm : ∀ j, MeasurableSet (Hg j) := fun j => (hgeom j).1
  have hHU : ∀ j, Hg j ⊆ U j := fun j => (hgeom j).2.1
  have hHfin : (∑ j, volume (Hg j)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro j _
    exact ne_top_of_le_ne_top (by rw [hUvol]; exact ENNReal.ofReal_ne_top) (measure_mono (hHU j))
  -- Step A: keep the individually dense grains
  have hbudget : (∑ j, O (δ ^ h / 2) * volume (U j)) ≤
      (1 / 2 : ℝ≥0∞) * ∑ j, volume (Hg j) := by
    simp only [hUvol]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc (L : ℝ≥0∞) * (O (δ ^ h / 2) * O (a * (ρ * c) * c))
        = (1 / 2 : ℝ≥0∞) * O (δ ^ h * L * a * (ρ * c) * c) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ofReal_half, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
      _ ≤ (1 / 2 : ℝ≥0∞) * ∑ j, volume (Hg j) := mul_le_mul' le_rfl hmass
  obtain ⟨W, hW, hWmass, hWdense⟩ := dense_individual_refinement Hg U hHm hHfin hbudget
  -- Step B: a regular half of each dense grain
  have hreg : ∀ j, ∃ Hp : Set V, MeasurableSet Hp ∧ Hp ⊆ W j ∧
      (1 / 2 : ℝ≥0∞) * volume (W j) ≤ volume Hp ∧
      ∀ p ∈ Hp, O (δ ^ h / 2 / 16000) * volume (U j ∩ ball p s) ≤ volume (Hp ∩ ball p s) := by
    intro j
    by_cases hWj : W j = ∅
    · exact ⟨∅, MeasurableSet.empty, empty_subset _, by simp [hWj], fun p hp => hp.elim⟩
    · obtain ⟨Z', hZ'm, hZ'W, hZ'mass, hZ'reg⟩ :=
        convex_regular_subshading_finite
          (convex_P a (ρ * c) c (z j) (e j)) (measurableSet_P a (ρ * c) c (z j) (e j))
          (totallyBounded_P a (ρ * c) c (z j) (e j)) (by rw [hUvol]; exact ENNReal.ofReal_ne_top)
          (hW j).1 ((hW j).2.trans (hHU j)) (lam := δ ^ h / 2) (by positivity) (hWdense j hWj)
          (k := 1) one_pos (fun _ => s) (fun _ => hs0)
      exact ⟨Z', hZ'm, hZ'W, hZ'mass, fun p hp => by simpa using hZ'reg p hp 0⟩
  choose Hp hHpm hHpW hHpmass hHpreg using hreg
  -- Step C: transfer the refinement to the fine shadings
  have hZm : ∀ i, MeasurableSet (Z i) := fun i => (hZ i).1
  have hZempty : ∀ i, i ∉ S → Z i = ∅ := fun i hi => (hZ i).2.2 hi
  have hmemS : ∀ i p, p ∈ Z i → i ∈ S := by
    intro i p hp
    by_contra hiS
    rw [hZempty i hiS] at hp
    exact hp
  have heq : ∀ k, assignedFiber γ Hg k = assignedFiber f Z k := by
    intro k
    ext p
    simp only [assignedFiber, mem_ofPred_eq]
    have hk := congrArg (fun A : Set V => p ∈ A) (hunion k)
    simp only [mem_ofPred_eq, eq_iff_iff] at hk
    rw [hk]
    constructor
    · rintro ⟨i, _, hik, hpi⟩
      exact ⟨i, hik, hpi⟩
    · rintro ⟨i, hik, hpi⟩
      exact ⟨i, hmemS i p hpi, hik, hpi⟩
  have hlevel : ∀ k p, p ∈ assignedFiber f Z k →
      m ≤ fiberBodyCount f Z k p ∧ fiberBodyCount f Z k p ≤ 2 * m := by
    intro k p hp
    obtain ⟨i, hik, hpi⟩ := hp
    have h := hmult k p ⟨i, hmemS i p hpi, hik, hpi⟩
    rw [fiberBodyCount_eq_ncard]
    have hsets : {i' : Fin n | f i' = k ∧ p ∈ Z i'} = {i' | i' ∈ S ∧ f i' = k ∧ p ∈ Z i'} := by
      ext i'
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hmemS i' p h2, h1, h2⟩
      · rintro ⟨_, h1, h2⟩
        exact ⟨h1, h2⟩
    rw [hsets]
    exact h
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hA.1
  have hYmass : O (δ ^ h * n * δ ^ 2) ≤ ∑ i, μ (Y i) := hA.2.2.2.1
  have hm : 0 ≤ m := by
    by_contra hneg
    have hneg' := not_le.mp hneg
    have hall : ∀ i, Z i = ∅ := by
      intro i
      by_cases hiS : i ∈ S
      · ext p
        simp only [mem_empty_iff_false, iff_false]
        intro hp
        have h := hmult (f i) p ⟨i, hiS, rfl, hp⟩
        have h2 := h.1.trans h.2
        linarith
      · exact hZempty i hiS
    have hsum0 : ∑ i ∈ S, μ (Z i) = 0 := by simp [hall]
    rw [hsum0] at hZmass
    have hpos1 : (0 : ℝ≥0∞) < O (δ ^ h) := ENNReal.ofReal_pos.mpr (by positivity)
    have hpos2 : (0 : ℝ≥0∞) < ∑ i, μ (Y i) :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) hYmass
    exact absurd hZmass (not_le.mpr (ENNReal.mul_pos hpos1.ne' hpos2.ne'))
  have hretain : O (1 / 4) * ∑ j, volume (Hg j) ≤ ∑ j, volume (Hp j) := by
    have hquarter : O (1 / 4) = (1 / 2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) := by
      rw [ofReal_half, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    calc O (1 / 4) * ∑ j, volume (Hg j)
        = (1 / 2 : ℝ≥0∞) * ((1 / 2 : ℝ≥0∞) * ∑ j, volume (Hg j)) := by
          rw [hquarter, mul_assoc]
      _ ≤ (1 / 2 : ℝ≥0∞) * ∑ j, volume (W j) := mul_le_mul' le_rfl hWmass
      _ = ∑ j, (1 / 2 : ℝ≥0∞) * volume (W j) := Finset.mul_sum _ _ _
      _ ≤ ∑ j, volume (Hp j) := Finset.sum_le_sum fun j _ => hHpmass j
  obtain ⟨W', hW'm, hW'mass, hW'fib⟩ := grain_refinement_transfer f γ Z Hg Hp hm
    (by norm_num : (0 : ℝ) ≤ 1 / 4) hZm hHm hHpm (fun j => (hHpW j).trans (hW j).2)
    hdisj heq hlevel hretain
  -- Step D: the neighbourhood power gain
  have hδ2 : δ ^ (2 : ℕ) ≤ δ := pow_le_of_le_one hδ.le hδ1 two_ne_zero
  have hr6 : δ ≤ δ ^ (1 - b) / 6 := scalar_r6 hδ hδb
  have hr8 : δ ^ (2 : ℕ) ≤ (δ ^ (1 - b) / 6) / 8 := scalar_r8 hδ (hδ100.trans (by norm_num)) hr6
  have hηq : 128 * (δ ^ (2 : ℕ)) ^ η ≤ δ ^ ν := scalar_eta hδ hδ1 hνη hδη
  have hbud : 7 * ν + 2 * (b * ω / 8) + h ≤ b * ω / 2 := by
    have : 0 < b * ω := by positivity
    linarith
  have hnmax : (n : ℝ) ≤ (δ ^ (2 : ℕ)) ^ (-100 : ℝ) :=
    scalar_nmax hδ hC₀ hnpos
      (hpack δ hδ hδ100 n x v (fun i => (hA.2.1 i).1) (fun i => (hA.2.1 i).2.1) hA.2.2.1)
      (hδ196.trans (min_le_right _ _))
  have hWY : ∀ i, MeasurableSet (W' i) ∧ W' i ⊆ Y i :=
    fun i => ⟨(hW'm i).1, (hW'm i).2.trans (hZ i).2.1⟩
  have hmassW : O (δ ^ ν * n * δ ^ 2) ≤ ∑ i, volume (W' i) := by
    have hZS : ∑ i ∈ S, volume (Z i) ≤ ∑ i, volume (Z i) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ S)
    have hchain : O (1 / 4 / 2) * (O (δ ^ h) * O (δ ^ h * n * δ ^ 2)) ≤ ∑ i, volume (W' i) :=
      calc O (1 / 4 / 2) * (O (δ ^ h) * O (δ ^ h * n * δ ^ 2))
          ≤ O (1 / 4 / 2) * (O (δ ^ h) * ∑ i, μ (Y i)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hYmass)
        _ ≤ O (1 / 4 / 2) * ∑ i ∈ S, volume (Z i) := mul_le_mul' le_rfl hZmass
        _ ≤ O (1 / 4 / 2) * ∑ i, volume (Z i) := mul_le_mul' le_rfl hZS
        _ ≤ _ := hW'mass
    refine le_trans ?_ hchain
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hkey : δ ^ ν ≤ 1 / 4 / 2 * (δ ^ h * δ ^ h) := scalar_mass hδ hδ1 hhν hh0 hδν2
    have hnd : 0 ≤ (n : ℝ) * δ ^ 2 := by positivity
    calc δ ^ ν * n * δ ^ 2 = δ ^ ν * (n * δ ^ 2) := by ring
      _ ≤ 1 / 4 / 2 * (δ ^ h * δ ^ h) * (n * δ ^ 2) := mul_le_mul_of_nonneg_right hkey hnd
      _ = 1 / 4 / 2 * (δ ^ h * (δ ^ h * n * δ ^ 2)) := by ring
  have hdensity : ∀ i p, p ∈ W' i → O (δ ^ (6 * ν) * (δ ^ (1 - b) / 2) ^ 3) ≤
      volume ((⋃ i, Y i) ∩ ball p (δ ^ (1 - b) / 2)) := by
    intro i p hp
    have hpf : p ∈ assignedFiber f W' (f i) := ⟨i, rfl, hp⟩
    rw [hW'fib] at hpf
    obtain ⟨j, hj, hpj⟩ := hpf
    have hHpY : Hp j ⊆ ⋃ i, Y i := by
      intro q hq
      have hqH : q ∈ Hg j := (hW j).2 (hHpW j hq)
      have hq' : q ∈ assignedFiber γ Hg (γ j) := ⟨j, rfl, hqH⟩
      rw [heq] at hq'
      obtain ⟨i', _, hqi'⟩ := hq'
      exact mem_iUnion.mpr ⟨i', (hZ i').2.1 hqi'⟩
    have hpU : p ∈ U j := hHU j ((hW j).2 (hHpW j hpj))
    have hball := volume_P_inter_ball hs0 (by linarith) (by linarith) (by linarith) hpU
    have hreg := hHpreg j p hpj
    calc O (δ ^ (6 * ν) * (δ ^ (1 - b) / 2) ^ 3)
        ≤ O (δ ^ h / 2 / 16000) * O (s ^ 3 / 8) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          have h6 : δ ^ (6 * ν) ≤ δ ^ h / 256000 := scalar_density hδ hδ1 hhν hν0 hδ5ν
          have hs3 : 0 ≤ s ^ 3 := by positivity
          calc δ ^ (6 * ν) * (δ ^ (1 - b) / 2) ^ 3 = δ ^ (6 * ν) * s ^ 3 := by rw [hs]
            _ ≤ δ ^ h / 256000 * s ^ 3 := mul_le_mul_of_nonneg_right h6 hs3
            _ = δ ^ h / 2 / 16000 * (s ^ 3 / 8) := by ring
      _ ≤ O (δ ^ h / 2 / 16000) * volume (U j ∩ ball p s) := mul_le_mul' le_rfl hball
      _ ≤ volume (Hp j ∩ ball p s) := hreg
      _ ≤ volume ((⋃ i, Y i) ∩ ball p (δ ^ (1 - b) / 2)) :=
          measure_mono (inter_subset_inter hHpY (le_of_eq rfl))
  exact NPG δ h b ν hδ hδ1 hh0 hb.le hb1 (hδ2.trans hδd₁) hr6 hr8 hηq hbud n x v Y W'
    hnmax hA hWY hmassW hdensity

end WangZahlLot.Obl.wz_move_three_thick_grains_gain
