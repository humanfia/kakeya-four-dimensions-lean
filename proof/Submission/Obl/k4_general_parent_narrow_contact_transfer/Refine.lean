/- Retained from this obligation, o255, branch x0901 at commit 0f8ba410.
   Earlier source attributions in this file are preserved. -/
import Submission.Obl.k4_general_parent_narrow_contact_transfer.VelocityCap

/-!
# Refining a projected-layer output to a finer mesh

A projected-layer output at the mesh `χ₀ = N^(-m₀)` is refined to the finer
mesh `χ = N^(-m)` by splitting every assignment along the fine velocity and
intercept bins, keeping only fine velocity bins inside one coarse bin, and
deleting fine assignments below their new floor.  The interval width `β`, the
predictors and the subsequence are unchanged.  The fine floors of one coarse
assignment sum to at most `3 χ₀ π(coarse bin)` times the old reference
factor, so light fine assignments cost little; lines in fine velocity bins
straddling a coarse boundary are negligible by the velocity cap when
`m₀ < S m`.

Consequently ordinary projected preparation may always be requested at a
moderate mesh and refined.
-/

namespace Submission.Obl.k4_general_parent_narrow_contact_transfer

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Model

/-- A fine bin `[j χ, (j+1) χ)` lies inside one coarse bin of width `χ₀`. -/
def goodBin (χ χ₀ : ℝ) (j : ℤ) : Prop := ((j : ℝ) + 1) * χ ≤ (⌊(j : ℝ) * χ / χ₀⌋ + 1) * χ₀

theorem floor_coarse_of_goodBin {χ χ₀ x : ℝ} (hχ : 0 < χ) (hχ₀ : 0 < χ₀) {j : ℤ}
    (hj : ⌊x / χ⌋ = j) (hg : goodBin χ χ₀ j) : ⌊x / χ₀⌋ = ⌊(j : ℝ) * χ / χ₀⌋ := by
  rw [Int.floor_eq_iff] at hj ⊢
  obtain ⟨h1, h2⟩ := hj
  have hx1 : (j : ℝ) * χ ≤ x := by rwa [le_div_iff₀ hχ] at h1
  have hx2 : x < ((j : ℝ) + 1) * χ := by rwa [div_lt_iff₀ hχ] at h2
  set J := ⌊(j : ℝ) * χ / χ₀⌋ with hJ
  have hJ1 : (J : ℝ) ≤ (j : ℝ) * χ / χ₀ := Int.floor_le _
  have hJ1' : (J : ℝ) * χ₀ ≤ (j : ℝ) * χ := by rwa [le_div_iff₀ hχ₀] at hJ1
  constructor
  · rw [le_div_iff₀ hχ₀]; linarith
  · rw [div_lt_iff₀ hχ₀]
    unfold goodBin at hg
    rw [← hJ] at hg
    linarith

variable {α : Type} [MeasurableSpace α]

section Construction

variable (cfg : Model α) (τ : ℕ → ℕ) (m₀ m : ℝ) (n' : ℕ → ℝ → ℕ)
  (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
  (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
  (β : ℕ → ℝ → ℝ) (H₁ : ℕ → ℝ)

/-- The fine mesh at index `k`. -/
def χf (k : ℕ) : ℝ := cfg.N (τ k) ^ (-m)

/-- The coarse mesh at index `k`. -/
def χc (k : ℕ) : ℝ := cfg.N (τ k) ^ (-m₀)

open Classical in
/-- Fine velocity bins of a coarse assignment: inside its coarse velocity bin. -/
def fset0 (k : ℕ) (s : ℝ) (i : Fin (n' k s)) : Finset ℤ :=
  (Finset.Icc ⌊(tag k s i 0 : ℝ) * χc cfg τ m₀ k / χf cfg τ m k⌋
      ⌊((tag k s i 0 : ℝ) + 1) * χc cfg τ m₀ k / χf cfg τ m k⌋).filter
    (fun j => goodBin (χf cfg τ m k) (χc cfg τ m₀ k) j ∧
      ⌊(j : ℝ) * χf cfg τ m k / χc cfg τ m₀ k⌋ = tag k s i 0)

/-- Fine intercept bins of a coarse assignment. -/
def fset1 (k : ℕ) (s : ℝ) (i : Fin (n' k s)) : Finset ℤ :=
  Finset.Icc ⌊(tag k s i 1 : ℝ) * χc cfg τ m₀ k / χf cfg τ m k⌋
    ⌊((tag k s i 1 : ℝ) + 1) * χc cfg τ m₀ k / χf cfg τ m k⌋

/-- A fine piece of a coarse assignment. -/
def fine (k : ℕ) (s : ℝ) (x : Fin (n' k s) × ℤ × ℤ) : Set α :=
  C k s x.1 ∩ {l | ⌊cfg.b (τ k) l 3 / χf cfg τ m k⌋ = x.2.1 ∧
    ⌊cfg.b (τ k) l 0 / χf cfg τ m k⌋ = x.2.2}

/-- The new floor of a fine piece. -/
def floorVal (k : ℕ) (s : ℝ) (j₀ : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (χf cfg τ m k * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k) *
    cfg.π (τ k) {w : ℝ | ⌊w / χf cfg τ m k⌋ = j₀}

/-- Candidate fine indices. -/
def cand (k : ℕ) (s : ℝ) : Finset (Fin (n' k s) × ℤ × ℤ) :=
  Finset.univ.biUnion fun i =>
    (fset0 cfg τ m₀ m n' tag k s i ×ˢ fset1 cfg τ m₀ m n' tag k s i).image fun jj => (i, jj)

open Classical in
/-- Retained fine indices. -/
def rIdx (k : ℕ) (s : ℝ) : Finset (Fin (n' k s) × ℤ × ℤ) :=
  (cand cfg τ m₀ m n' tag k s).filter fun x =>
    floorVal cfg τ m β H₁ k s x.2.1 ≤
      cfg.ρ (τ k) (fine cfg τ m n' C k s x ×ˢ Icc (0 : ℝ) 1)

/-- Number of retained fine pieces. -/
def rN (k : ℕ) (s : ℝ) : ℕ := (rIdx cfg τ m₀ m n' C tag β H₁ k s).card

/-- Enumeration of retained fine pieces. -/
def rE (k : ℕ) (s : ℝ) (i : Fin (rN cfg τ m₀ m n' C tag β H₁ k s)) :
    Fin (n' k s) × ℤ × ℤ :=
  ((rIdx cfg τ m₀ m n' C tag β H₁ k s).equivFin.symm i).1

theorem rE_mem (k : ℕ) (s : ℝ) (i : Fin (rN cfg τ m₀ m n' C tag β H₁ k s)) :
    rE cfg τ m₀ m n' C tag β H₁ k s i ∈ rIdx cfg τ m₀ m n' C tag β H₁ k s :=
  ((rIdx cfg τ m₀ m n' C tag β H₁ k s).equivFin.symm i).2

theorem rE_injective (k : ℕ) (s : ℝ) :
    Function.Injective (rE cfg τ m₀ m n' C tag β H₁ k s) := by
  intro i i' h
  have := Subtype.ext h
  exact (rIdx cfg τ m₀ m n' C tag β H₁ k s).equivFin.symm.injective this

theorem rE_surj (k : ℕ) (s : ℝ) (x : Fin (n' k s) × ℤ × ℤ)
    (hx : x ∈ rIdx cfg τ m₀ m n' C tag β H₁ k s) :
    ∃ i, rE cfg τ m₀ m n' C tag β H₁ k s i = x :=
  ⟨(rIdx cfg τ m₀ m n' C tag β H₁ k s).equivFin ⟨x, hx⟩, by simp [rE]⟩

theorem fine_disjoint (k : ℕ) (s : ℝ) (hC : ∀ i i', i ≠ i' → Disjoint (C k s i) (C k s i'))
    {x y : Fin (n' k s) × ℤ × ℤ} (hxy : x ≠ y) :
    Disjoint (fine cfg τ m n' C k s x) (fine cfg τ m n' C k s y) := by
  rw [Set.disjoint_left]
  rintro l ⟨hlx, hx0, hx1⟩ ⟨hly, hy0, hy1⟩
  by_cases h1 : x.1 = y.1
  · apply hxy
    ext
    · exact congrArg Fin.val h1
    · rw [← hx0, ← hy0]
    · rw [← hx1, ← hy1]
  · exact Set.disjoint_left.mp (hC _ _ h1) hlx hly

theorem fine_measurable (k : ℕ) (s : ℝ) (hb : Measurable (cfg.b (τ k)))
    (hC : ∀ i, MeasurableSet (C k s i)) (x : Fin (n' k s) × ℤ × ℤ) :
    MeasurableSet (fine cfg τ m n' C k s x) := by
  refine (hC x.1).inter (MeasurableSet.inter ?_ ?_)
  · exact ((((measurable_pi_apply 3).comp hb).div_const _).floor) (measurableSet_singleton _)
  · exact ((((measurable_pi_apply 0).comp hb).div_const _).floor) (measurableSet_singleton _)

/-- The fine floors of one coarse assignment sum to at most three coarse
reference factors. -/
theorem sum_floorVal_le (k : ℕ) (s : ℝ) (i : Fin (n' k s))
    (hχ : 0 < χf cfg τ m k) (hχχ : χf cfg τ m k ≤ χc cfg τ m₀ k)
    (hc : 0 ≤ (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k) :
    ∑ j₀ ∈ fset0 cfg τ m₀ m n' tag k s i, ∑ _j₁ ∈ fset1 cfg τ m₀ m n' tag k s i,
        floorVal cfg τ m β H₁ k s j₀ ≤
      ENNReal.ofReal (3 * χc cfg τ m₀ k * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k) *
        cfg.π (τ k) {w : ℝ | ⌊w / χc cfg τ m₀ k⌋ = tag k s i 0} := by
  classical
  have hχ₀ : 0 < χc cfg τ m₀ k := lt_of_lt_of_le hχ hχχ
  set χ := χf cfg τ m k
  set χ₀ := χc cfg τ m₀ k
  set c := χ * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k
  have hcnn : 0 ≤ c := by
    have : c = χ * ((cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k) := by simp only [c]; ring
    rw [this]; exact mul_nonneg hχ.le hc
  -- the fine velocity bins are disjoint subsets of the coarse bin
  have hbins : ∑ j₀ ∈ fset0 cfg τ m₀ m n' tag k s i, cfg.π (τ k) {w : ℝ | ⌊w / χ⌋ = j₀} ≤
      cfg.π (τ k) {w : ℝ | ⌊w / χ₀⌋ = tag k s i 0} := by
    rw [← measure_biUnion_finset]
    · apply measure_mono
      intro w hw
      simp only [mem_iUnion, Finset.mem_coe] at hw
      obtain ⟨j, hj, hwj⟩ := hw
      simp only [fset0, Finset.mem_filter] at hj
      have h := floor_coarse_of_goodBin hχ hχ₀ hwj hj.2.1
      simp only [mem_setOf_eq]
      rw [h, hj.2.2]
    · intro j _ j' _ hjj'
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      intro w hw hw'
      exact hjj' (hw.symm.trans hw')
    · intro j _
      exact (measurable_id.div_const χ).floor (measurableSet_singleton j)
  have hcard : ((fset1 cfg τ m₀ m n' tag k s i).card : ℝ) ≤ χ₀ / χ + 2 := by
    simp only [fset1, Int.card_Icc]
    set lo := ⌊(tag k s i 1 : ℝ) * χ₀ / χ⌋
    set hi := ⌊((tag k s i 1 : ℝ) + 1) * χ₀ / χ⌋
    have hlo : (tag k s i 1 : ℝ) * χ₀ / χ - 1 < lo := Int.sub_one_lt_floor _
    have hhi : (hi : ℝ) ≤ ((tag k s i 1 : ℝ) + 1) * χ₀ / χ := Int.floor_le _
    have hle : lo ≤ hi := Int.floor_mono (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hχ₀.le) hχ.le)
    have h0 : 0 ≤ hi + 1 - lo := by omega
    have hcast : (((hi + 1 - lo).toNat : ℕ) : ℝ) = (hi : ℝ) + 1 - lo := by
      have h2 : (((hi + 1 - lo).toNat : ℕ) : ℤ) = hi + 1 - lo := Int.toNat_of_nonneg h0
      have h3 : (((hi + 1 - lo).toNat : ℕ) : ℝ) = ((hi + 1 - lo : ℤ) : ℝ) := by exact_mod_cast h2
      rw [h3]; push_cast; ring
    rw [hcast]
    have : ((tag k s i 1 : ℝ) + 1) * χ₀ / χ - (tag k s i 1 : ℝ) * χ₀ / χ = χ₀ / χ := by ring
    linarith
  calc ∑ j₀ ∈ fset0 cfg τ m₀ m n' tag k s i, ∑ _j₁ ∈ fset1 cfg τ m₀ m n' tag k s i,
        floorVal cfg τ m β H₁ k s j₀
      = ∑ j₀ ∈ fset0 cfg τ m₀ m n' tag k s i,
          ((fset1 cfg τ m₀ m n' tag k s i).card : ℝ≥0∞) *
            (ENNReal.ofReal c * cfg.π (τ k) {w : ℝ | ⌊w / χ⌋ = j₀}) := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ = ((fset1 cfg τ m₀ m n' tag k s i).card : ℝ≥0∞) * ENNReal.ofReal c *
          ∑ j₀ ∈ fset0 cfg τ m₀ m n' tag k s i, cfg.π (τ k) {w : ℝ | ⌊w / χ⌋ = j₀} := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ ((fset1 cfg τ m₀ m n' tag k s i).card : ℝ≥0∞) * ENNReal.ofReal c *
          cfg.π (τ k) {w : ℝ | ⌊w / χ₀⌋ = tag k s i 0} := by gcongr
    _ ≤ ENNReal.ofReal (3 * χ₀ * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k) *
          cfg.π (τ k) {w : ℝ | ⌊w / χ₀⌋ = tag k s i 0} := by
        gcongr
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have h3 : ((fset1 cfg τ m₀ m n' tag k s i).card : ℝ) * χ ≤ 3 * χ₀ := by
          have := mul_le_mul_of_nonneg_right hcard hχ.le
          rw [add_mul, div_mul_cancel₀ _ hχ.ne'] at this
          linarith
        have hc' : c = χ * ((cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k) := by
          simp only [c]; ring
        rw [hc', ← mul_assoc]
        have := mul_le_mul_of_nonneg_right h3 hc
        calc _ ≤ 3 * χ₀ * ((cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k) := this
          _ = _ := by ring

/-- A line of a coarse assignment in a good fine velocity bin lies in a
candidate fine piece. -/
theorem mem_cand_of_mem (k : ℕ) (s : ℝ) (i : Fin (n' k s)) {l : α}
    (hχ : 0 < χf cfg τ m k) (hχ₀ : 0 < χc cfg τ m₀ k)
    (hl : l ∈ C k s i)
    (ht0 : ⌊cfg.b (τ k) l 3 / χc cfg τ m₀ k⌋ = tag k s i 0)
    (ht1 : ⌊cfg.b (τ k) l 0 / χc cfg τ m₀ k⌋ = tag k s i 1)
    (hg : goodBin (χf cfg τ m k) (χc cfg τ m₀ k) ⌊cfg.b (τ k) l 3 / χf cfg τ m k⌋) :
    (i, ⌊cfg.b (τ k) l 3 / χf cfg τ m k⌋, ⌊cfg.b (τ k) l 0 / χf cfg τ m k⌋) ∈
        cand cfg τ m₀ m n' tag k s ∧
      l ∈ fine cfg τ m n' C k s
        (i, ⌊cfg.b (τ k) l 3 / χf cfg τ m k⌋, ⌊cfg.b (τ k) l 0 / χf cfg τ m k⌋) := by
  classical
  set χ := χf cfg τ m k
  set χ₀ := χc cfg τ m₀ k
  refine ⟨?_, hl, rfl, rfl⟩
  -- the fine bins lie in the coarse ranges
  have hrange : ∀ (x : ℝ) (T : ℤ), ⌊x / χ₀⌋ = T →
      ⌊x / χ⌋ ∈ Finset.Icc ⌊(T : ℝ) * χ₀ / χ⌋ ⌊((T : ℝ) + 1) * χ₀ / χ⌋ := by
    intro x T hT
    rw [Int.floor_eq_iff] at hT
    have h1 : (T : ℝ) * χ₀ ≤ x := by rw [le_div_iff₀ hχ₀] at hT; linarith [hT.1]
    have h2 : x < ((T : ℝ) + 1) * χ₀ := by rw [div_lt_iff₀ hχ₀] at hT; linarith [hT.2]
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right h1 hχ.le),
      Int.floor_mono (div_le_div_of_nonneg_right h2.le hχ.le)⟩
  simp only [cand, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_product]
  refine ⟨i, (⌊cfg.b (τ k) l 3 / χ⌋, ⌊cfg.b (τ k) l 0 / χ⌋), ⟨?_, ?_⟩, rfl⟩
  · simp only [fset0, Finset.mem_filter]
    refine ⟨hrange _ _ ht0, hg, ?_⟩
    rw [← floor_coarse_of_goodBin hχ hχ₀ rfl hg, ht0]
  · exact hrange _ _ ht1

/-- Lines in fine velocity bins straddling a coarse boundary have small mass. -/
theorem straddle_measure_le (μ₀ : Measure (α × ℝ)) (bb : α → Fin 6 → ℝ)
    {χ χ₀ K c₁ : ℝ} (hχ : 0 < χ) (hχχ : χ ≤ χ₀) (hχ₀1 : χ₀ ≤ 1) (hK : 0 ≤ K)
    (hc₁ : 0 ≤ c₁) (hbound : ∀ᵐ p ∂μ₀, |bb p.1 3| ≤ K)
    (hcap : ∀ j : ℤ, μ₀ {p | ⌊bb p.1 3 / χ⌋ = j} ≤ ENNReal.ofReal c₁) :
    μ₀ {p | ¬ goodBin χ χ₀ ⌊bb p.1 3 / χ⌋} ≤
      ENNReal.ofReal (((2 * K + 5) / χ₀ + 4) * c₁) := by
  classical
  have hχ₀ : 0 < χ₀ := lt_of_lt_of_le hχ hχχ
  set S : Finset ℤ := (Finset.Icc (-⌈K / χ⌉ - 1) ⌈K / χ⌉).filter fun j => ¬ goodBin χ χ₀ j
  have hsub : {p : α × ℝ | ¬ goodBin χ χ₀ ⌊bb p.1 3 / χ⌋} ⊆
      {p | ¬ |bb p.1 3| ≤ K} ∪ ⋃ j ∈ S, {p | ⌊bb p.1 3 / χ⌋ = j} := by
    intro p hp
    by_cases hpK : |bb p.1 3| ≤ K
    · right
      simp only [mem_iUnion]
      refine ⟨⌊bb p.1 3 / χ⌋, ?_, rfl⟩
      simp only [S, Finset.mem_filter]
      exact ⟨floor_div_mem_Icc hχ hpK, hp⟩
    · left; exact hpK
  have hnull : μ₀ {p | ¬ |bb p.1 3| ≤ K} = 0 := ae_iff.mp hbound
  -- count the straddling bins through the coarse boundary they contain
  have hcard : (S.card : ℝ) ≤ (2 * K + 5) / χ₀ + 4 := by
    let B : ℤ → ℤ := fun j => ⌊(j : ℝ) * χ / χ₀⌋ + 1
    have hmaps : ∀ j ∈ S, B j ∈ Finset.Icc (-⌈(K + 3) / χ₀⌉) (⌈(K + 2) / χ₀⌉ + 1) := by
      intro j hj
      simp only [S, Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hlo, hhi⟩, -⟩ := hj
      have hlo' : -(K / χ) - 2 ≤ (j : ℝ) := by
        have := Int.ceil_lt_add_one (K / χ)
        have h' : ((-⌈K / χ⌉ - 1 : ℤ) : ℝ) ≤ j := by exact_mod_cast hlo
        push_cast at h'; linarith
      have hhi' : (j : ℝ) ≤ K / χ + 1 := by
        have := Int.ceil_lt_add_one (K / χ)
        have h' : (j : ℝ) ≤ ⌈K / χ⌉ := by exact_mod_cast hhi
        linarith
      have hjχlo : -(K + 3) ≤ (j : ℝ) * χ := by
        have := mul_le_mul_of_nonneg_right hlo' hχ.le
        rw [sub_mul, neg_mul, div_mul_cancel₀ _ hχ.ne'] at this
        nlinarith
      have hjχhi : (j : ℝ) * χ ≤ K + 2 := by
        have := mul_le_mul_of_nonneg_right hhi' hχ.le
        rw [add_mul, div_mul_cancel₀ _ hχ.ne', one_mul] at this
        nlinarith
      rw [Finset.mem_Icc]
      constructor
      · have h1 : -((K + 3) / χ₀) ≤ (j : ℝ) * χ / χ₀ := by
          rw [← neg_div]; exact div_le_div_of_nonneg_right hjχlo hχ₀.le
        have h2 : -(⌈(K + 3) / χ₀⌉ : ℝ) - 1 < ⌊(j : ℝ) * χ / χ₀⌋ := by
          have := Int.le_ceil ((K + 3) / χ₀)
          have := Int.sub_one_lt_floor ((j : ℝ) * χ / χ₀)
          linarith
        have h3 : -⌈(K + 3) / χ₀⌉ - 1 < ⌊(j : ℝ) * χ / χ₀⌋ := by exact_mod_cast h2
        simp only [B]; omega
      · have h1 : (j : ℝ) * χ / χ₀ ≤ (K + 2) / χ₀ := div_le_div_of_nonneg_right hjχhi hχ₀.le
        have h2 : ⌊(j : ℝ) * χ / χ₀⌋ ≤ ⌈(K + 2) / χ₀⌉ :=
          Int.floor_le_iff.mpr (by linarith [Int.le_ceil ((K + 2) / χ₀)])
        simp only [B]; omega
    have hinj : Set.InjOn B S := by
      intro j hj j' hj' hB
      simp only [S, Finset.coe_filter, mem_ofPred_eq] at hj hj'
      have key : ∀ i : ℤ, ¬ goodBin χ χ₀ i →
          (i : ℝ) * χ < (B i : ℝ) * χ₀ ∧ (B i : ℝ) * χ₀ < ((i : ℝ) + 1) * χ := by
        intro i hi
        unfold goodBin at hi
        push Not at hi
        constructor
        · have := Int.lt_floor_add_one ((i : ℝ) * χ / χ₀)
          simp only [B]; push_cast
          rw [div_lt_iff₀ hχ₀] at this
          linarith
        · simp only [B]; push_cast; linarith
      obtain ⟨h1, h2⟩ := key j hj.2
      obtain ⟨h1', h2'⟩ := key j' hj'.2
      rw [hB] at h1 h2
      have hjj : (j : ℝ) < (j' : ℝ) + 1 := by nlinarith
      have hjj' : (j' : ℝ) < (j : ℝ) + 1 := by nlinarith
      have a1 : j < j' + 1 := by exact_mod_cast hjj
      have a2 : j' < j + 1 := by exact_mod_cast hjj'
      omega
    have hle := Finset.card_le_card_of_injOn B hmaps hinj
    have hI : ((Finset.Icc (-⌈(K + 3) / χ₀⌉) (⌈(K + 2) / χ₀⌉ + 1)).card : ℝ) ≤
        (2 * K + 5) / χ₀ + 4 := by
      rw [Int.card_Icc]
      have h0 : 0 ≤ ⌈(K + 2) / χ₀⌉ + 1 + 1 - -⌈(K + 3) / χ₀⌉ := by
        have := Int.ceil_nonneg (div_nonneg (by linarith : (0:ℝ) ≤ K + 2) hχ₀.le)
        have := Int.ceil_nonneg (div_nonneg (by linarith : (0:ℝ) ≤ K + 3) hχ₀.le)
        omega
      have hcast : (((⌈(K + 2) / χ₀⌉ + 1 + 1 - -⌈(K + 3) / χ₀⌉).toNat : ℕ) : ℝ) =
          (⌈(K + 2) / χ₀⌉ : ℝ) + 2 + ⌈(K + 3) / χ₀⌉ := by
        have h2 : (((⌈(K + 2) / χ₀⌉ + 1 + 1 - -⌈(K + 3) / χ₀⌉).toNat : ℕ) : ℤ) =
            ⌈(K + 2) / χ₀⌉ + 1 + 1 - -⌈(K + 3) / χ₀⌉ := Int.toNat_of_nonneg h0
        have h3 : (((⌈(K + 2) / χ₀⌉ + 1 + 1 - -⌈(K + 3) / χ₀⌉).toNat : ℕ) : ℝ) =
            ((⌈(K + 2) / χ₀⌉ + 1 + 1 - -⌈(K + 3) / χ₀⌉ : ℤ) : ℝ) := by exact_mod_cast h2
        rw [h3]; push_cast; ring
      rw [hcast]
      have := Int.ceil_lt_add_one ((K + 2) / χ₀)
      have := Int.ceil_lt_add_one ((K + 3) / χ₀)
      have : (K + 2) / χ₀ + (K + 3) / χ₀ = (2 * K + 5) / χ₀ := by ring
      linarith
    exact (Nat.cast_le.mpr hle).trans hI
  calc μ₀ {p | ¬ goodBin χ χ₀ ⌊bb p.1 3 / χ⌋}
      ≤ μ₀ ({p | ¬ |bb p.1 3| ≤ K} ∪ ⋃ j ∈ S, {p | ⌊bb p.1 3 / χ⌋ = j}) := measure_mono hsub
    _ ≤ μ₀ {p | ¬ |bb p.1 3| ≤ K} + μ₀ (⋃ j ∈ S, {p | ⌊bb p.1 3 / χ⌋ = j}) :=
        measure_union_le _ _
    _ ≤ 0 + ∑ j ∈ S, μ₀ {p | ⌊bb p.1 3 / χ⌋ = j} := by
        rw [hnull]; exact add_le_add le_rfl (measure_biUnion_finset_le _ _)
    _ ≤ 0 + ∑ _j ∈ S, ENNReal.ofReal c₁ := by gcongr with j hj; exact hcap j
    _ = ENNReal.ofReal ((S.card : ℝ) * c₁) := by
        rw [zero_add, Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (((2 * K + 5) / χ₀ + 4) * c₁) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hc₁)

end Construction

/-- Prior-a.e. statements hold for almost every incidence. -/
theorem ae_mu_of_ae_nu (cfg : Model α) (hv : Valid cfg) (k : ℕ) {P : α → Prop}
    (h : ∀ᵐ l ∂cfg.ν k, P l) : ∀ᵐ p ∂cfg.μ k, P p.1 := by
  obtain ⟨-, -, -, hμK, -⟩ := hv.basic k
  rw [ae_iff] at h ⊢
  have hnull : ((cfg.ν k).prod volume) ({l | ¬ P l} ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod, h, zero_mul]
  have hle := hμK ({l | ¬ P l} ×ˢ (univ : Set ℝ))
  rw [Measure.smul_apply, hnull, smul_zero] at hle
  have hsub' : {p : α × ℝ | ¬ P p.1} ⊆ {l | ¬ P l} ×ˢ (univ : Set ℝ) :=
    fun p hp => ⟨hp, mem_univ _⟩
  exact measure_mono_null hsub' (le_antisymm hle zero_le)

theorem ae_abs_b3_le (cfg : Model α) (hv : Valid cfg) (k : ℕ) :
    ∀ᵐ p ∂cfg.μ k, |cfg.b k p.1 3| ≤ cfg.K k := by
  obtain ⟨-, -, -, -, -, -, -, -, hbound, -⟩ := hv.basic k
  refine (ae_mu_of_ae_nu cfg hv k hbound).mono fun p hp => ?_
  have := abs_nonneg (cfg.b k p.1 0)
  have := abs_nonneg (cfg.b k p.1 1)
  have := abs_nonneg (cfg.b k p.1 4)
  linarith

/-- The whole incidence law has mass at most `K`. -/
theorem mu_univ_le (cfg : Model α) (hv : Valid cfg) (k : ℕ) :
    cfg.μ k univ ≤ ENNReal.ofReal (cfg.K k) := by
  obtain ⟨-, hνp, -, hμK, -, hsupp, -⟩ := hv.basic k
  have h1 : cfg.μ k univ = cfg.μ k (univ ×ˢ Icc (0 : ℝ) 1) := by
    rw [← measure_inter_conull (s := univ) hsupp, univ_inter]
  rw [h1]
  refine (hμK _).trans ?_
  rw [Measure.smul_apply, Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc,
    sub_zero, ENNReal.ofReal_one, smul_eq_mul, mul_one]

/-- **One refined slice.** The fine pieces retained from an old slice at the
coarse mesh form a slice at the fine mesh, for any loss `H'' ≥ H, H₁ K`. -/
theorem refined_slice (cfg : Model α) (hv : Valid cfg) {w : Bool} {L a m₀ m : ℝ}
    {τ : ℕ → ℕ} {H H'' H₁ : ℕ → ℝ} {ρ' ρ'' : ℕ → Measure (α × ℝ)} {β : ℕ → ℝ → ℝ}
    {n' : ℕ → ℝ → ℕ} {C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α}
    {tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ}
    {u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ}
    {G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ} (j : ℕ) (s : ℝ)
    (hold : Slice cfg w L a m₀ τ H ρ' β n' C tag u v G j s)
    (hH1 : 1 ≤ H j) (hHH : H j ≤ H'' j) (hH₁ : 0 < H₁ j)
    (hH₁K : H₁ j * cfg.K (τ j) ≤ H'' j)
    (hcov : ∀ᵐ p ∂ρ'' j, ∃ i, p.1 ∈ fine cfg τ m n' C j s
      (rE cfg τ m₀ m n' C tag β H₁ j s i)) :
    Slice cfg w L a m τ H'' ρ'' β (fun k s => rN cfg τ m₀ m n' C tag β H₁ k s)
      (fun k s i => fine cfg τ m n' C k s (rE cfg τ m₀ m n' C tag β H₁ k s i))
      (fun k s i => ![(rE cfg τ m₀ m n' C tag β H₁ k s i).2.1,
        (rE cfg τ m₀ m n' C tag β H₁ k s i).2.2])
      (fun k s i => u k s (rE cfg τ m₀ m n' C tag β H₁ k s i).1)
      (fun k s i => v k s (rE cfg τ m₀ m n' C tag β H₁ k s i).1)
      (fun k s i => G k s (rE cfg τ m₀ m n' C tag β H₁ k s i).1) j s := by
  classical
  obtain ⟨hβ, hlow, hup, hmeas, hdisj, hpiece, -, -⟩ := hold
  have hbasic := hv.basic (τ j)
  have hbm := hbasic.1
  have hρμ := hbasic.2.2.2.2.1
  have hK1 : 1 ≤ cfg.K (τ j) := hv.subpower.1 _
  have hH0 : 0 < H j := lt_of_lt_of_le one_pos hH1
  have hH''0 : 0 < H'' j := lt_of_lt_of_le hH0 hHH
  have hH₁H'' : H₁ j ≤ H'' j := by nlinarith
  have hN := hv.scale (τ j)
  have hNpos : 0 < cfg.N (τ j) := by linarith
  refine ⟨hβ, ?_, ?_, ?_, ?_, ?_, ?_, hcov⟩
  · refine le_trans ?_ hlow
    apply div_le_div_of_nonneg_left _ hH0 hHH
    apply mul_nonneg (Real.rpow_nonneg hNpos.le _)
    split_ifs
    · exact zero_le_one
    · exact Real.rpow_nonneg hNpos.le _
  · exact hup.trans (mul_le_mul_of_nonneg_right hHH (Real.rpow_nonneg hNpos.le _))
  · intro i
    exact fine_measurable cfg τ m n' C j s hbm hmeas _
  · intro i i' hii'
    exact fine_disjoint cfg τ m n' C j s hdisj
      (fun h => hii' (rE_injective cfg τ m₀ m n' C tag β H₁ j s h))
  · intro i
    set x := rE cfg τ m₀ m n' C tag β H₁ j s i with hx
    obtain ⟨huv, hdeg, hGb, hl, -⟩ := hpiece x.1
    refine ⟨huv.trans hHH, hdeg, fun t ht w hw => (hGb t ht w hw).trans hHH, ?_, ?_⟩
    · rintro l ⟨hlC, hl0, hl1⟩
      obtain ⟨-, -, hlt⟩ := hl l hlC
      refine ⟨by simpa [χf] using hl0, by simpa [χf] using hl1, fun t ht => ⟨?_, ?_⟩⟩
      · exact (hlt t ht).1.trans (mul_le_mul_of_nonneg_right hHH hβ.le)
      · exact (hlt t ht).2.trans (mul_le_mul_of_nonneg_right hHH (Real.rpow_nonneg hNpos.le _))
    · have hmem := rE_mem cfg τ m₀ m n' C tag β H₁ j s i
      simp only [rIdx, Finset.mem_filter] at hmem
      refine le_trans ?_ hmem.2
      simp only [floorVal, χf, Fin.isValue, Matrix.cons_val_zero]
      gcongr ENNReal.ofReal ?_ * _
      apply div_le_div_of_nonneg_left _ hH₁ hH₁H''
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hNpos.le _)
        (Real.rpow_nonneg (Real.rpow_nonneg hNpos.le _) _)) hβ.le
  · -- the budget, from the floors and disjointness
    have hc : ∀ i : Fin (rN cfg τ m₀ m n' C tag β H₁ j s),
        ENNReal.ofReal (cfg.N (τ j) ^ (-m) * (cfg.N (τ j) ^ (-s)) ^ cfg.d * β j s) *
            cfg.π (τ j) {w : ℝ | ⌊w / cfg.N (τ j) ^ (-m)⌋ =
              (![(rE cfg τ m₀ m n' C tag β H₁ j s i).2.1,
                (rE cfg τ m₀ m n' C tag β H₁ j s i).2.2] : Fin 2 → ℤ) 0} ≤
          ENNReal.ofReal (H₁ j) * cfg.ρ (τ j)
            (fine cfg τ m n' C j s (rE cfg τ m₀ m n' C tag β H₁ j s i) ×ˢ Icc (0 : ℝ) 1) := by
      intro i
      have hmem := rE_mem cfg τ m₀ m n' C tag β H₁ j s i
      simp only [rIdx, Finset.mem_filter] at hmem
      refine le_trans ?_ (mul_le_mul_right hmem.2 _)
      simp only [floorVal, χf, Fin.isValue, Matrix.cons_val_zero]
      rw [← mul_assoc, ← ENNReal.ofReal_mul hH₁.le]
      gcongr ENNReal.ofReal ?_ * _
      rw [mul_div_cancel₀ _ hH₁.ne']
    calc ∑ i : Fin (rN cfg τ m₀ m n' C tag β H₁ j s),
          ENNReal.ofReal (cfg.N (τ j) ^ (-m) * (cfg.N (τ j) ^ (-s)) ^ cfg.d * β j s) *
            cfg.π (τ j) {w : ℝ | ⌊w / cfg.N (τ j) ^ (-m)⌋ =
              (![(rE cfg τ m₀ m n' C tag β H₁ j s i).2.1,
                (rE cfg τ m₀ m n' C tag β H₁ j s i).2.2] : Fin 2 → ℤ) 0}
        ≤ ∑ i : Fin (rN cfg τ m₀ m n' C tag β H₁ j s), ENNReal.ofReal (H₁ j) *
            cfg.ρ (τ j) (fine cfg τ m n' C j s (rE cfg τ m₀ m n' C tag β H₁ j s i) ×ˢ
              Icc (0 : ℝ) 1) := Finset.sum_le_sum fun i _ => hc i
      _ = ENNReal.ofReal (H₁ j) * cfg.ρ (τ j) (⋃ i : Fin (rN cfg τ m₀ m n' C tag β H₁ j s),
            fine cfg τ m n' C j s (rE cfg τ m₀ m n' C tag β H₁ j s i) ×ˢ Icc (0 : ℝ) 1) := by
          rw [← Finset.mul_sum, measure_iUnion]
          · rw [tsum_fintype]
          · intro i i' hii'
            simp only [Function.onFun]
            exact Set.disjoint_prod.mpr (Or.inl (fine_disjoint cfg τ m n' C j s hdisj
              (fun h => hii' (rE_injective cfg τ m₀ m n' C tag β H₁ j s h))))
          · intro i
            exact (fine_measurable cfg τ m n' C j s hbm hmeas _).prod measurableSet_Icc
      _ ≤ ENNReal.ofReal (H₁ j) * ENNReal.ofReal (cfg.K (τ j)) := by
          gcongr
          exact (measure_mono (subset_univ _)).trans ((hρμ univ).trans (mu_univ_le cfg hv _))
      _ ≤ ENNReal.ofReal (H'' j) := by
          rw [← ENNReal.ofReal_mul hH₁.le]
          exact ENNReal.ofReal_le_ofReal hH₁K

theorem tendsto_of_strictMono {τ : ℕ → ℕ} (hτ : StrictMono τ) : Tendsto τ atTop atTop :=
  hτ.tendsto_atTop

/-- **Refinement of a layer output.** An output at the coarse mesh exponent
`m₀` gives an output at any finer `m` with `m₀ < S m`, with the same widths. -/
theorem LayerOutput.refine (cfg : Model α) (hv : Valid cfg) {w : Bool} {L a m₀ m : ℝ}
    {D : Finset ℝ} (hm₀ : 0 < m₀) (hm : m₀ ≤ m) (hSm : m₀ < cfg.S * m)
    (h : LayerOutput cfg w L a D m₀) : LayerOutput cfg w L a D m := by
  classical
  obtain ⟨τ, hτ, H, hH, hHsub, ρ', β, n', C, tag, u, v, G, hρ', hsl⟩ := h
  have hτlim : Tendsto τ atTop atTop := tendsto_of_strictMono hτ
  set dc : ℝ := (D.card : ℝ) + 1 with hdc
  have hdc1 : 1 ≤ dc := by simp [dc]
  let H₁ : ℕ → ℝ := fun k => 24 * dc * H k ^ 2
  let H'' : ℕ → ℝ := fun k => 2 * H₁ k * cfg.K (τ k)
  have hH1 : ∀ k, 1 ≤ H k := fun k => (hH k).1
  have hK1 : ∀ k, 1 ≤ cfg.K k := hv.subpower.1
  have hH₁pos : ∀ k, 0 < H₁ k := fun k => by
    have := hH1 k; simp only [H₁]; positivity
  have hH₁ge : ∀ k, H k ≤ H₁ k := fun k => by
    have := hH1 k; simp only [H₁]; nlinarith
  have hH''ge : ∀ k, 2 * H₁ k ≤ H'' k := fun k => by
    have := hK1 (τ k); have := hH₁pos k; simp only [H'']; nlinarith
  -- the new retained laws (unshifted)
  let good : ℕ → Set (α × ℝ) := fun k =>
    ⋂ s ∈ D, {p | ∃ i, p.1 ∈ fine cfg τ m n' C k s (rE cfg τ m₀ m n' C tag β H₁ k s i)}
  let ρ'' : ℕ → Measure (α × ℝ) := fun k => (ρ' k).restrict (good k)
  have hm0 : 0 < m := lt_of_lt_of_le hm₀ hm
  -- the per-depth loss, under the eventual conditions at index `k`
  have hloss : ∀ k,
      (∀ j : ℤ, cfg.μ (τ k) {p | ⌊cfg.b (τ k) p.1 3 / χf cfg τ m k⌋ = j} ≤
        ENNReal.ofReal (400 * cfg.K (τ k) ^ 5 * (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m)))) →
      ((2 * cfg.K (τ k) + 5) / χc cfg τ m₀ k + 4) *
          (400 * cfg.K (τ k) ^ 5 * (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m))) ≤
        1 / (4 * dc * H k) →
      ∀ s ∈ D, ρ' k {p | ¬ ∃ i, p.1 ∈ fine cfg τ m n' C k s
          (rE cfg τ m₀ m n' C tag β H₁ k s i)} ≤ ENNReal.ofReal (3 / (8 * dc * H k)) := by
    intro k hvc hnum s hs
    obtain ⟨hβ, -, -, hmeas, hdisj, hpiece, hbudget, hcov⟩ := hsl k s hs
    have hN := hv.scale (τ k)
    have hNpos : 0 < cfg.N (τ k) := by linarith
    have hχ : 0 < χf cfg τ m k := Real.rpow_pos_of_pos hNpos _
    have hχ₀ : 0 < χc cfg τ m₀ k := Real.rpow_pos_of_pos hNpos _
    have hχχ : χf cfg τ m k ≤ χc cfg τ m₀ k :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hχ₀1 : χc cfg τ m₀ k ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have hbasic := hv.basic (τ k)
    have hρμ := hbasic.2.2.2.2.1
    have hK1k := hK1 (τ k)
    have hρ'ρ : ρ' k ≤ cfg.ρ (τ k) := (hρ' k).1
    have hH0 : 0 < H k := lt_of_lt_of_le one_pos (hH1 k)
    have hsub : {p : α × ℝ | ¬ ∃ i, p.1 ∈ fine cfg τ m n' C k s
        (rE cfg τ m₀ m n' C tag β H₁ k s i)} ⊆
        ({p | ¬ ∃ i, p.1 ∈ C k s i} ∪ {p | ¬ goodBin (χf cfg τ m k) (χc cfg τ m₀ k)
          ⌊cfg.b (τ k) p.1 3 / χf cfg τ m k⌋}) ∪
        ⋃ x ∈ (cand cfg τ m₀ m n' tag k s \ rIdx cfg τ m₀ m n' C tag β H₁ k s),
          fine cfg τ m n' C k s x ×ˢ (univ : Set ℝ) := by
      intro p hp
      by_cases h0 : ∃ i, p.1 ∈ C k s i
      · obtain ⟨i, hi⟩ := h0
        by_cases h1 : goodBin (χf cfg τ m k) (χc cfg τ m₀ k) ⌊cfg.b (τ k) p.1 3 / χf cfg τ m k⌋
        · obtain ⟨ht0, ht1, -⟩ := (hpiece i).2.2.2.1 p.1 hi
          obtain ⟨hcand, hfine⟩ := mem_cand_of_mem cfg τ m₀ m n' C tag k s i hχ hχ₀ hi
            ht0 ht1 h1
          right
          simp only [mem_iUnion]
          refine ⟨_, Finset.mem_sdiff.mpr ⟨hcand, fun hr => ?_⟩, hfine, mem_univ _⟩
          obtain ⟨i'', hi''⟩ := rE_surj cfg τ m₀ m n' C tag β H₁ k s _ hr
          exact hp ⟨i'', by rw [hi'']; exact hfine⟩
        · left; right; exact h1
      · left; left; exact h0
    have hU0 : ρ' k {p | ¬ ∃ i, p.1 ∈ C k s i} = 0 := by
      rw [ae_iff] at hcov; exact hcov
    have hU1 : ρ' k {p | ¬ goodBin (χf cfg τ m k) (χc cfg τ m₀ k)
        ⌊cfg.b (τ k) p.1 3 / χf cfg τ m k⌋} ≤ ENNReal.ofReal (1 / (4 * dc * H k)) := by
      refine (hρ'ρ _).trans ((hρμ _).trans ?_)
      refine (straddle_measure_le (cfg.μ (τ k)) (cfg.b (τ k))
        (c₁ := 400 * cfg.K (τ k) ^ 5 * (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m)))
        hχ hχχ hχ₀1 (by linarith) (by positivity) (ae_abs_b3_le cfg hv (τ k)) hvc).trans ?_
      exact ENNReal.ofReal_le_ofReal hnum
    have hU2 : ρ' k (⋃ x ∈ (cand cfg τ m₀ m n' tag k s \ rIdx cfg τ m₀ m n' C tag β H₁ k s),
        fine cfg τ m n' C k s x ×ˢ (univ : Set ℝ)) ≤ ENNReal.ofReal (1 / (8 * dc * H k)) := by
      have hsupp : cfg.ρ (τ k) (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
        measure_mono_null le_rfl (le_antisymm ((hρμ _).trans (le_of_eq hbasic.2.2.2.2.2.1))
          zero_le)
      have hfloor : ∀ x ∈ cand cfg τ m₀ m n' tag k s \ rIdx cfg τ m₀ m n' C tag β H₁ k s,
          ρ' k (fine cfg τ m n' C k s x ×ˢ (univ : Set ℝ)) ≤
            floorVal cfg τ m β H₁ k s x.2.1 := by
        intro x hx
        obtain ⟨-, hxr⟩ := Finset.mem_sdiff.mp hx
        have hnot : ¬ floorVal cfg τ m β H₁ k s x.2.1 ≤
            cfg.ρ (τ k) (fine cfg τ m n' C k s x ×ˢ Icc (0 : ℝ) 1) := by
          intro hle
          exact hxr (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hx).1, hle⟩)
        refine (hρ'ρ _).trans ?_
        have heq : cfg.ρ (τ k) (fine cfg τ m n' C k s x ×ˢ (univ : Set ℝ)) =
            cfg.ρ (τ k) (fine cfg τ m n' C k s x ×ˢ Icc (0 : ℝ) 1) := by
          rw [← measure_inter_conull hsupp]
          congr 1
          ext p; simp [and_comm]
        rw [heq]
        exact (not_le.mp hnot).le
      have hcand : ∑ x ∈ cand cfg τ m₀ m n' tag k s, floorVal cfg τ m β H₁ k s x.2.1 ≤
          ∑ i : Fin (n' k s), ∑ j₀ ∈ fset0 cfg τ m₀ m n' tag k s i,
            ∑ _j₁ ∈ fset1 cfg τ m₀ m n' tag k s i, floorVal cfg τ m β H₁ k s j₀ := by
        rw [cand, Finset.sum_biUnion]
        · refine Finset.sum_le_sum fun i _ => ?_
          rw [Finset.sum_image (fun jj _ jj' _ h => (Prod.mk.inj h).2), Finset.sum_product]
        · intro i _ i' _ hii'
          simp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro x hx hx'
          obtain ⟨jj, -, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨jj', -, h⟩ := Finset.mem_image.mp hx'
          exact hii' (Prod.mk.inj h).1.symm
      have hsum := Finset.sum_le_sum fun (i : Fin (n' k s)) (_ : i ∈ Finset.univ) =>
        sum_floorVal_le cfg τ m₀ m n' tag β H₁ k s i hχ hχχ
          (div_nonneg (mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hNpos.le _) _) hβ.le)
            (hH₁pos k).le)
      have hb3 : ∑ i : Fin (n' k s),
          ENNReal.ofReal (3 * χc cfg τ m₀ k * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k) *
            cfg.π (τ k) {w : ℝ | ⌊w / χc cfg τ m₀ k⌋ = tag k s i 0} ≤
          ENNReal.ofReal (3 * H k / H₁ k) := by
        have hsplit : ∀ i : Fin (n' k s),
            ENNReal.ofReal (3 * χc cfg τ m₀ k * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s / H₁ k) *
              cfg.π (τ k) {w : ℝ | ⌊w / χc cfg τ m₀ k⌋ = tag k s i 0} =
            ENNReal.ofReal (3 / H₁ k) *
              (ENNReal.ofReal (cfg.N (τ k) ^ (-m₀) * (cfg.N (τ k) ^ (-s)) ^ cfg.d * β k s) *
                cfg.π (τ k) {w : ℝ | ⌊w / cfg.N (τ k) ^ (-m₀)⌋ = tag k s i 0}) := by
          intro i
          rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (by norm_num) (hH₁pos k).le)]
          congr 2
          simp only [χc]; ring
        rw [Finset.sum_congr rfl fun i _ => hsplit i, ← Finset.mul_sum]
        calc ENNReal.ofReal (3 / H₁ k) * _ ≤ ENNReal.ofReal (3 / H₁ k) * ENNReal.ofReal (H k) :=
              mul_le_mul_right hbudget _
          _ = ENNReal.ofReal (3 * H k / H₁ k) := by
              rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) (hH₁pos k).le)]
              congr 1; ring
      calc ρ' k (⋃ x ∈ (cand cfg τ m₀ m n' tag k s \ rIdx cfg τ m₀ m n' C tag β H₁ k s),
            fine cfg τ m n' C k s x ×ˢ (univ : Set ℝ))
          ≤ ∑ x ∈ cand cfg τ m₀ m n' tag k s \ rIdx cfg τ m₀ m n' C tag β H₁ k s,
              ρ' k (fine cfg τ m n' C k s x ×ˢ (univ : Set ℝ)) := measure_biUnion_finset_le _ _
        _ ≤ ∑ x ∈ cand cfg τ m₀ m n' tag k s \ rIdx cfg τ m₀ m n' C tag β H₁ k s,
              floorVal cfg τ m β H₁ k s x.2.1 := Finset.sum_le_sum hfloor
        _ ≤ ∑ x ∈ cand cfg τ m₀ m n' tag k s, floorVal cfg τ m β H₁ k s x.2.1 :=
            Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
        _ ≤ _ := hcand
        _ ≤ _ := hsum
        _ ≤ ENNReal.ofReal (3 * H k / H₁ k) := hb3
        _ = ENNReal.ofReal (1 / (8 * dc * H k)) := by
            congr 1; simp only [H₁]; field_simp; ring
    calc ρ' k {p | ¬ ∃ i, p.1 ∈ fine cfg τ m n' C k s (rE cfg τ m₀ m n' C tag β H₁ k s i)}
        ≤ ρ' k (({p | ¬ ∃ i, p.1 ∈ C k s i} ∪ {p | ¬ goodBin (χf cfg τ m k) (χc cfg τ m₀ k)
          ⌊cfg.b (τ k) p.1 3 / χf cfg τ m k⌋}) ∪
          ⋃ x ∈ (cand cfg τ m₀ m n' tag k s \ rIdx cfg τ m₀ m n' C tag β H₁ k s),
            fine cfg τ m n' C k s x ×ˢ (univ : Set ℝ)) := measure_mono hsub
      _ ≤ (ρ' k {p | ¬ ∃ i, p.1 ∈ C k s i} + ρ' k {p | ¬ goodBin (χf cfg τ m k)
            (χc cfg τ m₀ k) ⌊cfg.b (τ k) p.1 3 / χf cfg τ m k⌋}) +
          ρ' k (⋃ x ∈ (cand cfg τ m₀ m n' tag k s \ rIdx cfg τ m₀ m n' C tag β H₁ k s),
            fine cfg τ m n' C k s x ×ˢ (univ : Set ℝ)) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ (0 + ENNReal.ofReal (1 / (4 * dc * H k))) + ENNReal.ofReal (1 / (8 * dc * H k)) := by
          rw [hU0]; exact add_le_add (add_le_add le_rfl hU1) hU2
      _ = ENNReal.ofReal (3 / (8 * dc * H k)) := by
          rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; field_simp; ring
  -- the eventual conditions
  set R : ℝ := max m m⁻¹ + 2 with hR
  have hR1 : 1 < R := by have := le_max_left m m⁻¹; linarith
  have hRpos : 0 < R := by linarith
  have hRm : m ≤ R := by have := le_max_left m m⁻¹; linarith
  have hRm' : R⁻¹ ≤ m := by
    have h1 : m⁻¹ ≤ R := by have := le_max_right m m⁻¹; linarith
    exact (inv_le_comm₀ hm0 hRpos).mp h1
  have hR1' : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1.le
  have hKτ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K (τ k) ≤ cfg.N (τ k) ^ ε :=
    fun ε hε => hτlim.eventually (hv.subpower.2 ε hε)
  have hNτ : Tendsto (fun k => cfg.N (τ k)) atTop atTop := hv.scale_limit.comp hτlim
  have hvc : ∀ᶠ k in atTop, ∀ j : ℤ,
      cfg.μ (τ k) {p | ⌊cfg.b (τ k) p.1 3 / χf cfg τ m k⌋ = j} ≤
        ENNReal.ofReal (400 * cfg.K (τ k) ^ 5 * (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m))) := by
    have h1 := hτlim.eventually (velocity_cap_eventually cfg hv hm0)
    have h2 := hτlim.eventually (hv.caps R hR1)
    filter_upwards [h1, h2] with k hk1 hk2 j
    obtain ⟨hπbin, -, -⟩ := hk2 1 0 m hR1' hR1.le le_rfl hRpos.le hRm' hRm
    have hK0 : 0 ≤ cfg.K (τ k) := by linarith [hK1 (τ k)]
    calc cfg.μ (τ k) {p | ⌊cfg.b (τ k) p.1 3 / χf cfg τ m k⌋ = j}
        ≤ ENNReal.ofReal (400 * cfg.K (τ k) ^ 5) *
            cfg.π (τ k) {w | ⌊w / cfg.N (τ k) ^ (-m)⌋ = j} := hk1 j
      _ ≤ ENNReal.ofReal (400 * cfg.K (τ k) ^ 5) *
            ENNReal.ofReal (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m)) :=
          mul_le_mul_right (hπbin j) _
      _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
  have hnum : ∀ᶠ k in atTop,
      ((2 * cfg.K (τ k) + 5) / χc cfg τ m₀ k + 4) *
          (400 * cfg.K (τ k) ^ 5 * (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m))) ≤
        1 / (4 * dc * H k) := by
    set δ := cfg.S * m - m₀ with hδ
    have hδpos : 0 < δ := by linarith
    have h1 := hKτ (δ / 16) (by linarith)
    have h2 := hHsub (δ / 4) (by linarith)
    have h3 : ∀ᶠ k in atTop, 17600 * dc ≤ cfg.N (τ k) ^ (5 * δ / 16) :=
      ((tendsto_rpow_atTop (by linarith)).comp hNτ).eventually_ge_atTop _
    filter_upwards [h1, h2, h3] with k hk1 hk2 hk3
    have hN := hv.scale (τ k)
    have hNpos : 0 < cfg.N (τ k) := by linarith
    have hK1k := hK1 (τ k)
    have hH1k := hH1 k
    have hNm₀ : 1 ≤ cfg.N (τ k) ^ m₀ := Real.one_le_rpow (by linarith) hm₀.le
    have hχc : (2 * cfg.K (τ k) + 5) / χc cfg τ m₀ k = (2 * cfg.K (τ k) + 5) * cfg.N (τ k) ^ m₀ := by
      simp only [χc]; rw [Real.rpow_neg hNpos.le, div_inv_eq_mul]
    rw [hχc]
    have hfirst : (2 * cfg.K (τ k) + 5) * cfg.N (τ k) ^ m₀ + 4 ≤
        11 * cfg.K (τ k) * cfg.N (τ k) ^ m₀ := by nlinarith
    have hpow : cfg.N (τ k) ^ m₀ * cfg.N (τ k) ^ (-cfg.S * m) = cfg.N (τ k) ^ (-δ) := by
      rw [← Real.rpow_add hNpos]; congr 1; rw [hδ]; ring
    have hK7 : cfg.K (τ k) ^ 7 ≤ cfg.N (τ k) ^ (7 * δ / 16) := by
      calc cfg.K (τ k) ^ 7 ≤ (cfg.N (τ k) ^ (δ / 16)) ^ 7 :=
            pow_le_pow_left₀ (by linarith) hk1 7
        _ = cfg.N (τ k) ^ (7 * δ / 16) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; push_cast; ring_nf
    have hHK : cfg.K (τ k) ^ 7 * H k ≤ cfg.N (τ k) ^ (11 * δ / 16) := by
      calc cfg.K (τ k) ^ 7 * H k ≤ cfg.N (τ k) ^ (7 * δ / 16) * cfg.N (τ k) ^ (δ / 4) :=
            mul_le_mul hK7 hk2 (by linarith) (Real.rpow_nonneg hNpos.le _)
        _ = cfg.N (τ k) ^ (11 * δ / 16) := by rw [← Real.rpow_add hNpos]; ring_nf
    have hbig : 17600 * dc * (cfg.K (τ k) ^ 7 * H k) ≤ cfg.N (τ k) ^ δ := by
      calc 17600 * dc * (cfg.K (τ k) ^ 7 * H k)
          ≤ cfg.N (τ k) ^ (5 * δ / 16) * cfg.N (τ k) ^ (11 * δ / 16) :=
            mul_le_mul hk3 hHK (by positivity) (Real.rpow_nonneg hNpos.le _)
        _ = cfg.N (τ k) ^ δ := by rw [← Real.rpow_add hNpos]; ring_nf
    have hNδ : 0 < cfg.N (τ k) ^ δ := Real.rpow_pos_of_pos hNpos _
    have hNδ' : cfg.N (τ k) ^ (-δ) = (cfg.N (τ k) ^ δ)⁻¹ := Real.rpow_neg hNpos.le _
    have hHpos : 0 < H k := by linarith
    calc ((2 * cfg.K (τ k) + 5) * cfg.N (τ k) ^ m₀ + 4) *
          (400 * cfg.K (τ k) ^ 5 * (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m)))
        ≤ (11 * cfg.K (τ k) * cfg.N (τ k) ^ m₀) *
          (400 * cfg.K (τ k) ^ 5 * (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m))) :=
          mul_le_mul_of_nonneg_right hfirst (by positivity)
      _ = 4400 * cfg.K (τ k) ^ 7 * (cfg.N (τ k) ^ m₀ * cfg.N (τ k) ^ (-cfg.S * m)) := by ring
      _ = 4400 * cfg.K (τ k) ^ 7 * (cfg.N (τ k) ^ δ)⁻¹ := by rw [hpow, hNδ']
      _ ≤ 1 / (4 * dc * H k) := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ hNδ (by positivity)]
          nlinarith [hbig]
  -- the mass of the new retained laws
  have hmassk : ∀ k,
      (∀ j : ℤ, cfg.μ (τ k) {p | ⌊cfg.b (τ k) p.1 3 / χf cfg τ m k⌋ = j} ≤
        ENNReal.ofReal (400 * cfg.K (τ k) ^ 5 * (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m)))) →
      ((2 * cfg.K (τ k) + 5) / χc cfg τ m₀ k + 4) *
          (400 * cfg.K (τ k) ^ 5 * (cfg.K (τ k) * cfg.N (τ k) ^ (-cfg.S * m))) ≤
        1 / (4 * dc * H k) →
      ENNReal.ofReal ((H'' k)⁻¹) ≤ ρ'' k univ := by
    intro k hk1 hk2
    have hHpos : 0 < H k := lt_of_lt_of_le one_pos (hH1 k)
    have hcompl : (good k)ᶜ ⊆ ⋃ s ∈ D, {p | ¬ ∃ i, p.1 ∈ fine cfg τ m n' C k s
        (rE cfg τ m₀ m n' C tag β H₁ k s i)} := by
      intro p hp
      simp only [good, mem_compl_iff, mem_iInter, not_forall] at hp
      obtain ⟨s, hs, hps⟩ := hp
      exact mem_iUnion₂.mpr ⟨s, hs, hps⟩
    have hbad : ρ' k (good k)ᶜ ≤ ENNReal.ofReal (3 / (8 * H k)) := by
      calc ρ' k (good k)ᶜ ≤ ρ' k (⋃ s ∈ D, {p | ¬ ∃ i, p.1 ∈ fine cfg τ m n' C k s
            (rE cfg τ m₀ m n' C tag β H₁ k s i)}) := measure_mono hcompl
        _ ≤ ∑ s ∈ D, ρ' k {p | ¬ ∃ i, p.1 ∈ fine cfg τ m n' C k s
            (rE cfg τ m₀ m n' C tag β H₁ k s i)} := measure_biUnion_finset_le _ _
        _ ≤ ∑ _s ∈ D, ENNReal.ofReal (3 / (8 * dc * H k)) :=
            Finset.sum_le_sum fun s hs => hloss k hk1 hk2 s hs
        _ = ENNReal.ofReal ((D.card : ℝ) * (3 / (8 * dc * H k))) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        _ ≤ ENNReal.ofReal (3 / (8 * H k)) := by
            apply ENNReal.ofReal_le_ofReal
            have hdc0 : 0 < dc := by linarith
            rw [show (D.card : ℝ) * (3 / (8 * dc * H k)) = (D.card / dc) * (3 / (8 * H k)) by
              field_simp]
            have : (D.card : ℝ) / dc ≤ 1 := by
              rw [div_le_one hdc0]; simp [dc]
            have h3 : 0 ≤ 3 / (8 * H k) := by positivity
            nlinarith
    have huniv : ρ' k univ ≤ ρ' k (good k) + ρ' k (good k)ᶜ := by
      calc ρ' k univ = ρ' k (good k ∪ (good k)ᶜ) := by rw [union_compl_self]
        _ ≤ ρ' k (good k) + ρ' k (good k)ᶜ := measure_union_le _ _
    have hρ''eq : ρ'' k univ = ρ' k (good k) := Measure.restrict_apply_univ _
    rw [hρ''eq]
    have h1 : ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k (good k) + ENNReal.ofReal (3 / (8 * H k)) :=
      ((hρ' k).2.trans huniv).trans (add_le_add le_rfl hbad)
    have h2 : ENNReal.ofReal ((H k)⁻¹) - ENNReal.ofReal (3 / (8 * H k)) ≤ ρ' k (good k) :=
      tsub_le_iff_right.mpr h1
    refine le_trans ?_ h2
    rw [← ENNReal.ofReal_sub _ (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hH'' : 2 * H k ≤ H'' k := (by linarith [hH₁ge k] : 2 * H k ≤ 2 * H₁ k).trans (hH''ge k)
    have hH''pos : 0 < H'' k := by linarith
    rw [inv_eq_one_div, inv_eq_one_div, div_le_iff₀ hH''pos]
    have : (1 / H k - 3 / (8 * H k)) = 5 / (8 * H k) := by field_simp; ring
    rw [this]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 (hvc.and hnum)
  refine ⟨fun k => τ (k + k₀), fun a b h => hτ (Nat.add_lt_add_right h k₀),
    fun k => H'' (k + k₀), ?_, ?_, fun k => ρ'' (k + k₀), fun k s => β (k + k₀) s,
    fun k s => rN cfg τ m₀ m n' C tag β H₁ (k + k₀) s,
    fun k s i => fine cfg τ m n' C (k + k₀) s (rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s i),
    fun k s i => ![(rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s i).2.1,
      (rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s i).2.2],
    fun k s i => u (k + k₀) s (rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s i).1,
    fun k s i => v (k + k₀) s (rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s i).1,
    fun k s i => G (k + k₀) s (rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s i).1, ?_, ?_⟩
  · intro k
    have := hK1 (τ (k + k₀))
    have := hH₁ge (k + k₀)
    have := hH1 (k + k₀)
    have h2 := hH''ge (k + k₀)
    constructor
    · simp only [H'', H₁] at h2 ⊢; nlinarith
    · simp only [H'']; nlinarith
  · intro ε hε
    have h1 := hHsub (ε / 4) (by linarith)
    have h2 := hKτ (ε / 4) (by linarith)
    have h3 : ∀ᶠ k in atTop, 48 * dc ≤ cfg.N (τ k) ^ (ε / 4) :=
      ((tendsto_rpow_atTop (by linarith)).comp hNτ).eventually_ge_atTop _
    have hall : ∀ᶠ k in atTop, H'' k ≤ cfg.N (τ k) ^ ε := by
      filter_upwards [h1, h2, h3] with k hk1 hk2 hk3
      have hN := hv.scale (τ k)
      have hNpos : 0 < cfg.N (τ k) := by linarith
      have hH0 : 0 ≤ H k := by linarith [hH1 k]
      calc H'' k = 48 * dc * (H k * H k) * cfg.K (τ k) := by simp only [H'', H₁]; ring
        _ ≤ cfg.N (τ k) ^ (ε / 4) * (cfg.N (τ k) ^ (ε / 4) * cfg.N (τ k) ^ (ε / 4)) *
              cfg.N (τ k) ^ (ε / 4) := by
            have hp := Real.rpow_nonneg hNpos.le (ε / 4)
            have hK0 : 0 ≤ cfg.K (τ k) := by linarith [hK1 (τ k)]
            have hdc0 : 0 ≤ 48 * dc := by linarith
            exact mul_le_mul (mul_le_mul hk3 (mul_le_mul hk1 hk1 hH0 hp) (by positivity) hp)
              hk2 hK0 (by positivity)
        _ = cfg.N (τ k) ^ ε := by
            rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; ring_nf
    exact (tendsto_add_atTop_nat k₀).eventually hall
  · intro k
    refine ⟨Measure.restrict_le_self.trans (hρ' (k + k₀)).1, ?_⟩
    obtain ⟨hA, hB⟩ := hk₀ (k + k₀) (by omega)
    exact hmassk (k + k₀) hA hB
  · intro k s hs
    have hcov : ∀ᵐ p ∂ρ'' (k + k₀), ∃ i, p.1 ∈ fine cfg τ m n' C (k + k₀) s
        (rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s i) := by
      have hgm : ∀ p ∈ good (k + k₀), ∃ i, p.1 ∈ fine cfg τ m n' C (k + k₀) s
          (rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s i) := by
        intro p hp
        simp only [good, mem_iInter] at hp
        exact hp s hs
      have hgoodm : MeasurableSet (good (k + k₀)) := by
        refine MeasurableSet.biInter D.countable_toSet fun s' hs' => ?_
        have heq : {p : α × ℝ | ∃ i, p.1 ∈ fine cfg τ m n' C (k + k₀) s'
            (rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s' i)} =
            ⋃ i, fine cfg τ m n' C (k + k₀) s' (rE cfg τ m₀ m n' C tag β H₁ (k + k₀) s' i) ×ˢ
              (univ : Set ℝ) := by
          ext p; simp
        rw [heq]
        exact MeasurableSet.iUnion fun i =>
          (fine_measurable cfg τ m n' C (k + k₀) s' (hv.basic _).1
            (hsl (k + k₀) s' hs').2.2.2.1 _).prod MeasurableSet.univ
      exact (ae_restrict_iff' hgoodm).2 (Filter.Eventually.of_forall hgm)
    exact refined_slice cfg hv (k + k₀) s (hsl (k + k₀) s hs) (hH1 _)
      ((hH₁ge _).trans (by linarith [hH''ge (k + k₀), hH₁pos (k + k₀)])) (hH₁pos _)
      (by have := hH''ge (k + k₀); have := hH₁pos (k + k₀); simp only [H''] at *; nlinarith)
      hcov

end Model

end

end Submission.Obl.k4_general_parent_narrow_contact_transfer
