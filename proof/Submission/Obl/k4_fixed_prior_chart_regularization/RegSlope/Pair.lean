-- Adapted from LOT tree g-oai-074, obligation o245, session x0854, commit 3602b8f657fd9f9293587a9dd3e1bdba2451d373.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/RegSlope/Pair.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope.Basic

/-!
# Slope regularization: pair durations and spacetime counts

At width `s`, keep an incidence `(l, t)` only if `l` is labeled for time `≥ s/K₂` in the
`s`-block of `t` (`pairGood`, cost `≤ 2/K₂`). Then, in one `s`-group of the static `y`, the
occupied spacetime cells `(⌊t/s⌋, ⌊x̄_l(t)/s⌋)` number at most
`(1/s + 1) K₂ (4K + 3) B`, where `B` bounds the scalar support count at width `s`
(`spacetime_count`): integrate the fixed-time scalar count over the block durations of witnesses.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

open FirstJet

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The labeled duration of `l` in the `s`-block with index `j`. -/
def blockDur (E : Set (Ω × ℝ)) (s : ℝ) (l : Ω) (j : ℤ) : ENNReal :=
  volume {t' | (l, t') ∈ E ∧ ⌊t' / s⌋ = j}

theorem measurableSet_block (s : ℝ) (j : ℤ) : MeasurableSet {t' : ℝ | ⌊t' / s⌋ = j} :=
  (Int.measurable_floor.comp (measurable_id.div_const s)) (measurableSet_singleton j)

theorem measurable_blockDur {E : Set (Ω × ℝ)} (hE : MeasurableSet E) (s : ℝ) (j : ℤ) :
    Measurable fun l => blockDur E s l j := by
  have h : MeasurableSet (E ∩ univ ×ˢ {t' : ℝ | ⌊t' / s⌋ = j}) :=
    hE.inter (MeasurableSet.univ.prod (measurableSet_block s j))
  have hm := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) h
  have heq : (fun l => blockDur E s l j) =
      fun l => volume (Prod.mk l ⁻¹' (E ∩ univ ×ˢ {t' : ℝ | ⌊t' / s⌋ = j})) := by
    funext l; unfold blockDur; congr 1; ext t'; simp
  rw [heq]; exact hm

/-- Incidences whose trajectory is labeled for time `≥ s/K₂` in their `s`-block. -/
def pairGood (E : Set (Ω × ℝ)) (s K₂ : ℝ) : Set (Ω × ℝ) :=
  {p | p ∈ E ∧ ENNReal.ofReal (s / K₂) ≤ blockDur E s p.1 ⌊p.2 / s⌋}

omit [MeasurableSpace Ω] in
theorem pairGood_subset (E : Set (Ω × ℝ)) (s K₂ : ℝ) : pairGood E s K₂ ⊆ E := fun _ h => h.1

theorem measurableSet_pairGood {E : Set (Ω × ℝ)} (hE : MeasurableSet E) (s K₂ : ℝ) :
    MeasurableSet (pairGood E s K₂) := by
  have : pairGood E s K₂ = E ∩ ⋃ j : ℤ,
      {l | ENNReal.ofReal (s / K₂) ≤ blockDur E s l j} ×ˢ {t : ℝ | ⌊t / s⌋ = j} := by
    ext ⟨l, t⟩
    simp only [pairGood, mem_setOf_eq, mem_inter_iff, mem_iUnion, mem_prod]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, ⌊t / s⌋, h2, rfl⟩
    · rintro ⟨h1, j, h2, h3⟩; exact ⟨h1, h3 ▸ h2⟩
  rw [this]
  exact hE.inter (MeasurableSet.iUnion fun j =>
    (measurableSet_le measurable_const (measurable_blockDur hE s j)).prod
      (measurableSet_block s j))

/-- The pair-duration preparation costs at most `2/K₂`. -/
theorem pairGood_mass {ν : Measure Ω} [IsProbabilityMeasure ν] {E : Set (Ω × ℝ)}
    (hE : MeasurableSet E) (hE01 : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {s K₂ : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) (hK₂ : 0 < K₂) :
    (ν.prod volume) (E \ pairGood E s K₂) ≤ ENNReal.ofReal (2 / K₂) := by
  classical
  have hG := measurableSet_pairGood hE s K₂
  set J : ℕ := ⌊1 / s⌋₊ with hJ
  rw [Measure.prod_apply (hE.diff hG)]
  calc ∫⁻ l, volume (Prod.mk l ⁻¹' (E \ pairGood E s K₂)) ∂ν
      ≤ ∫⁻ _l, ENNReal.ofReal (2 / K₂) ∂ν := by
        refine lintegral_mono fun l => ?_
        -- the bad times of `l` lie in the short blocks
        have hsub : Prod.mk l ⁻¹' (E \ pairGood E s K₂) ⊆
            ⋃ j ∈ (Finset.range (J + 1)).filter
              (fun j : ℕ => blockDur E s l j < ENNReal.ofReal (s / K₂)),
              {t' | (l, t') ∈ E ∧ ⌊t' / s⌋ = (j : ℤ)} := by
          intro t ht
          simp only [mem_preimage, mem_diff, pairGood, mem_setOf_eq, not_and, not_le] at ht
          have hlt := ht.2 ht.1
          have ht01 := (hE01 ht.1).2
          have h0 : 0 ≤ ⌊t / s⌋ := Int.floor_nonneg.mpr (div_nonneg ht01.1 hs.le)
          obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h0
          have hnJ : n ≤ J := by
            have : (n : ℝ) ≤ t / s := by rw [← Int.cast_natCast, ← hn]; exact Int.floor_le _
            have h2 : t / s ≤ 1 / s := div_le_div_of_nonneg_right ht01.2 hs.le
            exact Nat.le_floor (this.trans h2)
          simp only [mem_iUnion, Finset.mem_filter, Finset.mem_range, mem_setOf_eq]
          exact ⟨n, ⟨by omega, by rw [← hn]; exact hlt⟩, ht.1, hn⟩
        calc volume (Prod.mk l ⁻¹' (E \ pairGood E s K₂))
            ≤ volume (⋃ j ∈ (Finset.range (J + 1)).filter
              (fun j : ℕ => blockDur E s l j < ENNReal.ofReal (s / K₂)),
              {t' | (l, t') ∈ E ∧ ⌊t' / s⌋ = (j : ℤ)}) := measure_mono hsub
          _ ≤ ∑ j ∈ (Finset.range (J + 1)).filter
              (fun j : ℕ => blockDur E s l j < ENNReal.ofReal (s / K₂)),
              volume {t' | (l, t') ∈ E ∧ ⌊t' / s⌋ = (j : ℤ)} := measure_biUnion_finset_le _ _
          _ ≤ ∑ _j ∈ Finset.range (J + 1), ENNReal.ofReal (s / K₂) := by
              refine (Finset.sum_le_sum fun j hj => ?_).trans
                (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
              exact (Finset.mem_filter.mp hj).2.le
          _ = ENNReal.ofReal ((J + 1) * (s / K₂)) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
                ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [show ((J : ℝ) + 1) = ((J + 1 : ℕ) : ℝ) by push_cast; ring,
                ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal (2 / K₂) := by
              apply ENNReal.ofReal_le_ofReal
              have hJs : (J : ℝ) * s ≤ 1 := by
                have := Nat.floor_le (show 0 ≤ 1 / s by positivity)
                calc (J : ℝ) * s ≤ 1 / s * s := by gcongr
                  _ = 1 := by field_simp
              calc ((J : ℝ) + 1) * (s / K₂) = (J * s + s) / K₂ := by ring
                _ ≤ (1 + 1) / K₂ := by gcongr
                _ = 2 / K₂ := by norm_num
    _ = ENNReal.ofReal (2 / K₂) := by rw [lintegral_const, measure_univ, mul_one]

omit [MeasurableSpace Ω] in
/-- The `s`-block of `t` has length `s`. -/
theorem volume_block_le {s : ℝ} (hs : 0 < s) (j : ℤ) :
    volume {t' : ℝ | ⌊t' / s⌋ = j} ≤ ENNReal.ofReal s := by
  calc volume {t' : ℝ | ⌊t' / s⌋ = j} ≤ volume (Icc ((j : ℝ) * s) ((j + 1) * s)) := by
        apply measure_mono
        intro t' ht'
        simp only [mem_setOf_eq] at ht'
        have h1 := Int.floor_le (t' / s)
        have h2 := Int.lt_floor_add_one (t' / s)
        rw [ht'] at h1 h2
        constructor
        · rw [← le_div_iff₀ hs]; exact h1
        · have := (div_lt_iff₀ hs).mp h2; linarith
    _ = ENNReal.ofReal s := by rw [Real.volume_Icc]; congr 1; ring

omit [MeasurableSpace Ω] in
theorem abs_xbar_le {β γ : Ω → ℝ} {K : ℝ} (hβ : ∀ l, |β l| ≤ K) (hγ : ∀ l, |γ l| ≤ K)
    {l : Ω} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |xbar β γ l t| ≤ 2 * K := by
  unfold xbar
  have h1 := hβ l
  have h2 : |t * γ l| ≤ K := by
    rw [abs_mul, abs_of_nonneg ht.1]
    calc t * |γ l| ≤ 1 * |γ l| := by gcongr; exact ht.2
      _ ≤ K := by rw [one_mul]; exact hγ l
  calc |β l + t * γ l| ≤ |β l| + |t * γ l| := abs_add_le _ _
    _ ≤ 2 * K := by linarith

/-- The floor of a value bounded by `2K` lies in `[-R, R]`, `R = ⌈2K/s⌉ + 1`. -/
theorem floor_mem_range {v K s : ℝ} (hs : 0 < s) (hv : |v| ≤ 2 * K) :
    ⌊v / s⌋ ∈ Finset.Icc (-(⌈2 * K / s⌉ + 1)) (⌈2 * K / s⌉ + 1) := by
  rw [abs_le] at hv
  have h1 : v / s ≤ 2 * K / s := div_le_div_of_nonneg_right hv.2 hs.le
  have h2 : -(2 * K / s) ≤ v / s := by rw [← neg_div]; exact div_le_div_of_nonneg_right hv.1 hs.le
  have h3 := Int.le_ceil (2 * K / s)
  have h4 := Int.floor_le (v / s)
  have h5 := Int.lt_floor_add_one (v / s)
  rw [Finset.mem_Icc]
  constructor
  · have : ((-(⌈2 * K / s⌉ + 1) : ℤ) : ℝ) < ⌊v / s⌋ + 1 := by push_cast; linarith
    have : (-(⌈2 * K / s⌉ + 1) : ℤ) < ⌊v / s⌋ + 1 := by exact_mod_cast this
    omega
  · have : ((⌊v / s⌋ : ℤ) : ℝ) ≤ ((⌈2 * K / s⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- Two witnesses of one block and one static group whose scalars share a cell at a common time
have `x̄`-cells less than `4K + 2` apart. -/
theorem cell_close {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {F : ℝ → Fin 2 → ℝ} {K s : ℝ}
    (hK : 0 ≤ K) (hs : 0 < s) (hγ : ∀ l, |γ l| ≤ K) (hF : ∀ t i, |F t i| ≤ K)
    {l l' : Ω} {t t' u : ℝ} {x x' : ℤ} (ht : |u - t| < s) (ht' : |u - t'| < s)
    (hx : ⌊xbar β γ l t / s⌋ = x) (hx' : ⌊xbar β γ l' t' / s⌋ = x')
    (hy : ∀ i, |y l i - y l' i| < s)
    (hS : ⌊scal y β γ F l u / s⌋ = ⌊scal y β γ F l' u / s⌋) :
    ((x - x' : ℤ) : ℝ) < 4 * K + 2 := by
  have hS' := abs_sub_lt_of_floor_eq hs hS
  have hx1 : (x : ℝ) * s ≤ xbar β γ l t := by
    have := Int.floor_le (xbar β γ l t / s); rw [hx] at this
    rwa [le_div_iff₀ hs] at this
  have hx2 : xbar β γ l' t' < ((x' : ℝ) + 1) * s := by
    have := Int.lt_floor_add_one (xbar β γ l' t' / s); rw [hx'] at this
    rwa [div_lt_iff₀ hs] at this
  have e1 : |xbar β γ l u - xbar β γ l t| ≤ s * K := by
    unfold xbar
    rw [show β l + u * γ l - (β l + t * γ l) = (u - t) * γ l by ring, abs_mul]
    exact mul_le_mul ht.le (hγ l) (abs_nonneg _) hs.le
  have e2 : |xbar β γ l' u - xbar β γ l' t'| ≤ s * K := by
    unfold xbar
    rw [show β l' + u * γ l' - (β l' + t' * γ l') = (u - t') * γ l' by ring, abs_mul]
    exact mul_le_mul ht'.le (hγ l') (abs_nonneg _) hs.le
  have e3 : |F u 0 * (y l 0 - y l' 0) + F u 1 * (y l 1 - y l' 1)| ≤ 2 * K * s := by
    calc |F u 0 * (y l 0 - y l' 0) + F u 1 * (y l 1 - y l' 1)|
        ≤ |F u 0 * (y l 0 - y l' 0)| + |F u 1 * (y l 1 - y l' 1)| := abs_add_le _ _
      _ ≤ K * s + K * s := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul (hF u 0) (hy 0).le (abs_nonneg _) hK)
            (mul_le_mul (hF u 1) (hy 1).le (abs_nonneg _) hK)
      _ = 2 * K * s := by ring
  have e4 : scal y β γ F l u - scal y β γ F l' u = (xbar β γ l u - xbar β γ l' u) -
      (F u 0 * (y l 0 - y l' 0) + F u 1 * (y l 1 - y l' 1)) := by unfold scal; ring
  rw [e4] at hS'
  have a1 := (abs_lt.mp hS').2
  have a2 := (abs_le.mp e1).1
  have a3 := (abs_le.mp e2).2
  have a4 := (abs_le.mp e3).2
  have : ((x : ℝ) - x') * s < (4 * K + 2) * s := by linarith
  push_cast
  exact lt_of_mul_lt_mul_right this hs.le

/-- **Spacetime count in one static group.** -/
theorem spacetime_count {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {F : ℝ → Fin 2 → ℝ}
    {K s K₂ B : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hK₂ : 0 < K₂) (hB : 0 ≤ B)
    (hβ : ∀ l, |β l| ≤ K) (hγ : ∀ l, |γ l| ≤ K) (hF : ∀ t i, |F t i| ≤ K)
    {E : Set (Ω × ℝ)} (hE : MeasurableSet E) (hE01 : E ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hsupp : ∀ t, ∃ C : Finset ℤ, (C.card : ℝ) ≤ B ∧
      ∀ l, (l, t) ∈ E → ⌊scal y β γ F l t / s⌋ ∈ C)
    (Y : Fin 2 → ℤ) :
    ∃ Fs : Finset (ℤ × ℤ), (Fs.card : ℝ) ≤ (1 / s + 1) * (K₂ * ((4 * K + 3) * B)) ∧
      ∀ l t, (l, t) ∈ pairGood E s K₂ → (∀ i, ⌊y l i / s⌋ = Y i) →
        (⌊t / s⌋, ⌊xbar β γ l t / s⌋) ∈ Fs := by
  classical
  set J : ℕ := ⌊1 / s⌋₊ with hJ
  set R : ℤ := ⌈2 * K / s⌉ + 1 with hR
  set occ : ℤ → ℤ → Prop := fun j x => ∃ l t, (l, t) ∈ pairGood E s K₂ ∧
    (∀ i, ⌊y l i / s⌋ = Y i) ∧ ⌊t / s⌋ = j ∧ ⌊xbar β γ l t / s⌋ = x with hocc
  set X : ℤ → Finset ℤ := fun j => (Finset.Icc (-R) R).filter (occ j) with hX
  set Fs : Finset (ℤ × ℤ) :=
    (Finset.range (J + 1)).biUnion fun j => (X j).image fun x => ((j : ℤ), x) with hFs
  -- the count in one block
  have hXc : ∀ j : ℤ, ((X j).card : ℝ) ≤ K₂ * ((4 * K + 3) * B) := by
    intro j
    rcases (X j).eq_empty_or_nonempty with hXe | ⟨x₀, hx₀⟩
    · rw [hXe, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hK₂.le (mul_nonneg (by linarith) hB)
    have hw : ∀ x ∈ X j, ∃ l t, (l, t) ∈ pairGood E s K₂ ∧ (∀ i, ⌊y l i / s⌋ = Y i) ∧
        ⌊t / s⌋ = j ∧ ⌊xbar β γ l t / s⌋ = x := fun x hx => (Finset.mem_filter.mp hx).2
    haveI : Nonempty Ω := ⟨(hw x₀ hx₀).choose⟩
    choose! wl wt hwp hwY hwj hwx using hw
    set A : ℤ → Set ℝ := fun x => {t' | (wl x, t') ∈ E ∧ ⌊t' / s⌋ = j} with hAdef
    have hAm : ∀ x, MeasurableSet (A x) := by
      intro x
      exact (measurable_prodMk_left hE).inter (measurableSet_block s j)
    have hAvol : ∀ x ∈ X j, ENNReal.ofReal (s / K₂) ≤ volume (A x) := by
      intro x hx
      have h := (hwp x hx).2
      rw [hwj x hx] at h
      exact h
    -- pointwise: at most `(4K + 3) B` witnesses are labeled at any time of the block
    have hpt : ∀ t' : ℝ, ⌊t' / s⌋ = j →
        (((X j).filter fun x => (wl x, t') ∈ E).card : ℝ) ≤ (4 * K + 3) * B := by
      intro t' ht'
      obtain ⟨C, hC, hCmem⟩ := hsupp t'
      set W := (X j).filter fun x => (wl x, t') ∈ E with hW
      set φ : ℤ → ℤ := fun x => ⌊scal y β γ F (wl x) t' / s⌋ with hφ
      have himg : W.image φ ⊆ C := by
        intro b hb
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
        exact hCmem _ (Finset.mem_filter.mp hx).2
      have hfiber : ∀ b ∈ W.image φ, (W.filter fun x => φ x = b).card ≤ ⌈4 * K + 2⌉₊ := by
        intro b hb
        obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hb
        set f := W.filter fun x => φ x = φ x₀ with hf
        have hne : f.Nonempty := ⟨x₀, Finset.mem_filter.mpr ⟨hx₀, rfl⟩⟩
        set m := f.min' hne with hm
        have hsub : f ⊆ Finset.Ico m (m + ⌈4 * K + 2⌉₊) := by
          intro x hx
          have hmx : m ≤ x := f.min'_le x hx
          have hmf : m ∈ f := f.min'_mem hne
          obtain ⟨hxW, hxφ⟩ := Finset.mem_filter.mp hx
          obtain ⟨hmW, hmφ⟩ := Finset.mem_filter.mp hmf
          obtain ⟨hxX, hxE⟩ := Finset.mem_filter.mp hxW
          obtain ⟨hmX, hmE⟩ := Finset.mem_filter.mp hmW
          have hclose : ((x - m : ℤ) : ℝ) < 4 * K + 2 := by
            refine cell_close (y := y) (F := F) hK hs hγ hF (u := t')
              (abs_sub_lt_of_floor_eq hs (ht'.trans (hwj x hxX).symm))
              (abs_sub_lt_of_floor_eq hs (ht'.trans (hwj m hmX).symm))
              (hwx x hxX) (hwx m hmX) (fun i => abs_sub_lt_of_floor_eq hs
                ((hwY x hxX i).trans (hwY m hmX i).symm)) ?_
            exact hxφ.trans hmφ.symm
          have hceil : (4 * K + 2 : ℝ) ≤ (⌈4 * K + 2⌉₊ : ℝ) := Nat.le_ceil _
          have : ((x - m : ℤ) : ℝ) < ((⌈4 * K + 2⌉₊ : ℤ) : ℝ) := by
            push_cast at hclose ⊢; linarith
          have : x - m < (⌈4 * K + 2⌉₊ : ℤ) := by exact_mod_cast this
          rw [Finset.mem_Ico]; constructor <;> omega
        calc f.card ≤ (Finset.Ico m (m + ⌈4 * K + 2⌉₊)).card := Finset.card_le_card hsub
          _ = ⌈4 * K + 2⌉₊ := by simp
      have h1 := Finset.card_le_mul_card_image W ⌈4 * K + 2⌉₊ hfiber
      have h2 : ((W.image φ).card : ℝ) ≤ B := (by exact_mod_cast Finset.card_le_card himg :
        ((W.image φ).card : ℝ) ≤ C.card).trans hC
      have h3 : (⌈4 * K + 2⌉₊ : ℝ) ≤ 4 * K + 3 := by
        have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * K + 2 by linarith); linarith
      calc (W.card : ℝ) ≤ (⌈4 * K + 2⌉₊ * (W.image φ).card : ℕ) := by exact_mod_cast h1
        _ = (⌈4 * K + 2⌉₊ : ℝ) * (W.image φ).card := by push_cast; ring
        _ ≤ (4 * K + 3) * B := mul_le_mul h3 h2 (Nat.cast_nonneg _) (by linarith)
    -- integrate over the block
    have hsum : ((X j).card : ENNReal) * ENNReal.ofReal (s / K₂) ≤
        ENNReal.ofReal ((4 * K + 3) * B) * ENNReal.ofReal s := by
      calc ((X j).card : ENNReal) * ENNReal.ofReal (s / K₂)
          = ∑ _x ∈ X j, ENNReal.ofReal (s / K₂) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ X j, volume (A x) := Finset.sum_le_sum hAvol
        _ = ∑ x ∈ X j, ∫⁻ t', (A x).indicator 1 t' := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [lintegral_indicator_one (hAm x)]
        _ = ∫⁻ t', ∑ x ∈ X j, (A x).indicator 1 t' := by
            rw [lintegral_finset_sum]
            intro x _
            exact measurable_one.indicator (hAm x)
        _ ≤ ∫⁻ t', {t' : ℝ | ⌊t' / s⌋ = j}.indicator
              (fun _ => ENNReal.ofReal ((4 * K + 3) * B)) t' := by
            refine lintegral_mono fun t' => ?_
            by_cases ht' : ⌊t' / s⌋ = j
            · rw [indicator_of_mem (show t' ∈ {t' : ℝ | ⌊t' / s⌋ = j} from ht')]
              have e : ∑ x ∈ X j, (A x).indicator (1 : ℝ → ENNReal) t' =
                  (((X j).filter fun x => (wl x, t') ∈ E).card : ENNReal) := by
                rw [Finset.card_filter]
                push_cast
                refine Finset.sum_congr rfl fun x _ => ?_
                by_cases hx : (wl x, t') ∈ E
                · rw [indicator_of_mem (show t' ∈ A x from ⟨hx, ht'⟩), if_pos hx]; rfl
                · rw [indicator_of_notMem (show t' ∉ A x from fun h => hx h.1), if_neg hx]
              rw [e, ← ENNReal.ofReal_natCast]
              exact ENNReal.ofReal_le_ofReal (hpt t' ht')
            · have e : ∀ x, (A x).indicator (1 : ℝ → ENNReal) t' = 0 := fun x =>
                indicator_of_notMem (fun h => ht' h.2) _
              simp only [e, Finset.sum_const_zero]
              exact bot_le
        _ = ENNReal.ofReal ((4 * K + 3) * B) * volume {t' : ℝ | ⌊t' / s⌋ = j} := by
            rw [lintegral_indicator_const (measurableSet_block s j)]
        _ ≤ ENNReal.ofReal ((4 * K + 3) * B) * ENNReal.ofReal s := by
            gcongr; exact volume_block_le hs j
    have hKB : 0 ≤ (4 * K + 3) * B := mul_nonneg (by linarith) hB
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul hKB] at hsum
    have h := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKB hs.le)).mp hsum
    have h' : ((X j).card : ℝ) * s ≤ K₂ * ((4 * K + 3) * B) * s := by
      have := mul_le_mul_of_nonneg_left h hK₂.le
      calc ((X j).card : ℝ) * s = K₂ * ((X j).card * (s / K₂)) := by field_simp
        _ ≤ K₂ * ((4 * K + 3) * B * s) := this
        _ = K₂ * ((4 * K + 3) * B) * s := by ring
    exact le_of_mul_le_mul_right h' hs
  refine ⟨Fs, ?_, ?_⟩
  · calc (Fs.card : ℝ) ≤ ∑ j ∈ Finset.range (J + 1), (((X j).image fun x => ((j : ℤ), x)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ Finset.range (J + 1), K₂ * ((4 * K + 3) * B) := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact (by exact_mod_cast Finset.card_image_le :
            (((X j).image fun x => ((j : ℤ), x)).card : ℝ) ≤ (X j).card).trans (hXc j)
      _ = ((J : ℝ) + 1) * (K₂ * ((4 * K + 3) * B)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ (1 / s + 1) * (K₂ * ((4 * K + 3) * B)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hK₂.le (mul_nonneg (by linarith) hB))
          have := Nat.floor_le (show 0 ≤ 1 / s by positivity)
          linarith
  · intro l t hp hY
    have ht01 := (hE01 hp.1).2
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Int.floor_nonneg.mpr (div_nonneg ht01.1 hs.le))
    have hnJ : n ≤ J := by
      have : (n : ℝ) ≤ t / s := by rw [← Int.cast_natCast, ← hn]; exact Int.floor_le _
      have h2 : t / s ≤ 1 / s := div_le_div_of_nonneg_right ht01.2 hs.le
      exact Nat.le_floor (this.trans h2)
    have hxR := floor_mem_range hs (abs_xbar_le hβ hγ (l := l) ht01)
    rw [hFs, Finset.mem_biUnion]
    refine ⟨n, Finset.mem_range.mpr (by omega), Finset.mem_image.mpr
      ⟨⌊xbar β γ l t / s⌋, Finset.mem_filter.mpr ⟨hxR, l, t, hp, hY, hn, rfl⟩, ?_⟩⟩
    rw [hn]

end Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

end
