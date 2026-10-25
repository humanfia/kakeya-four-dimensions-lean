import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.GroupSum
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Transfer

/-!
# The cover pairs at the reading time

`cover_pairs`: trajectories labeled at `ts` whose residual slopes lie within `w' + V` of a
center depending only on their group (`2(w' + V) ≤ w`) contain a half-dense part `L₁` on which
the pairs `(⌊S(ts)/w⌋, ⌊(γ - A · y)/w⌋)` take few values. The coarse bin `Z = ⌊S(ts)/w⌋`, the
fine bin `Y` = group, the dyadic coefficient bin `X` at side `r ∈ [w/2, w]` and the value
`J = ⌊(γ - A · y)/w⌋` are fed to `success_restriction` and `transfer_core`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The dyadic coefficient bin of a trajectory. -/
def coefBin (y : Ω → Fin 2 → ℝ) (β γ : Ω → ℝ) (r : ℝ) (l : Ω) : Fin 4 → ℤ :=
  ![⌊y l 0 / r⌋, ⌊y l 1 / r⌋, ⌊β l / r⌋, ⌊γ l / r⌋]

theorem coefBin_eq_iff {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {r : ℝ} {l : Ω} {x : Fin 4 → ℤ} :
    coefBin y β γ r l = x ↔ (⌊y l 0 / r⌋ = x 0 ∧ ⌊y l 1 / r⌋ = x 1 ∧ ⌊β l / r⌋ = x 2 ∧
      ⌊γ l / r⌋ = x 3) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    fin_cases i <;> simp [coefBin, h0, h1, h2, h3]

theorem measurableSet_coefBin_preimage {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} (hy : Measurable y)
    (hβ : Measurable β) (hγ : Measurable γ) (r : ℝ) (s : Set (Fin 4 → ℤ)) :
    MeasurableSet (coefBin y β γ r ⁻¹' s) := by
  have hy0 : Measurable fun l => y l 0 := (measurable_pi_apply 0).comp hy
  have hy1 : Measurable fun l => y l 1 := (measurable_pi_apply 1).comp hy
  have hm : Measurable (coefBin y β γ r) := by
    unfold coefBin
    refine measurable_pi_iff.mpr (fun i => ?_)
    fin_cases i
    · exact Int.measurable_floor.comp (hy0.div_const r)
    · exact Int.measurable_floor.comp (hy1.div_const r)
    · exact Int.measurable_floor.comp (hβ.div_const r)
    · exact Int.measurable_floor.comp (hγ.div_const r)
  exact hm (DiscreteMeasurableSpace.forall_measurableSet s)

/-- A value in the window `[c - ρ, c + ρ]` has its `w`-floor in a two-element set when
`2 ρ ≤ w`. -/
theorem floor_mem_window {x c ρ w : ℝ} (hw : 0 < w) (hρ : 2 * ρ ≤ w) (hx : |x - c| ≤ ρ) :
    ⌊x / w⌋ ∈ ({⌊(c - ρ) / w⌋, ⌊(c - ρ) / w⌋ + 1} : Finset ℤ) := by
  have h1 : (c - ρ) / w ≤ x / w := div_le_div_of_nonneg_right (by linarith [(abs_le.mp hx).1])
    hw.le
  have h2 : x / w ≤ (c - ρ) / w + 1 := by
    rw [div_add_one hw.ne', div_le_div_iff_of_pos_right hw]; linarith [(abs_le.mp hx).2]
  have a1 : ⌊(c - ρ) / w⌋ ≤ ⌊x / w⌋ := Int.floor_le_floor h1
  have a2 : ⌊x / w⌋ ≤ ⌊(c - ρ) / w⌋ + 1 := by
    calc ⌊x / w⌋ ≤ ⌊(c - ρ) / w + 1⌋ := Int.floor_le_floor h2
      _ = ⌊(c - ρ) / w⌋ + 1 := Int.floor_add_one _
  rcases eq_or_lt_of_le a1 with h | h
  · simp [← h]
  · have : ⌊x / w⌋ = ⌊(c - ρ) / w⌋ + 1 := by omega
    simp [this]

/-- Nearby values have nearby floors. -/
theorem floor_near {a b K H : ℝ} (hH : 0 < H) (hK : 0 ≤ K) (h : |a - b| ≤ K * H) :
    ⌊a / H⌋ ∈ Finset.Icc (⌊b / H⌋ - ((⌈K⌉₊ : ℤ) + 1)) (⌊b / H⌋ + ((⌈K⌉₊ : ℤ) + 1)) := by
  have a1 := Int.floor_le (a / H)
  have a2 := Int.lt_floor_add_one (a / H)
  have b1 := Int.floor_le (b / H)
  have b2 := Int.lt_floor_add_one (b / H)
  have hK' : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
  have hd : |a / H - b / H| ≤ K := by
    rw [← sub_div, abs_div, abs_of_pos hH, div_le_iff₀ hH]; linarith
  rw [Finset.mem_Icc]
  constructor
  · have : (⌊b / H⌋ : ℝ) - ((⌈K⌉₊ : ℝ) + 1) < (⌊a / H⌋ : ℝ) + 1 := by
      linarith [(abs_le.mp hd).1]
    have : ⌊b / H⌋ - ((⌈K⌉₊ : ℤ) + 1) < ⌊a / H⌋ + 1 := by exact_mod_cast this
    omega
  · have : (⌊a / H⌋ : ℝ) < (⌊b / H⌋ : ℝ) + ((⌈K⌉₊ : ℝ) + 1) + 1 := by
      linarith [(abs_le.mp hd).2]
    have : ⌊a / H⌋ < ⌊b / H⌋ + ((⌈K⌉₊ : ℤ) + 1) + 1 := by exact_mod_cast this
    omega

theorem card_Icc_near (n : ℤ) (K : ℝ) :
    ((Finset.Icc (n - ((⌈K⌉₊ : ℤ) + 1)) (n + ((⌈K⌉₊ : ℤ) + 1))).card : ℝ) = 2 * ⌈K⌉₊ + 3 := by
  rw [Int.card_Icc]
  have : n + ((⌈K⌉₊ : ℤ) + 1) + 1 - (n - ((⌈K⌉₊ : ℤ) + 1)) = 2 * (⌈K⌉₊ : ℤ) + 3 := by ring
  rw [this]
  have h0 : (0 : ℤ) ≤ 2 * (⌈K⌉₊ : ℤ) + 3 := by positivity
  rw [show ((2 * (⌈K⌉₊ : ℤ) + 3).toNat : ℝ) = ((2 * (⌈K⌉₊ : ℤ) + 3 : ℤ) : ℝ) from
    by exact_mod_cast Int.toNat_of_nonneg h0]
  push_cast; ring

/-- A value of a bounded affine form over a coefficient cell lies in a window. -/
theorem window_of_cell {v c r : ℝ} {n : ℤ} (hr : 0 < r) (h : ⌊v / r⌋ = n) :
    |v - n * r| ≤ r := by
  have a1 := Int.floor_le (v / r)
  have a2 := Int.lt_floor_add_one (v / r)
  rw [h, le_div_iff₀ hr] at a1
  rw [h, div_lt_iff₀ hr] at a2
  rw [abs_le]; constructor <;> linarith

/-- The bound on the number of cover pairs. -/
def pairBound (K KA d w mL : ℝ) : ℝ :=
  (2 * (2 * K + 2 * K ^ 2) + 2) * (K * (1 / w) ^ d) * (K * (2 * ⌈K⌉₊ + 3)) ^ 2 *
    (9 * (6 * K + 3) * K * 2 ^ d) * ((⌈4 * KA + 4⌉₊ * ⌈4 * K + 6⌉₊ : ℕ) : ℝ) * (4 / mL) ^ 2

/-- The absolute fine-bin bound inside a dyadic coefficient bin. -/
theorem fine_in_coef {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : Data ν y β γ E F d K ζ) (hK : 0 ≤ K) (hd : 0 ≤ d)
    {t₀ ts H w : ℝ} (hH : 0 < H) (hζH : ζ ≤ H) (hts0 : ts - t₀ ∈ Icc (0 : ℝ) H) {n : ℕ}
    (hrw : (2 : ℝ) ^ (-(n : ℤ)) ≤ w) (hwr : w ≤ 2 * (2 : ℝ) ^ (-(n : ℤ)))
    (hHr : H ≤ (2 : ℝ) ^ (-(n : ℤ))) {L : Set Ω} (hLE : ∀ l ∈ L, (l, ts) ∈ E)
    (x : Fin 4 → ℤ) (c : ℤ) :
    ν (L ∩ (fun l => ⌊baseVal y β γ F t₀ ts l / H⌋) ⁻¹' {c} ∩
        coefBin y β γ ((2 : ℝ) ^ (-(n : ℤ))) ⁻¹' {x}) ≤
      ENNReal.ofReal (9 * (6 * K + 3) * K * 2 ^ d / (w / H) ^ d) *
        ν (coefBin y β γ ((2 : ℝ) ^ (-(n : ℤ))) ⁻¹' {x}) := by
  set r : ℝ := (2 : ℝ) ^ (-(n : ℤ)) with hr
  have hr0 : 0 < r := zpow_pos (by norm_num) _
  have hw0 : 0 < w := hr0.trans_le hrw
  have key := slab_binCap h hK (t := ts) (q := H) (σ := r) (ω := (2 * K + 1) * H)
    (y00 := x 0 * r) (y10 := x 1 * r) (s₀ := c * H - K * H) (n := n) hζH hHr hH hr0.le
    (by positivity) x
    (L ∩ (fun l => ⌊baseVal y β γ F t₀ ts l / H⌋) ⁻¹' {c} ∩ coefBin y β γ r ⁻¹' {x}) (by
      rintro l ⟨⟨hlL, hlc⟩, hlx⟩
      simp only [mem_preimage, mem_singleton_iff] at hlc hlx
      obtain ⟨h0, h1, h2, h3⟩ := coefBin_eq_iff.mp hlx
      have w0 := window_of_cell (c := 0) hr0 h0
      have w1 := window_of_cell (c := 0) hr0 h1
      have f0 := Int.floor_le (y l 0 / r)
      have f0' := Int.lt_floor_add_one (y l 0 / r)
      have f1 := Int.floor_le (y l 1 / r)
      have f1' := Int.lt_floor_add_one (y l 1 / r)
      rw [h0, le_div_iff₀ hr0] at f0
      rw [h0, div_lt_iff₀ hr0] at f0'
      rw [h1, le_div_iff₀ hr0] at f1
      rw [h1, div_lt_iff₀ hr0] at f1'
      have b1 := Int.floor_le (baseVal y β γ F t₀ ts l / H)
      have b2 := Int.lt_floor_add_one (baseVal y β γ F t₀ ts l / H)
      rw [hlc, le_div_iff₀ hH] at b1
      rw [hlc, div_lt_iff₀ hH] at b2
      have hdiff : |scal y β γ F l ts - baseVal y β γ F t₀ ts l| ≤ K * H := by
        have : scal y β γ F l ts - baseVal y β γ F t₀ ts l = (ts - t₀) * γ l := by
          unfold scal baseVal xbar; ring
        rw [this, abs_mul, mul_comm]
        exact mul_le_mul (h.bound_γ l) (by rw [abs_le]; constructor <;> linarith [hts0.1, hts0.2])
          (abs_nonneg _) hK
      have hd' := abs_le.mp hdiff
      exact ⟨⟨h0, h1, h2, h3⟩, hLE l hlL, by linarith, by linarith, by linarith, by linarith,
        by linarith, by nlinarith⟩)
  refine key.trans ?_
  have hbin : {l | ⌊y l 0 / r⌋ = x 0 ∧ ⌊y l 1 / r⌋ = x 1 ∧ ⌊β l / r⌋ = x 2 ∧ ⌊γ l / r⌋ = x 3} =
      coefBin y β γ r ⁻¹' {x} := by
    ext l; simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff, coefBin_eq_iff]
  rw [hbin]
  apply mul_le_mul_of_nonneg_right _ bot_le
  apply ENNReal.ofReal_le_ofReal
  -- numerics
  have hrH : 1 ≤ r / H := (le_div_iff₀ hH).mpr (by linarith)
  have hsq : (r / H + 2) ^ 2 ≤ 9 * (r / H) ^ 2 := by nlinarith
  have hω : (2 * K + 1) * H / H + 4 * K + 2 = 6 * K + 3 := by field_simp; ring
  rw [hω]
  have hHr0 : 0 < H / r := div_pos hH hr0
  have hpow : (H / r) ^ (2 + d) = (H / r) ^ 2 * (H / r) ^ d := by
    rw [Real.rpow_add hHr0, Real.rpow_two]
  have hHrw : H / r ≤ 2 * (H / w) := by
    rw [div_le_iff₀ hr0]
    have : 2 * (H / w) * r = H * (2 * r / w) := by ring
    rw [this]
    have : 1 ≤ 2 * r / w := by rw [le_div_iff₀ hw0]; linarith
    nlinarith
  have hdpow : (H / r) ^ d ≤ 2 ^ d * (H / w) ^ d := by
    rw [← Real.mul_rpow (by norm_num) (div_pos hH hw0).le]
    exact Real.rpow_le_rpow hHr0.le hHrw hd
  have hM : 9 * (6 * K + 3) * K * 2 ^ d / (w / H) ^ d = 9 * (6 * K + 3) * K * 2 ^ d * (H / w) ^ d := by
    rw [div_eq_mul_inv, ← Real.inv_rpow (div_pos hw0 hH).le, inv_div]
  rw [hM, hpow]
  have h1 : (r / H) ^ 2 * (H / r) ^ 2 = 1 := by
    rw [← mul_pow, div_mul_div_cancel₀ hH.ne', div_self hr0.ne', one_pow]
  have hK3 : 0 ≤ (6 * K + 3) * K := by positivity
  calc (r / H + 2) ^ 2 * (6 * K + 3) * (K * ((H / r) ^ 2 * (H / r) ^ d))
      ≤ 9 * (r / H) ^ 2 * (6 * K + 3) * (K * ((H / r) ^ 2 * (H / r) ^ d)) := by
        gcongr
    _ = 9 * (6 * K + 3) * K * ((r / H) ^ 2 * (H / r) ^ 2) * (H / r) ^ d := by ring
    _ = 9 * (6 * K + 3) * K * (H / r) ^ d := by rw [h1]; ring
    _ ≤ 9 * (6 * K + 3) * K * (2 ^ d * (H / w) ^ d) := by gcongr
    _ = 9 * (6 * K + 3) * K * 2 ^ d * (H / w) ^ d := by ring

/-- The cover pairs at the reading time. -/
theorem cover_pairs {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : Data ν y β γ E F d K ζ) (hK : 1 ≤ K) (hd : 0 ≤ d)
    {t₀ ts H w : ℝ} (hH : 0 < H) (hζH : ζ ≤ H) (hHw : H ≤ w) (hw1 : w ≤ 1)
    (hts : ts ∈ Icc (0 : ℝ) 1) (hts0 : ts - t₀ ∈ Icc (0 : ℝ) H) {n : ℕ}
    (hrw : (2 : ℝ) ^ (-(n : ℤ)) ≤ w) (hwr : w ≤ 2 * (2 : ℝ) ^ (-(n : ℤ)))
    (hHr : H ≤ (2 : ℝ) ^ (-(n : ℤ)))
    {A : Fin 2 → ℝ} {KA : ℝ} (hKA : 0 ≤ KA) (hA : ∀ i, |A i| ≤ KA)
    {L₀ : Set Ω} (hL₀ : MeasurableSet L₀) (hL₀E : ∀ l ∈ L₀, (l, ts) ∈ E)
    {κ : ℤ → ℝ} {ρ : ℝ} (hρ : 2 * ρ ≤ w)
    (hwin : ∀ l ∈ L₀, |resSlope y γ A l - κ ⌊baseVal y β γ F t₀ ts l / H⌋| ≤ ρ)
    {mL : ℝ} (hmL : 0 < mL) (hmass : ENNReal.ofReal mL ≤ ν L₀) :
    ∃ L₁ ⊆ L₀, MeasurableSet L₁ ∧ ENNReal.ofReal (mL / 2) ≤ ν L₁ ∧
      ∃ P : Finset (ℤ × ℤ), (P.card : ℝ) ≤ pairBound K KA d w mL ∧
        ∀ l ∈ L₁, (⌊scal y β γ F l ts / w⌋, ⌊resSlope y γ A l / w⌋) ∈ P := by
  classical
  have hK0 : 0 ≤ K := by linarith
  set r : ℝ := (2 : ℝ) ^ (-(n : ℤ)) with hr
  have hr0 : 0 < r := zpow_pos (by norm_num) _
  have hw0 : 0 < w := hr0.trans_le hrw
  set M : ℝ := (w / H) ^ d with hMdef
  have hM : 0 < M := Real.rpow_pos_of_pos (div_pos hw0 hH) _
  set R : ℝ := 2 * K + 2 * K ^ 2 with hRdef
  set kk : ℤ := (⌈K⌉₊ : ℤ) + 1 with hkk
  set KY : ℝ := K * (2 * ⌈K⌉₊ + 3) with hKY
  set anum : ℝ := 9 * (6 * K + 3) * K * 2 ^ d with hanum
  set s₀ : ℝ := mL / 4 with hs₀
  set K₀ : ℕ := ⌈4 * KA + 4⌉₊ * ⌈4 * K + 6⌉₊ with hK₀
  set c₀ : ℝ := anum / s₀ with hc₀
  set θ : ℝ := s₀ / (c₀ * K₀) with hθ
  have hs₀p : 0 < s₀ := by positivity
  have hanum0 : 0 < anum := by positivity
  have hK₀p : 0 < (K₀ : ℝ) := by
    rw [hK₀]; push_cast
    have : 0 < (⌈4 * KA + 4⌉₊ : ℝ) := by
      have := Nat.le_ceil (4 * KA + 4); positivity
    have : 0 < (⌈4 * K + 6⌉₊ : ℝ) := by
      have := Nat.le_ceil (4 * K + 6); positivity
    positivity
  have hc₀p : 0 < c₀ := by positivity
  have hθp : 0 < θ := by positivity
  -- the maps
  let X : Ω → Fin 4 → ℤ := coefBin y β γ r
  let Y : Ω → ℤ := fun l => ⌊baseVal y β γ F t₀ ts l / H⌋
  let Z : Ω → ℤ := fun l => ⌊scal y β γ F l ts / w⌋
  let J : Ω → ℤ := fun l => ⌊resSlope y γ A l / w⌋
  have hXm : ∀ s : Set (Fin 4 → ℤ), MeasurableSet (X ⁻¹' s) :=
    measurableSet_coefBin_preimage h.measurable_y h.measurable_β h.measurable_γ r
  have hYm : Measurable Y :=
    Int.measurable_floor.comp ((measurable_baseVal h.measurable_y h.measurable_β h.measurable_γ
      F t₀ ts).div_const H)
  -- the coarse bins
  obtain ⟨Zs, hZs, hZsmem⟩ := support_global h hK0 ts (q := w) (R := R) (hζH.trans hHw) hw1 hw0
    (by positivity)
  -- the fine bins of each coarse bin
  choose C hC hCmem using fun z : ℤ => h.support ts H w (z * w) hζH hHw hw1
  let Yset : ℤ → Finset ℤ := fun z => (C z).biUnion (fun m => Finset.Icc (m - kk) (m + kk))
  have hYset : ∀ z, ((Yset z).card : ℝ) ≤ KY * M := by
    intro z
    refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
    push_cast
    calc ∑ m ∈ C z, ((Finset.Icc (m - kk) (m + kk)).card : ℝ) = ∑ _m ∈ C z, (2 * ⌈K⌉₊ + 3 : ℝ) :=
          Finset.sum_congr rfl (fun m _ => card_Icc_near m K)
      _ = (C z).card * (2 * ⌈K⌉₊ + 3 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * (w / H) ^ d * (2 * ⌈K⌉₊ + 3 : ℝ) :=
          mul_le_mul_of_nonneg_right (hC z) (by positivity)
      _ = KY * M := by rw [hKY, hMdef]; ring
  -- the lists
  let listY : ℤ → Finset ℤ := fun g => {⌊(κ g - ρ) / w⌋, ⌊(κ g - ρ) / w⌋ + 1}
  let cX : (Fin 4 → ℤ) → ℝ := fun x => x 3 * r - (A 0 * (x 0 * r) + A 1 * (x 1 * r))
  let cZ : (Fin 4 → ℤ) → ℝ := fun x =>
    x 2 * r + ts * (x 3 * r) - (F ts 0 * (x 0 * r) + F ts 1 * (x 1 * r))
  let listX : (Fin 4 → ℤ) → Finset ℤ := fun x =>
    floorRange w (cX x - r * (1 + 2 * KA)) (2 * (r * (1 + 2 * KA)))
  let zlist : (Fin 4 → ℤ) → Finset ℤ := fun x =>
    floorRange w (cZ x - r * (2 + 2 * K)) (2 * (r * (2 + 2 * K)))
  have hrw' : r / w ≤ 1 := (div_le_one hw0).mpr hrw
  have h2c : ∀ x, (listX x).card * (zlist x).card ≤ K₀ := by
    intro x
    have a1 : ((listX x).card : ℝ) ≤ 4 * KA + 4 := by
      refine (card_floorRange_le hw0 (by positivity)).trans ?_
      have : 2 * (r * (1 + 2 * KA)) / w = 2 * (1 + 2 * KA) * (r / w) := by ring
      rw [this]; nlinarith
    have a2 : ((zlist x).card : ℝ) ≤ 4 * K + 6 := by
      refine (card_floorRange_le hw0 (by positivity)).trans ?_
      have : 2 * (r * (2 + 2 * K)) / w = 2 * (2 + 2 * K) * (r / w) := by ring
      rw [this]; nlinarith
    have b1 : (listX x).card ≤ ⌈4 * KA + 4⌉₊ := by exact_mod_cast a1.trans (Nat.le_ceil _)
    have b2 : (zlist x).card ≤ ⌈4 * K + 6⌉₊ := by exact_mod_cast a2.trans (Nat.le_ceil _)
    rw [hK₀]; exact Nat.mul_le_mul b1 b2
  -- membership facts on `L₀`
  have hcell : ∀ l, |y l 0 - (X l 0 : ℝ) * r| ≤ r ∧ |y l 1 - (X l 1 : ℝ) * r| ≤ r ∧
      |β l - (X l 2 : ℝ) * r| ≤ r ∧ |γ l - (X l 3 : ℝ) * r| ≤ r := by
    intro l
    exact ⟨window_of_cell (c := 0) hr0 rfl, window_of_cell (c := 0) hr0 rfl,
      window_of_cell (c := 0) hr0 rfl, window_of_cell (c := 0) hr0 rfl⟩
  have h1 : ∀ l ∈ L₀, J l ∈ listY (Y l) := fun l hl =>
    floor_mem_window hw0 hρ (hwin l hl)
  have h2 : ∀ l ∈ L₀, J l ∈ listX (X l) ∧ Z l ∈ zlist (X l) := by
    intro l _
    obtain ⟨c0, c1, c2, c3⟩ := hcell l
    have hA0 := hA 0
    have hA1 := hA 1
    have hF0 := h.bound_F ts 0
    have hF1 := h.bound_F ts 1
    constructor
    · apply floor_mem_floorRange hw0
      · have e : resSlope y γ A l - cX (X l) = (γ l - (X l 3 : ℝ) * r) -
            (A 0 * (y l 0 - (X l 0 : ℝ) * r) + A 1 * (y l 1 - (X l 1 : ℝ) * r)) := by
          simp only [resSlope, cX]; ring
        have : |resSlope y γ A l - cX (X l)| ≤ r * (1 + 2 * KA) := by
          rw [e]
          calc _ ≤ |γ l - (X l 3 : ℝ) * r| + (|A 0| * |y l 0 - (X l 0 : ℝ) * r| +
                |A 1| * |y l 1 - (X l 1 : ℝ) * r|) := by
                refine (abs_sub _ _).trans ?_
                gcongr
                rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
            _ ≤ r + (KA * r + KA * r) := by gcongr
            _ = r * (1 + 2 * KA) := by ring
        linarith [(abs_le.mp this).1]
      · have e : resSlope y γ A l - cX (X l) = (γ l - (X l 3 : ℝ) * r) -
            (A 0 * (y l 0 - (X l 0 : ℝ) * r) + A 1 * (y l 1 - (X l 1 : ℝ) * r)) := by
          simp only [resSlope, cX]; ring
        have : |resSlope y γ A l - cX (X l)| ≤ r * (1 + 2 * KA) := by
          rw [e]
          calc _ ≤ |γ l - (X l 3 : ℝ) * r| + (|A 0| * |y l 0 - (X l 0 : ℝ) * r| +
                |A 1| * |y l 1 - (X l 1 : ℝ) * r|) := by
                refine (abs_sub _ _).trans ?_
                gcongr
                rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
            _ ≤ r + (KA * r + KA * r) := by gcongr
            _ = r * (1 + 2 * KA) := by ring
        linarith [(abs_le.mp this).2]
    · have hts1 : |ts| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hts.1, hts.2]
      have e : scal y β γ F l ts - cZ (X l) = (β l - (X l 2 : ℝ) * r) +
          ts * (γ l - (X l 3 : ℝ) * r) -
          (F ts 0 * (y l 0 - (X l 0 : ℝ) * r) + F ts 1 * (y l 1 - (X l 1 : ℝ) * r)) := by
        simp only [scal, xbar, cZ]; ring
      have hb : |scal y β γ F l ts - cZ (X l)| ≤ r * (2 + 2 * K) := by
        rw [e]
        calc _ ≤ |β l - (X l 2 : ℝ) * r| + |ts| * |γ l - (X l 3 : ℝ) * r| +
              (|F ts 0| * |y l 0 - (X l 0 : ℝ) * r| + |F ts 1| * |y l 1 - (X l 1 : ℝ) * r|) := by
              refine (abs_sub _ _).trans ?_
              gcongr
              · rw [← abs_mul]; exact abs_add_le _ _
              · rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
          _ ≤ r + 1 * r + (K * r + K * r) := by gcongr
          _ = r * (2 + 2 * K) := by ring
      apply floor_mem_floorRange hw0
      · linarith [(abs_le.mp hb).1]
      · linarith [(abs_le.mp hb).2]
  have hZsL : ∀ l ∈ L₀, Z l ∈ Zs := fun l hl =>
    hZsmem l (hL₀E l hl) (scal_bound h hK0 hts l)
  have h4 : ∀ l ∈ L₀, Y l ∈ Yset (Z l) := by
    intro l hl
    have hlo : (Z l : ℝ) * w ≤ scal y β γ F l ts := by
      have := Int.floor_le (scal y β γ F l ts / w); rwa [le_div_iff₀ hw0] at this
    have hhi : scal y β γ F l ts ≤ (Z l : ℝ) * w + w := by
      have := Int.lt_floor_add_one (scal y β γ F l ts / w)
      rw [div_lt_iff₀ hw0] at this; linarith
    have hm := hCmem (Z l) l (hL₀E l hl) hlo hhi
    refine Finset.mem_biUnion.mpr ⟨_, hm, ?_⟩
    apply floor_near hH hK0
    have : baseVal y β γ F t₀ ts l - scal y β γ F l ts = -((ts - t₀) * γ l) := by
      unfold baseVal scal xbar; ring
    rw [this, abs_neg, abs_mul, mul_comm]
    exact mul_le_mul (h.bound_γ l) (by rw [abs_le]; constructor <;> linarith [hts0.1, hts0.2])
      (abs_nonneg _) hK0
  -- success restriction and transfer
  have h5abs : ∀ (x : Fin 4 → ℤ) (c : ℤ), ν (L₀ ∩ Y ⁻¹' {c} ∩ X ⁻¹' {x}) ≤
      ENNReal.ofReal (anum / M) * ν (X ⁻¹' {x}) :=
    fun x c => fine_in_coef h hK0 hd hH hζH hts0 hrw hwr hHr hL₀E x c
  obtain ⟨hloss, h5rel⟩ := success_restriction hL₀ hXm hYm (a := anum / M) (s₀ := s₀)
    (by positivity) hs₀p h5abs
  set good : Set (Fin 4 → ℤ) := {x | ENNReal.ofReal s₀ * ν (X ⁻¹' {x}) ≤ ν (L₀ ∩ X ⁻¹' {x})}
  set L₀' := L₀ ∩ X ⁻¹' good with hL₀'
  have hL₀'m : MeasurableSet L₀' := hL₀.inter (hXm good)
  have h5' : ∀ (S : Set (Fin 4 → ℤ)) (c : ℤ), ν (L₀' ∩ Y ⁻¹' {c} ∩ X ⁻¹' S) ≤
      ENNReal.ofReal (c₀ / M) * ν (L₀' ∩ X ⁻¹' S) := by
    intro S c
    refine (h5rel S c).trans (le_of_eq ?_)
    congr 2
    rw [hc₀]; field_simp
  have htc := transfer_core (ν := ν) hL₀'m hXm (J := J) (θ := θ) hM hc₀p.le
    (fun l hl => hZsL l hl.1) (fun l hl => h1 l hl.1) (fun l hl => h2 l hl.1) h2c
    (fun l hl => h4 l hl.1) h5'
  -- the final set
  set L₁ := L₀' ∩ {l | J l ∈ heavyVals Yset listY θ M (Z l)} with hL₁
  have hL₁m : MeasurableSet L₁ := by
    have hZm : Measurable Z := Int.measurable_floor.comp (by
      have hF := h.measurable_F
      have hy0m : Measurable fun l => y l 0 := (measurable_pi_apply 0).comp h.measurable_y
      have hy1m : Measurable fun l => y l 1 := (measurable_pi_apply 1).comp h.measurable_y
      have hβm := h.measurable_β
      have hγm := h.measurable_γ
      unfold scal xbar
      fun_prop)
    have hJm : Measurable J := Int.measurable_floor.comp (by
      have hy0m : Measurable fun l => y l 0 := (measurable_pi_apply 0).comp h.measurable_y
      have hy1m : Measurable fun l => y l 1 := (measurable_pi_apply 1).comp h.measurable_y
      have hγm := h.measurable_γ
      unfold resSlope
      fun_prop)
    have : {l | J l ∈ heavyVals Yset listY θ M (Z l)} =
        ⋃ z : ℤ, Z ⁻¹' {z} ∩ J ⁻¹' (heavyVals Yset listY θ M z : Set ℤ) := by
      ext l; simp
    rw [hL₁, this]
    exact hL₀'m.inter (MeasurableSet.iUnion (fun z => (hZm (measurableSet_singleton z)).inter
      (hJm (DiscreteMeasurableSpace.forall_measurableSet _))))
  refine ⟨L₁, fun l hl => hl.1.1, hL₁m, ?_, ?_⟩
  · -- mass
    have hν1 : ν L₀' ≤ 1 := prob_le_one
    have hlight : ν (L₀' ∩ {l | J l ∉ heavyVals Yset listY θ M (Z l)}) ≤ ENNReal.ofReal s₀ := by
      refine htc.trans ?_
      calc ENNReal.ofReal (θ * c₀) * (K₀ * ν L₀') ≤ ENNReal.ofReal (θ * c₀) * (K₀ * 1) := by
            gcongr
        _ = ENNReal.ofReal (θ * c₀ * K₀) := by
            rw [mul_one, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        _ = ENNReal.ofReal s₀ := by
            congr 1; rw [hθ]; field_simp
    have hcov : L₀ ⊆ (L₀ \ L₀') ∪ (L₀' ∩ {l | J l ∉ heavyVals Yset listY θ M (Z l)}) ∪ L₁ := by
      intro l hl
      by_cases h1' : l ∈ L₀'
      · by_cases h2' : J l ∈ heavyVals Yset listY θ M (Z l)
        · right; exact ⟨h1', h2'⟩
        · left; right; exact ⟨h1', h2'⟩
      · left; left; exact ⟨hl, h1'⟩
    have hsum := (measure_mono (μ := ν) hcov).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl))
    have hloss' : ν (L₀ \ L₀') ≤ ENNReal.ofReal s₀ := by
      refine hloss.trans ?_
      rw [measure_univ, mul_one]
    have : ENNReal.ofReal mL ≤ ENNReal.ofReal s₀ + ENNReal.ofReal s₀ + ν L₁ :=
      hmass.trans (hsum.trans (add_le_add (add_le_add hloss' hlight) le_rfl))
    rw [← ENNReal.ofReal_add hs₀p.le hs₀p.le] at this
    have e : mL = (s₀ + s₀) + mL / 2 := by rw [hs₀]; ring
    rw [e, ENNReal.ofReal_add (by positivity) (by positivity)] at this
    exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp this
  · -- the pairs
    refine ⟨Zs.biUnion (fun z => (heavyVals Yset listY θ M z).image (fun j => (z, j))), ?_, ?_⟩
    · refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
      push_cast
      have hcardY : ∀ g, ((listY g).card : ℝ) ≤ KY := by
        intro g
        have : (listY g).card ≤ 2 := Finset.card_le_two
        have h2 : (2 : ℝ) ≤ KY := by
          rw [hKY]
          have : (0 : ℝ) ≤ ⌈K⌉₊ := Nat.cast_nonneg _
          nlinarith
        exact (by exact_mod_cast this : ((listY g).card : ℝ) ≤ 2).trans h2
      have hKY0 : 0 ≤ KY := by rw [hKY]; positivity
      calc ∑ z ∈ Zs, (((heavyVals Yset listY θ M z).image (fun j => (z, j))).card : ℝ)
          ≤ ∑ _z ∈ Zs, KY * KY / θ := by
            apply Finset.sum_le_sum
            intro z _
            exact (Nat.cast_le.mpr Finset.card_image_le).trans
              (card_heavyVals_le hθp hM hKY0 hcardY z (hYset z))
        _ = Zs.card * (KY * KY / θ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * R + 2) * (K * (1 / w) ^ d) * (KY * KY / θ) :=
            mul_le_mul_of_nonneg_right hZs (by positivity)
        _ = pairBound K KA d w mL := by
            rw [pairBound, hθ, hc₀, hanum, hs₀, hKY, hRdef, hK₀]
            push_cast
            field_simp
    · intro l hl
      refine Finset.mem_biUnion.mpr ⟨Z l, hZsL l hl.1.1, Finset.mem_image.mpr ⟨J l, hl.2, rfl⟩⟩

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
