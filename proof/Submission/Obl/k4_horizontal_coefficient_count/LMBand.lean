import Submission.Obl.k4_horizontal_coefficient_count.LMSetup

/-!
# Band caps for one parameter group

A group `g = (d₀, p, q')` fixes the velocity bin of width `χ` and the
parameter bins of width `a`.  Its trajectories stay within `K a` of the moving
reference point `(p a + t v, q' a - t p a)` (`v = d₀ χ`), by the horizontal
equation `|b₄ + b₀| ≤ χ`.  Summing the joint cap over the cells of one time
bin bounds the incidence mass of any band of scalar values by
`K^4 a^2 r^d π(d₀)` up to constants: this is the Frostman bound of the scalar
coefficients in the group.
-/

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Floors of close numbers are close. -/
theorem floor_sub_floor_abs_le {x y c : ℝ} (h : |x - y| ≤ c) :
    |⌊x⌋ - ⌊y⌋| ≤ ⌈c⌉ := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le y
  have h4 := Int.lt_floor_add_one y
  have hc := Int.le_ceil c
  rw [abs_le] at h ⊢
  constructor
  · have : ((-⌈c⌉ - 1 : ℤ) : ℝ) < ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by push_cast; linarith
    have : (-⌈c⌉ - 1 : ℤ) < ⌊x⌋ - ⌊y⌋ := by exact_mod_cast this
    omega
  · have : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) < ((⌈c⌉ + 1 : ℤ) : ℝ) := by push_cast; linarith
    have : (⌊x⌋ - ⌊y⌋ : ℤ) < ⌈c⌉ + 1 := by exact_mod_cast this
    omega

/-- Membership of a floor in the symmetric offset window. -/
theorem floor_div_mem_window {x y c w : ℝ} (hw : 0 < w) (h : |x - y| ≤ c * w) :
    ⌊x / w⌋ - ⌊y / w⌋ ∈ Finset.Icc (-⌈c⌉) ⌈c⌉ := by
  have h' : |x / w - y / w| ≤ c := by
    rw [← sub_div, abs_div, abs_of_pos hw, div_le_iff₀ hw]
    exact h
  have := floor_sub_floor_abs_le h'
  rw [Finset.mem_Icc]
  rw [abs_le] at this
  exact this

theorem card_window (c : ℝ) (hc : 0 ≤ c) :
    ((Finset.Icc (-⌈c⌉) ⌈c⌉).card : ℝ) ≤ 2 * c + 3 := by
  have h0 : 0 ≤ ⌈c⌉ := Int.ceil_nonneg hc
  have hce : (⌈c⌉ : ℝ) < c + 1 := Int.ceil_lt_add_one c
  rw [Int.card_Icc]
  have : (⌈c⌉ + 1 - -⌈c⌉).toNat = 2 * ⌈c⌉.toNat + 1 := by omega
  rw [this]
  push_cast
  have : ((⌈c⌉.toNat : ℕ) : ℝ) = (⌈c⌉ : ℝ) := by
    have := Int.toNat_of_nonneg h0
    exact_mod_cast this
  rw [this]
  linarith

/-- Bounds on the coordinates of a binned coefficient. -/
theorem floor_eq_bounds {x w : ℝ} {m : ℤ} (hw : 0 < w) (h : ⌊x / w⌋ = m) :
    (m : ℝ) * w ≤ x ∧ x < (m : ℝ) * w + w := by
  rw [Int.floor_eq_iff] at h
  constructor
  · have := h.1
    rwa [le_div_iff₀ hw] at this
  · have := h.2
    rw [div_lt_iff₀ hw] at this
    linarith

variable {α : Type} [MeasurableSpace α]

/-- Reference horizontal position of group `g` at the start of time bin `n₀`. -/
def refZ (χ a : ℝ) (g : ℤ × ℤ × ℤ) (n0 : ℤ) : ℝ :=
  (g.2.1 : ℝ) * a + ((n0 : ℝ) * a) * ((g.1 : ℝ) * χ)

/-- Reference transverse position of group `g` at the start of time bin `n₀`. -/
def refY (a : ℝ) (g : ℤ × ℤ × ℤ) (n0 : ℤ) : ℝ :=
  (g.2.2 : ℝ) * a - ((n0 : ℝ) * a) * ((g.2.1 : ℝ) * a)

omit [MeasurableSpace α] in
/-- Positions of a good label of group `g` stay near the reference point. -/
theorem group_position_near {b : α → Fin 6 → ℝ} {K χ a : ℝ} (hχ : 0 < χ) (ha : 0 < a)
    (hχa : χ ≤ a) {g : ℤ × ℤ × ℤ} {l : α} (hl : l ∈ groupSet b χ a g ∩ goodSet b K χ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |X1 (b l) t - refZ χ a g ⌊t / a⌋| ≤ (K + 2) * a ∧
      |X2 (b l) t - refY a g ⌊t / a⌋| ≤ (K + 3) * a := by
  obtain ⟨⟨hg3, hg0, hg1⟩, hgood⟩ := hl
  obtain ⟨hsum, hhor, _, _⟩ := hgood
  have hb3 := floor_eq_bounds hχ hg3
  have hb0 := floor_eq_bounds ha hg0
  have hb1 := floor_eq_bounds ha hg1
  have htt := floor_eq_bounds ha (rfl : ⌊t / a⌋ = ⌊t / a⌋)
  set n0 : ℤ := ⌊t / a⌋
  have hn0a : (n0 : ℝ) * a ≤ 1 := htt.1.trans ht.2
  have hn0a0 : 0 ≤ (n0 : ℝ) * a := by
    have : (0 : ℤ) ≤ n0 := Int.floor_nonneg.mpr (div_nonneg ht.1 ha.le)
    have : (0 : ℝ) ≤ n0 := by exact_mod_cast this
    positivity
  have hK3 : |b l 3| ≤ K := by
    linarith [abs_nonneg (b l 0), abs_nonneg (b l 1), abs_nonneg (b l 4)]
  have hK0 : |b l 0| ≤ K := by
    linarith [abs_nonneg (b l 3), abs_nonneg (b l 1), abs_nonneg (b l 4)]
  constructor
  · -- X1 - Z = (b0 - p a) + (t - n0 a) b3 + n0 a (b3 - v)
    have hid : X1 (b l) t - refZ χ a g n0 =
        (b l 0 - (g.2.1 : ℝ) * a) + (t - (n0 : ℝ) * a) * b l 3 +
          ((n0 : ℝ) * a) * (b l 3 - (g.1 : ℝ) * χ) := by
      simp only [X1, refZ]; ring
    rw [hid]
    have e1 : |b l 0 - (g.2.1 : ℝ) * a| ≤ a := by
      rw [abs_le]; constructor <;> linarith
    have e2 : |(t - (n0 : ℝ) * a) * b l 3| ≤ a * K := by
      rw [abs_mul]
      have : |t - (n0 : ℝ) * a| ≤ a := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul this hK3 (abs_nonneg _) ha.le
    have e3 : |((n0 : ℝ) * a) * (b l 3 - (g.1 : ℝ) * χ)| ≤ 1 * a := by
      rw [abs_mul, abs_of_nonneg hn0a0]
      have : |b l 3 - (g.1 : ℝ) * χ| ≤ a := by
        rw [abs_le]; constructor <;> linarith
      exact mul_le_mul hn0a this (abs_nonneg _) zero_le_one
    calc _ ≤ |b l 0 - (g.2.1 : ℝ) * a| + |(t - (n0 : ℝ) * a) * b l 3| +
          |((n0 : ℝ) * a) * (b l 3 - (g.1 : ℝ) * χ)| := abs_add_three _ _ _
      _ ≤ a + a * K + 1 * a := by linarith
      _ = (K + 2) * a := by ring
  · have hid : X2 (b l) t - refY a g n0 =
        (b l 1 - (g.2.2 : ℝ) * a) + t * (b l 4 + b l 0) - (t - (n0 : ℝ) * a) * b l 0 -
          ((n0 : ℝ) * a) * (b l 0 - (g.2.1 : ℝ) * a) := by
      simp only [X2, refY]; ring
    rw [hid]
    have e1 : |b l 1 - (g.2.2 : ℝ) * a| ≤ a := by
      rw [abs_le]; constructor <;> linarith
    have e2 : |t * (b l 4 + b l 0)| ≤ 1 * a := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact mul_le_mul ht.2 (hhor.trans hχa) (abs_nonneg _) zero_le_one
    have e3 : |(t - (n0 : ℝ) * a) * b l 0| ≤ a * K := by
      rw [abs_mul]
      have : |t - (n0 : ℝ) * a| ≤ a := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul this hK0 (abs_nonneg _) ha.le
    have e4 : |((n0 : ℝ) * a) * (b l 0 - (g.2.1 : ℝ) * a)| ≤ 1 * a := by
      rw [abs_mul, abs_of_nonneg hn0a0]
      have : |b l 0 - (g.2.1 : ℝ) * a| ≤ a := by
        rw [abs_le]; constructor <;> linarith
      exact mul_le_mul hn0a this (abs_nonneg _) zero_le_one
    have := abs_sub (b l 1 - (g.2.2 : ℝ) * a + t * (b l 4 + b l 0) -
      (t - (n0 : ℝ) * a) * b l 0) (((n0 : ℝ) * a) * (b l 0 - (g.2.1 : ℝ) * a))
    have := abs_sub (b l 1 - (g.2.2 : ℝ) * a + t * (b l 4 + b l 0))
      ((t - (n0 : ℝ) * a) * b l 0)
    have := abs_add_le (b l 1 - (g.2.2 : ℝ) * a) (t * (b l 4 + b l 0))
    nlinarith

/-- The band cap: incidences of a group whose scalar values stay in a band of
half-width `ρ₃` around a function of the time bin. -/
theorem band_cap (H : DepthData α) (hH : H.Hyp) (g : ℤ × ℤ × ℤ) (S : Set α)
    (hS : S ⊆ groupSet H.b H.χ H.a g ∩ goodSet H.b H.K H.χ)
    (y0 : ℤ → ℝ) (ρ3 r : ℝ) (hr : H.a ≤ r) (hr1 : r ≤ 1) (hρ3 : 0 ≤ ρ3)
    (hy : ∀ l ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, |X3 (H.b l) t - y0 ⌊t / H.a⌋| ≤ ρ3) :
    H.μ (S ×ˢ univ) ≤
      ENNReal.ofReal ((1 / H.a + 1) * (2 * H.K + 7) * (2 * H.K + 9) * (2 * (ρ3 / r) + 3) *
        (H.K * H.a ^ 3 * r ^ H.d)) * H.π {x | ⌊x / H.χ⌋ = g.1} := by
  classical
  have ha := hH.ha0
  have hχ := hH.hχ0
  have hK := hH.hK
  have hr0 : 0 < r := ha.trans_le hr
  -- the cells
  set M1 : ℤ := ⌈H.K + 2⌉
  set M2 : ℤ := ⌈H.K + 3⌉
  set M3 : ℤ := ⌈ρ3 / r⌉
  set cells : Finset (ℤ × ℤ × ℤ × ℤ) :=
    ((Finset.Icc (0 : ℤ) ⌊1 / H.a⌋) ×ˢ (Finset.Icc (-M1) M1) ×ˢ (Finset.Icc (-M2) M2) ×ˢ
      (Finset.Icc (-M3) M3)).image
      (fun x => (x.1, ⌊refZ H.χ H.a g x.1 / H.a⌋ + x.2.1, ⌊refY H.a g x.1 / H.a⌋ + x.2.2.1,
        ⌊y0 x.1 / r⌋ + x.2.2.2)) with hcells
  set cell : ℤ × ℤ × ℤ × ℤ → Set (α × ℝ) := fun c =>
    {p | ⌊p.2 / H.a⌋ = c.1 ∧ ⌊X1 (H.b p.1) p.2 / H.a⌋ = c.2.1 ∧
      ⌊X2 (H.b p.1) p.2 / H.a⌋ = c.2.2.1 ∧ ⌊X3 (H.b p.1) p.2 / r⌋ = c.2.2.2 ∧
      ⌊H.b p.1 3 / H.χ⌋ = g.1} with hcell
  -- covering
  have hcover : S ×ˢ univ ⊆ (⋃ c ∈ cells, cell c) ∪ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ := by
    rintro ⟨l, t⟩ ⟨hl, -⟩
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · left
      have hlS := hS hl
      obtain ⟨hZ, hY⟩ := group_position_near hχ ha hH.hχa hlS ht
      have h3 := hy l hl t ht
      simp only [mem_iUnion]
      refine ⟨(⌊t / H.a⌋, ⌊X1 (H.b l) t / H.a⌋, ⌊X2 (H.b l) t / H.a⌋,
        ⌊X3 (H.b l) t / r⌋), ?_, ?_⟩
      · rw [hcells, Finset.mem_image]
        refine ⟨(⌊t / H.a⌋, ⌊X1 (H.b l) t / H.a⌋ - ⌊refZ H.χ H.a g ⌊t / H.a⌋ / H.a⌋,
          ⌊X2 (H.b l) t / H.a⌋ - ⌊refY H.a g ⌊t / H.a⌋ / H.a⌋,
          ⌊X3 (H.b l) t / r⌋ - ⌊y0 ⌊t / H.a⌋ / r⌋), ?_, ?_⟩
        · simp only [Finset.mem_product]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [Finset.mem_Icc]
            exact ⟨Int.floor_nonneg.mpr (div_nonneg ht.1 ha.le),
              Int.floor_mono (div_le_div_of_nonneg_right ht.2 ha.le)⟩
          · exact floor_div_mem_window ha hZ
          · exact floor_div_mem_window ha hY
          · apply floor_div_mem_window hr0
            rw [div_mul_cancel₀ _ hr0.ne']
            exact h3
        · simp
      · exact ⟨rfl, rfl, rfl, rfl, (hlS.1).1⟩
    · right
      simp [ht]
  have hcard : (cells.card : ℝ) ≤
      (1 / H.a + 1) * (2 * H.K + 7) * (2 * H.K + 9) * (2 * (ρ3 / r) + 3) := by
    have h1 := Finset.card_image_le (s := (Finset.Icc (0 : ℤ) ⌊1 / H.a⌋) ×ˢ
      (Finset.Icc (-M1) M1) ×ˢ (Finset.Icc (-M2) M2) ×ˢ (Finset.Icc (-M3) M3))
      (f := fun x => (x.1, ⌊refZ H.χ H.a g x.1 / H.a⌋ + x.2.1,
        ⌊refY H.a g x.1 / H.a⌋ + x.2.2.1, ⌊y0 x.1 / r⌋ + x.2.2.2))
    rw [← hcells] at h1
    have h1' : (cells.card : ℝ) ≤ (((Finset.Icc (0 : ℤ) ⌊1 / H.a⌋) ×ˢ
        (Finset.Icc (-M1) M1) ×ˢ (Finset.Icc (-M2) M2) ×ˢ
        (Finset.Icc (-M3) M3)).card : ℝ) := by exact_mod_cast h1
    refine h1'.trans ?_
    simp only [Finset.card_product]
    push_cast
    have c0 : ((Finset.Icc (0 : ℤ) ⌊1 / H.a⌋).card : ℝ) ≤ 1 / H.a + 1 := by
      rw [Int.card_Icc]
      have hf0 : 0 ≤ ⌊1 / H.a⌋ := Int.floor_nonneg.mpr (by positivity)
      have : (⌊1 / H.a⌋ + 1 - 0).toNat = ⌊1 / H.a⌋.toNat + 1 := by omega
      rw [this]
      push_cast
      have : ((⌊1 / H.a⌋.toNat : ℕ) : ℝ) = (⌊1 / H.a⌋ : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hf0
      rw [this]
      linarith [Int.floor_le (1 / H.a)]
    have c1 : ((Finset.Icc (-M1) M1).card : ℝ) ≤ 2 * H.K + 7 := by
      have := card_window (H.K + 2) (by linarith)
      linarith
    have c2 : ((Finset.Icc (-M2) M2).card : ℝ) ≤ 2 * H.K + 9 := by
      have := card_window (H.K + 3) (by linarith)
      linarith
    have c3 : ((Finset.Icc (-M3) M3).card : ℝ) ≤ 2 * (ρ3 / r) + 3 :=
      card_window (ρ3 / r) (div_nonneg hρ3 hr0.le)
    have p0 : (0 : ℝ) ≤ ((Finset.Icc (0 : ℤ) ⌊1 / H.a⌋).card : ℝ) := by positivity
    have p1 : (0 : ℝ) ≤ ((Finset.Icc (-M1) M1).card : ℝ) := by positivity
    have p2 : (0 : ℝ) ≤ ((Finset.Icc (-M2) M2).card : ℝ) := by positivity
    have p3 : (0 : ℝ) ≤ ((Finset.Icc (-M3) M3).card : ℝ) := by positivity
    calc _ = ((Finset.Icc (0 : ℤ) ⌊1 / H.a⌋).card : ℝ) * ((Finset.Icc (-M1) M1).card : ℝ) *
          ((Finset.Icc (-M2) M2).card : ℝ) * ((Finset.Icc (-M3) M3).card : ℝ) := by ring
      _ ≤ _ := by gcongr
  -- the measure estimate
  have hsupp : H.μ ((univ ×ˢ Icc (0 : ℝ) 1)ᶜ) = 0 := hH.hμsupp
  calc H.μ (S ×ˢ univ)
      ≤ H.μ ((⋃ c ∈ cells, cell c) ∪ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ) := measure_mono hcover
    _ ≤ H.μ (⋃ c ∈ cells, cell c) + H.μ ((univ ×ˢ Icc (0 : ℝ) 1)ᶜ) := measure_union_le _ _
    _ = H.μ (⋃ c ∈ cells, cell c) := by rw [hsupp, add_zero]
    _ ≤ ∑ c ∈ cells, H.μ (cell c) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _c ∈ cells, ENNReal.ofReal (H.K * H.a ^ 3 * r ^ H.d) *
          H.π {x | ⌊x / H.χ⌋ = g.1} := by
        apply Finset.sum_le_sum
        intro c _
        exact hH.capB r hr hr1 c.1 c.2.1 c.2.2.1 c.2.2.2 g.1
    _ = (cells.card : ℝ≥0∞) * (ENNReal.ofReal (H.K * H.a ^ 3 * r ^ H.d) *
          H.π {x | ⌊x / H.χ⌋ = g.1}) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((1 / H.a + 1) * (2 * H.K + 7) * (2 * H.K + 9) * (2 * (ρ3 / r) + 3)) *
          (ENNReal.ofReal (H.K * H.a ^ 3 * r ^ H.d) * H.π {x | ⌊x / H.χ⌋ = g.1}) := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcard
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul]
        have : 0 ≤ 1 / H.a + 1 := by positivity
        have : 0 ≤ 2 * (ρ3 / r) + 3 := by positivity
        positivity

end

end Submission.Obl.k4_horizontal_coefficient_count
