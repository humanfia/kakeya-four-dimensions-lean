import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Prep

/-!
# Tilted slabs and their cell covers

At a time `t`, the trajectories whose tangential coordinates `y` lie in a square of side `σ`
and whose scalar `x̄(t) - f · y` lies in an interval of length `ω` occupy at most
`(σ/q + 2)² (ω/q + 4K + 2)` grid cells of side `q` of `(x̄(t), y)`, where `|f i| ≤ K`
(`slab_cells`). Summing the absolute cap (`slab_absCap`) or the bin cap (`slab_binCap`) over
these cells bounds the labeled mass of the slab.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

/-- The integer interval of the floors of `[a, a + L]` at width `q`. -/
def floorRange (q a L : ℝ) : Finset ℤ := Finset.Icc ⌊a / q⌋ ⌊(a + L) / q⌋

theorem floor_mem_floorRange {q a L x : ℝ} (hq : 0 < q) (hx : a ≤ x) (hx' : x ≤ a + L) :
    ⌊x / q⌋ ∈ floorRange q a L :=
  Finset.mem_Icc.mpr ⟨Int.floor_le_floor (div_le_div_of_nonneg_right hx hq.le),
    Int.floor_le_floor (div_le_div_of_nonneg_right hx' hq.le)⟩

theorem card_floorRange_le {q a L : ℝ} (hq : 0 < q) (hL : 0 ≤ L) :
    ((floorRange q a L).card : ℝ) ≤ L / q + 2 := by
  unfold floorRange
  rw [Int.card_Icc]
  have h1 : (⌊(a + L) / q⌋ : ℝ) ≤ (a + L) / q := Int.floor_le _
  have h2 : a / q - 1 < (⌊a / q⌋ : ℝ) := by have := Int.sub_one_lt_floor (a / q); linarith
  have h3 : ((⌊(a + L) / q⌋ + 1 - ⌊a / q⌋ : ℤ) : ℝ) ≤ L / q + 2 := by
    push_cast
    have : (a + L) / q = a / q + L / q := by rw [add_div]
    linarith
  rcases le_or_gt 0 (⌊(a + L) / q⌋ + 1 - ⌊a / q⌋) with h | h
  · have e : (((⌊(a + L) / q⌋ + 1 - ⌊a / q⌋).toNat : ℕ) : ℝ) =
        ((⌊(a + L) / q⌋ + 1 - ⌊a / q⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h
    rw [e]; exact h3
  · rw [Int.toNat_of_nonpos h.le]; simp only [CharP.cast_eq_zero]; positivity

/-- The `q`-cell of `(x̄, y)`. -/
def cellOf3 (q xb y0 y1 : ℝ) : Fin 3 → ℤ := ![⌊xb / q⌋, ⌊y0 / q⌋, ⌊y1 / q⌋]

/-- The cells of a tilted slab. -/
def slabCells (q σ ω K : ℝ) (y00 y10 s₀ : ℝ) (f : Fin 2 → ℝ) : Finset (Fin 3 → ℤ) :=
  ((floorRange q y00 σ) ×ˢ (floorRange q y10 σ)).biUnion (fun z =>
    (floorRange q (s₀ + f 0 * (z.1 * q) + f 1 * (z.2 * q) - 2 * K * q) (ω + 4 * K * q)).image
      (fun z0 => ![z0, z.1, z.2]))

theorem slab_cells {q σ ω K y00 y10 s₀ : ℝ} {f : Fin 2 → ℝ} (hq : 0 < q) (hK : 0 ≤ K)
    (hf : ∀ i, |f i| ≤ K) {xb y0 y1 : ℝ} (hy0 : y00 ≤ y0) (hy0' : y0 ≤ y00 + σ)
    (hy1 : y10 ≤ y1) (hy1' : y1 ≤ y10 + σ) (hs : s₀ ≤ xb - (f 0 * y0 + f 1 * y1))
    (hs' : xb - (f 0 * y0 + f 1 * y1) ≤ s₀ + ω) :
    cellOf3 q xb y0 y1 ∈ slabCells q σ ω K y00 y10 s₀ f := by
  unfold slabCells cellOf3
  refine Finset.mem_biUnion.mpr ⟨(⌊y0 / q⌋, ⌊y1 / q⌋),
    Finset.mem_product.mpr ⟨floor_mem_floorRange hq hy0 hy0', floor_mem_floorRange hq hy1 hy1'⟩,
    Finset.mem_image.mpr ⟨⌊xb / q⌋, ?_, rfl⟩⟩
  -- the position of `y` inside its cell
  have hc0 : |y0 - (⌊y0 / q⌋ : ℝ) * q| ≤ q := by
    have h1 := Int.floor_le (y0 / q)
    have h2 := Int.lt_floor_add_one (y0 / q)
    rw [abs_le]
    constructor
    · have : (⌊y0 / q⌋ : ℝ) * q ≤ y0 := by rwa [le_div_iff₀ hq] at h1
      linarith
    · have : y0 < ((⌊y0 / q⌋ : ℝ) + 1) * q := by rwa [div_lt_iff₀ hq] at h2
      linarith
  have hc1 : |y1 - (⌊y1 / q⌋ : ℝ) * q| ≤ q := by
    have h1 := Int.floor_le (y1 / q)
    have h2 := Int.lt_floor_add_one (y1 / q)
    rw [abs_le]
    constructor
    · have : (⌊y1 / q⌋ : ℝ) * q ≤ y1 := by rwa [le_div_iff₀ hq] at h1
      linarith
    · have : y1 < ((⌊y1 / q⌋ : ℝ) + 1) * q := by rwa [div_lt_iff₀ hq] at h2
      linarith
  have hd0 : |f 0 * y0 - f 0 * ((⌊y0 / q⌋ : ℝ) * q)| ≤ K * q := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (hf 0) hc0 (abs_nonneg _) hK
  have hd1 : |f 1 * y1 - f 1 * ((⌊y1 / q⌋ : ℝ) * q)| ≤ K * q := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul (hf 1) hc1 (abs_nonneg _) hK
  apply floor_mem_floorRange hq
  · dsimp only
    have := (abs_le.mp hd0).1; have := (abs_le.mp hd1).1
    linarith
  · dsimp only
    have := (abs_le.mp hd0).2; have := (abs_le.mp hd1).2
    linarith

theorem card_slabCells_le {q σ ω K y00 y10 s₀ : ℝ} {f : Fin 2 → ℝ} (hq : 0 < q) (hσ : 0 ≤ σ)
    (hω : 0 ≤ ω) (hK : 0 ≤ K) :
    ((slabCells q σ ω K y00 y10 s₀ f).card : ℝ) ≤ (σ / q + 2) ^ 2 * (ω / q + 4 * K + 2) := by
  unfold slabCells
  refine (Nat.cast_le.mpr Finset.card_biUnion_le).trans ?_
  push_cast
  calc ∑ z ∈ floorRange q y00 σ ×ˢ floorRange q y10 σ,
        (((floorRange q (s₀ + f 0 * (z.1 * q) + f 1 * (z.2 * q) - 2 * K * q)
          (ω + 4 * K * q)).image (fun z0 => ![z0, z.1, z.2])).card : ℝ)
      ≤ ∑ _z ∈ floorRange q y00 σ ×ˢ floorRange q y10 σ, (ω / q + 4 * K + 2) := by
        apply Finset.sum_le_sum
        intro z _
        refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
        refine (card_floorRange_le hq (by positivity)).trans (le_of_eq ?_)
        field_simp
    _ = ((floorRange q y00 σ).card * (floorRange q y10 σ).card : ℝ) * (ω / q + 4 * K + 2) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; ring
    _ ≤ (σ / q + 2) ^ 2 * (ω / q + 4 * K + 2) := by
        have h1 := card_floorRange_le (a := y00) hq hσ
        have h2 := card_floorRange_le (a := y10) hq hσ
        have h3 : 0 ≤ ω / q + 4 * K + 2 := by positivity
        have h4 : ((floorRange q y00 σ).card * (floorRange q y10 σ).card : ℝ) ≤
            (σ / q + 2) ^ 2 := by
          rw [sq]; exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_right h4 h3

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The labeled mass of a tilted slab at time `t` from the absolute cap. -/
theorem slab_absCap {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : Data ν y β γ E F d K ζ) (hK : 0 ≤ K)
    {t q σ ω y00 y10 s₀ : ℝ} (hq : ζ ≤ q) (hq1 : q ≤ 1) (hq0 : 0 < q) (hσ : 0 ≤ σ)
    (hω : 0 ≤ ω) (S : Set Ω)
    (hS : ∀ l ∈ S, (l, t) ∈ E ∧ y00 ≤ y l 0 ∧ y l 0 ≤ y00 + σ ∧ y10 ≤ y l 1 ∧ y l 1 ≤ y10 + σ ∧
      s₀ ≤ scal y β γ F l t ∧ scal y β γ F l t ≤ s₀ + ω) :
    ν S ≤ ENNReal.ofReal ((σ / q + 2) ^ 2 * (ω / q + 4 * K + 2) * (K * q ^ (2 + d))) := by
  classical
  set cells := slabCells q σ ω K y00 y10 s₀ (F t)
  have hsub : S ⊆ ⋃ z ∈ cells, {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧
      ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} := by
    intro l hl
    obtain ⟨hlE, h0, h0', h1, h1', hs, hs'⟩ := hS l hl
    refine mem_iUnion₂.mpr ⟨cellOf3 q (xbar β γ l t) (y l 0) (y l 1), ?_, hlE, rfl, rfl, rfl⟩
    exact slab_cells hq0 hK (fun i => h.bound_F t i) h0 h0' h1 h1' hs hs'
  calc ν S ≤ ∑ z ∈ cells, ν {l | (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧
        ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _z ∈ cells, ENNReal.ofReal (K * q ^ (2 + d)) :=
        Finset.sum_le_sum (fun z _ => h.absCap t q hq hq1 z)
    _ = ENNReal.ofReal (cells.card * (K * q ^ (2 + d))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (card_slabCells_le hq0 hσ hω hK)
          (mul_nonneg hK (Real.rpow_nonneg hq0.le _))

/-- The labeled mass of a tilted slab inside a dyadic coefficient bin, from the bin cap. -/
theorem slab_binCap {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : Data ν y β γ E F d K ζ) (hK : 0 ≤ K)
    {t q σ ω y00 y10 s₀ : ℝ} {n : ℕ} (hq : ζ ≤ q) (hqn : q ≤ (2 : ℝ) ^ (-(n : ℤ))) (hq0 : 0 < q)
    (hσ : 0 ≤ σ) (hω : 0 ≤ ω) (b : Fin 4 → ℤ) (S : Set Ω)
    (hS : ∀ l ∈ S, (⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
        ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3) ∧
      (l, t) ∈ E ∧ y00 ≤ y l 0 ∧ y l 0 ≤ y00 + σ ∧ y10 ≤ y l 1 ∧ y l 1 ≤ y10 + σ ∧
      s₀ ≤ scal y β γ F l t ∧ scal y β γ F l t ≤ s₀ + ω) :
    ν S ≤ ENNReal.ofReal ((σ / q + 2) ^ 2 * (ω / q + 4 * K + 2) *
        (K * (q / (2 : ℝ) ^ (-(n : ℤ))) ^ (2 + d))) *
      ν {l | ⌊y l 0 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 0 ∧ ⌊y l 1 / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 1 ∧
          ⌊β l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 2 ∧ ⌊γ l / (2 : ℝ) ^ (-(n : ℤ))⌋ = b 3} := by
  classical
  set r : ℝ := (2 : ℝ) ^ (-(n : ℤ))
  set cells := slabCells q σ ω K y00 y10 s₀ (F t)
  set Bset := {l | ⌊y l 0 / r⌋ = b 0 ∧ ⌊y l 1 / r⌋ = b 1 ∧ ⌊β l / r⌋ = b 2 ∧ ⌊γ l / r⌋ = b 3}
  have hsub : S ⊆ ⋃ z ∈ cells, {l | (⌊y l 0 / r⌋ = b 0 ∧ ⌊y l 1 / r⌋ = b 1 ∧
      ⌊β l / r⌋ = b 2 ∧ ⌊γ l / r⌋ = b 3) ∧ (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧
      ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} := by
    intro l hl
    obtain ⟨hb, hlE, h0, h0', h1, h1', hs, hs'⟩ := hS l hl
    refine mem_iUnion₂.mpr ⟨cellOf3 q (xbar β γ l t) (y l 0) (y l 1), ?_, hb, hlE, rfl, rfl, rfl⟩
    exact slab_cells hq0 hK (fun i => h.bound_F t i) h0 h0' h1 h1' hs hs'
  calc ν S ≤ ∑ z ∈ cells, ν {l | (⌊y l 0 / r⌋ = b 0 ∧ ⌊y l 1 / r⌋ = b 1 ∧
        ⌊β l / r⌋ = b 2 ∧ ⌊γ l / r⌋ = b 3) ∧ (l, t) ∈ E ∧ ⌊xbar β γ l t / q⌋ = z 0 ∧
        ⌊y l 0 / q⌋ = z 1 ∧ ⌊y l 1 / q⌋ = z 2} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _z ∈ cells, ENNReal.ofReal (K * (q / r) ^ (2 + d)) * ν Bset :=
        Finset.sum_le_sum (fun z _ => h.binCap q n hq hqn b t z)
    _ = ENNReal.ofReal (cells.card * (K * (q / r) ^ (2 + d))) * ν Bset := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ bot_le
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (card_slabCells_le hq0 hσ hω hK)
          (mul_nonneg hK (Real.rpow_nonneg (div_nonneg hq0.le (zpow_nonneg (by norm_num) _)) _))

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
