import Mathlib

/-!
# The nested position cells of the synthetic model

Levels `k₀ + d`, `d ≤ D`, have dyadic meshes `q d = 2^(-T d)`, with `T (d+1) ≥ T d + B` and
`β = 2^(-B)`. The cells of level `d` are `[β + c q d, β + (c+1) q d)`. A cell of level `d+1` is a
valid child when it lies in the middle part `[β, 1-β)` (in relative units) of its parent cell;
root cells lie in `[β, 1-β)`. Lines move by at most `β q d` between a block of level `d` and
its sub-blocks, so a point of a valid child, moved back, lies in the parent cell (`plateau`),
and a point at relative distance more than `β + 1/r` from both ends of a valid cell, moved
forward, lies in a valid child (`step`). Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

noncomputable section

/-- The level structure of the synthetic model. -/
structure Grid where
  B : ℕ
  D : ℕ
  T : ℕ → ℕ
  hB : 2 ≤ B
  hT0 : B + 1 ≤ T 0
  hT : ∀ d, T d + B ≤ T (d + 1)

namespace Grid

variable (g : Grid)

/-- The slope range and margin `β = 2^(-B)`. -/
def β : ℝ := 1 / 2 ^ g.B

/-- The mesh of level `d`. -/
def q (d : ℕ) : ℝ := 1 / 2 ^ g.T d

/-- The refinement ratio from level `d` to level `d+1`. -/
def r (d : ℕ) : ℕ := 2 ^ (g.T (d + 1) - g.T d)

/-- The lowest admissible child digit, `r β`. -/
def lo (d : ℕ) : ℕ := 2 ^ (g.T (d + 1) - g.T d - g.B)

/-- The number of root cells. -/
def N₀ : ℕ := 2 ^ g.T 0 - 2 * 2 ^ (g.T 0 - g.B)

/-- Valid cells. -/
def valid : ℕ → ℕ → Prop
  | 0, c => c < g.N₀
  | d + 1, c => g.lo d ≤ c % g.r d ∧ c % g.r d < g.r d - g.lo d ∧ valid d (c / g.r d)

scoped instance (d c : ℕ) : Decidable (g.valid d c) := by
  induction d generalizing c with
  | zero => exact inferInstanceAs (Decidable (c < g.N₀))
  | succ d ih => exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The left end of a cell. -/
def cpos (d c : ℕ) : ℝ := g.β + c * g.q d

/-- The cell of a position. -/
def cellOf (d : ℕ) (x : ℝ) : ℕ := ⌊(x - g.β) / g.q d⌋₊

theorem β_pos : 0 < g.β := by unfold β; positivity
theorem q_pos (d : ℕ) : 0 < g.q d := by unfold q; positivity
theorem r_pos (d : ℕ) : 0 < g.r d := by unfold r; positivity

theorem β_le_half : g.β ≤ 1 / 2 := by
  unfold β
  have : (2 : ℝ) ≤ 2 ^ g.B := by
    have h1 : 1 ≤ g.B := by have := g.hB; omega
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g.B := pow_le_pow_right₀ (by norm_num) h1
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem q_succ (d : ℕ) : g.q d = g.r d * g.q (d + 1) := by
  have h := g.hT d
  have e : (2 : ℝ) ^ g.T (d + 1) = 2 ^ (g.T (d + 1) - g.T d) * 2 ^ g.T d := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  unfold q r
  push_cast
  rw [e]
  field_simp

theorem lo_eq (d : ℕ) : (g.lo d : ℝ) = g.r d * g.β := by
  unfold lo r β
  have h := g.hT d
  push_cast
  rw [mul_one_div, eq_div_iff (by positivity), ← pow_add]
  congr 1
  omega

theorem lo_lt_r (d : ℕ) : 2 * g.lo d ≤ g.r d := by
  unfold lo r
  have h := g.hT d
  have h1 : 1 ≤ g.B := by have := g.hB; omega
  obtain ⟨a, ha⟩ : ∃ a, g.T (d + 1) - g.T d = a + g.B := ⟨g.T (d + 1) - g.T d - g.B, by omega⟩
  rw [ha, Nat.add_sub_cancel, pow_add]
  calc 2 * 2 ^ a = 2 ^ a * 2 ^ 1 := by ring
    _ ≤ 2 ^ a * 2 ^ g.B := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h1)

theorem N₀_q : (g.N₀ : ℝ) * g.q 0 = 1 - 2 * g.β := by
  unfold N₀ q β
  have h := g.hT0
  have hB := g.hB
  have hle : 2 * 2 ^ (g.T 0 - g.B) ≤ 2 ^ g.T 0 := by
    calc 2 * 2 ^ (g.T 0 - g.B) = 2 ^ (g.T 0 - g.B + 1) := by ring
      _ ≤ 2 ^ g.T 0 := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.cast_sub hle]
  push_cast
  have e1 : (2 : ℝ) ^ g.T 0 = 2 ^ (g.T 0 - g.B) * 2 ^ g.B := by
    rw [← pow_add]; congr 1; omega
  rw [e1]
  field_simp

/-- Valid cells lie in `[β, 1-β)`. -/
theorem valid_bounds (d c : ℕ) (h : g.valid d c) :
    g.β ≤ g.cpos d c ∧ g.cpos d c + g.q d ≤ 1 - g.β := by
  induction d generalizing c with
  | zero =>
    have hc : c < g.N₀ := h
    unfold cpos
    have hq := g.q_pos 0
    have h0 : (0 : ℝ) ≤ c * g.q 0 := by positivity
    have hc' : (c : ℝ) + 1 ≤ g.N₀ := by exact_mod_cast hc
    have := g.N₀_q
    constructor
    · linarith
    · nlinarith
  | succ d ih =>
    obtain ⟨-, hhi, hv⟩ := h
    obtain ⟨h1, h2⟩ := ih _ hv
    unfold cpos at *
    have hq := g.q_succ d
    have hqp := g.q_pos (d + 1)
    have hdecomp : (c : ℝ) = (c / g.r d : ℕ) * g.r d + (c % g.r d : ℕ) := by
      exact_mod_cast (Nat.div_add_mod' c (g.r d)).symm
    have hmod : ((c % g.r d : ℕ) : ℝ) + 1 ≤ g.r d := by
      have := Nat.mod_lt c (g.r_pos d)
      exact_mod_cast this
    constructor
    · have : (0 : ℝ) ≤ c * g.q (d + 1) := by positivity
      linarith
    · calc g.β + c * g.q (d + 1) + g.q (d + 1)
          = g.β + ((c / g.r d : ℕ) * g.r d + ((c % g.r d : ℕ) + 1)) * g.q (d + 1) := by
            rw [hdecomp]; ring
        _ ≤ g.β + ((c / g.r d : ℕ) * g.r d + g.r d) * g.q (d + 1) := by gcongr
        _ = g.β + (c / g.r d : ℕ) * g.q d + g.q d := by rw [hq]; ring
        _ ≤ 1 - g.β := h2

/-- **Plateau.** A point of a valid child, moved back by less than `β q d`, lies in the parent
cell. -/
theorem plateau (d c : ℕ) (h : g.valid (d + 1) c) {x s : ℝ}
    (hx : g.cpos (d + 1) c ≤ x ∧ x < g.cpos (d + 1) c + g.q (d + 1))
    (hs0 : 0 ≤ s) (hs : s ≤ g.β * g.q d) :
    g.cpos d (c / g.r d) ≤ x - s ∧ x - s < g.cpos d (c / g.r d) + g.q d := by
  obtain ⟨hlo, -, -⟩ := h
  unfold cpos at *
  have hq := g.q_succ d
  have hqp := g.q_pos (d + 1)
  have hdecomp : (c : ℝ) = (c / g.r d : ℕ) * g.r d + (c % g.r d : ℕ) := by
    exact_mod_cast (Nat.div_add_mod' c (g.r d)).symm
  have hlo' : (g.lo d : ℝ) ≤ (c % g.r d : ℕ) := by exact_mod_cast hlo
  have hloe := g.lo_eq d
  have hmod : ((c % g.r d : ℕ) : ℝ) + 1 ≤ g.r d := by
    have := Nat.mod_lt c (g.r_pos d)
    exact_mod_cast this
  constructor
  · have : g.β * g.q d ≤ ((c % g.r d : ℕ) : ℝ) * g.q (d + 1) := by
      have e : g.β * g.q d = (g.lo d : ℝ) * g.q (d + 1) := by rw [hq, hloe]; ring
      rw [e]; nlinarith
    have e : g.β + c * g.q (d + 1) =
        g.β + (c / g.r d : ℕ) * g.q d + ((c % g.r d : ℕ) : ℝ) * g.q (d + 1) := by
      rw [hdecomp, hq]; ring
    linarith
  · have : g.β + c * g.q (d + 1) + g.q (d + 1) ≤ g.β + (c / g.r d : ℕ) * g.q d + g.q d := by
      calc g.β + c * g.q (d + 1) + g.q (d + 1)
          = g.β + ((c / g.r d : ℕ) * g.r d + ((c % g.r d : ℕ) + 1)) * g.q (d + 1) := by
            rw [hdecomp]; ring
        _ ≤ g.β + ((c / g.r d : ℕ) * g.r d + g.r d) * g.q (d + 1) := by gcongr
        _ = g.β + (c / g.r d : ℕ) * g.q d + g.q d := by rw [hq]; ring
    linarith

/-- The cell of a point of a cell is that cell. -/
theorem cellOf_eq (d c : ℕ) {x : ℝ} (hx : g.cpos d c ≤ x ∧ x < g.cpos d c + g.q d) :
    g.cellOf d x = c := by
  unfold cellOf
  unfold cpos at hx
  have hq := g.q_pos d
  rw [Nat.floor_eq_iff (by
    have : (0 : ℝ) ≤ c * g.q d := by positivity
    exact div_nonneg (by linarith) hq.le)]
  constructor
  · rw [le_div_iff₀ hq]; linarith
  · rw [div_lt_iff₀ hq]; linarith

/-- A point above `β` lies in the cell `cellOf`. -/
theorem mem_cellOf (d : ℕ) {x : ℝ} (hx : g.β ≤ x) :
    g.cpos d (g.cellOf d x) ≤ x ∧ x < g.cpos d (g.cellOf d x) + g.q d := by
  unfold cpos cellOf
  have hq := g.q_pos d
  have h0 : 0 ≤ (x - g.β) / g.q d := div_nonneg (by linarith) hq.le
  have h1 := Nat.floor_le h0
  have h2 := Nat.lt_floor_add_one ((x - g.β) / g.q d)
  rw [le_div_iff₀ hq] at h1
  rw [div_lt_iff₀ hq] at h2
  constructor <;> nlinarith

/-- Valid cells are below `2^(T d)`. -/
theorem valid_lt (d c : ℕ) (h : g.valid d c) : c < 2 ^ g.T d := by
  obtain ⟨-, h2⟩ := g.valid_bounds d c h
  unfold cpos q at h2
  have hβ := g.β_pos
  have hp : (0 : ℝ) < 2 ^ g.T d := by positivity
  have : ((c : ℝ) + 1) / 2 ^ g.T d ≤ 1 := by
    have : g.β + c * (1 / 2 ^ g.T d) + 1 / 2 ^ g.T d ≤ 1 := by linarith
    calc ((c : ℝ) + 1) / 2 ^ g.T d = c * (1 / 2 ^ g.T d) + 1 / 2 ^ g.T d := by ring
      _ ≤ 1 := by linarith
  rw [div_le_one hp] at this
  have : (c : ℝ) < 2 ^ g.T d := by linarith
  exact_mod_cast this

/-- The time exponents increase. -/
theorem T_mono {d d' : ℕ} (h : d ≤ d') : g.T d ≤ g.T d' := by
  obtain ⟨k, rfl⟩ : ∃ k, d' = d + k := ⟨d' - d, by omega⟩
  clear h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show d + (k + 1) = d + k + 1 by ring]
    have := g.hT (d + k)
    omega

/-- Ancestors of valid cells are valid. -/
theorem valid_anc (d k c : ℕ) (h : g.valid (d + k) c) :
    g.valid d (c / 2 ^ (g.T (d + k) - g.T d)) := by
  induction k generalizing c with
  | zero => simpa using h
  | succ k ih =>
    rw [show d + (k + 1) = d + k + 1 by ring] at h ⊢
    obtain ⟨-, -, hv⟩ := h
    have := ih (c / g.r (d + k)) hv
    have hmono : g.T d ≤ g.T (d + k) := g.T_mono (by omega)
    have h1 := g.hT (d + k)
    have e : c / 2 ^ (g.T (d + k + 1) - g.T d) =
        c / g.r (d + k) / 2 ^ (g.T (d + k) - g.T d) := by
      unfold r
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      congr 2
      omega
    rw [e]
    exact this

/-- **Step.** A point of a valid cell at relative distance at least `β + 1/r` from its left end
and `2β + 1/r` from its right end, moved forward by less than `β q d`, lies in a valid child. -/
theorem step (d c : ℕ) (h : g.valid d c) {x s : ℝ}
    (hx : g.cpos d c ≤ x ∧ x < g.cpos d c + g.q d)
    (hs0 : 0 ≤ s) (hs : s < g.β * g.q d)
    (hf1 : (g.β + 1 / g.r d) * g.q d ≤ x - g.cpos d c)
    (hf2 : x - g.cpos d c < (1 - 2 * g.β - 1 / g.r d) * g.q d) :
    g.valid (d + 1) (g.cellOf (d + 1) (x + s)) ∧
      g.cpos (d + 1) (g.cellOf (d + 1) (x + s)) ≤ x + s ∧
      x + s < g.cpos (d + 1) (g.cellOf (d + 1) (x + s)) + g.q (d + 1) := by
  have hq := g.q_succ d
  have hqp := g.q_pos (d + 1)
  have hqd := g.q_pos d
  have hr := g.r_pos d
  have hr' : (0 : ℝ) < g.r d := by exact_mod_cast hr
  have hloe := g.lo_eq d
  set R : ℝ := (g.r d : ℝ) with hR
  -- position of `x + s` relative to the parent cell, in child meshes
  set z : ℝ := (x + s - g.cpos d c) / g.q (d + 1) with hz
  have hzlo : (g.lo d : ℝ) + 1 ≤ z := by
    rw [hz, le_div_iff₀ hqp, hloe]
    have : (g.β + 1 / R) * g.q d = (R * g.β + 1) * g.q (d + 1) := by
      rw [hq]; field_simp
    nlinarith
  have hzhi : z < R - g.lo d - 1 := by
    rw [hz, div_lt_iff₀ hqp, hloe]
    have : (1 - 2 * g.β - 1 / R) * g.q d + g.β * g.q d = (R - R * g.β - 1) * g.q (d + 1) := by
      rw [hq]; field_simp; ring
    nlinarith
  set m := ⌊z⌋₊ with hm
  have hz0 : 0 ≤ z := by linarith [show (0 : ℝ) ≤ g.lo d from by positivity]
  have hm1 : (m : ℝ) ≤ z := Nat.floor_le hz0
  have hm2 : z < m + 1 := Nat.lt_floor_add_one z
  have hmlo : g.lo d + 1 ≤ m := by
    have := Nat.floor_le_floor (a := (g.lo d : ℝ) + 1) hzlo
    rwa [show ((g.lo d : ℝ) + 1) = ((g.lo d + 1 : ℕ) : ℝ) by push_cast; ring,
      Nat.floor_natCast] at this
  have hmhi : m + 1 < g.r d - g.lo d := by
    have h1 : (m : ℝ) < R - g.lo d - 1 := lt_of_le_of_lt hm1 hzhi
    have h2 : g.lo d ≤ g.r d := by have := g.lo_lt_r d; omega
    have h3 : (m : ℝ) + 1 < ((g.r d - g.lo d : ℕ) : ℝ) := by
      rw [Nat.cast_sub h2]; linarith
    exact_mod_cast h3
  -- the child cell
  have hcell : g.cellOf (d + 1) (x + s) = c * g.r d + m := by
    apply g.cellOf_eq
    unfold cpos
    unfold cpos at hx
    have e : g.β + ((c * g.r d + m : ℕ) : ℝ) * g.q (d + 1) =
        g.β + c * g.q d + m * g.q (d + 1) := by
      push_cast; rw [hq]; ring
    rw [e]
    have hzdef : x + s - (g.β + c * g.q d) = z * g.q (d + 1) := by
      rw [hz]; unfold cpos; field_simp
    constructor
    · nlinarith
    · nlinarith
  have hmr : m < g.r d := by omega
  have hdiv : (c * g.r d + m) / g.r d = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt hmr, zero_add]
  have hmod : (c * g.r d + m) % g.r d = m := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hmr]
  rw [hcell]
  refine ⟨⟨by rw [hmod]; omega, by rw [hmod]; omega, by rw [hdiv]; exact h⟩, ?_, ?_⟩
  · unfold cpos; unfold cpos at hx
    have e : g.β + ((c * g.r d + m : ℕ) : ℝ) * g.q (d + 1) =
        g.β + c * g.q d + m * g.q (d + 1) := by push_cast; rw [hq]; ring
    rw [e]
    have hzdef : x + s - (g.β + c * g.q d) = z * g.q (d + 1) := by
      rw [hz]; unfold cpos; field_simp
    nlinarith
  · unfold cpos; unfold cpos at hx
    have e : g.β + ((c * g.r d + m : ℕ) : ℝ) * g.q (d + 1) =
        g.β + c * g.q d + m * g.q (d + 1) := by push_cast; rw [hq]; ring
    rw [e]
    have hzdef : x + s - (g.β + c * g.q d) = z * g.q (d + 1) := by
      rw [hz]; unfold cpos; field_simp
    nlinarith

end Grid

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
