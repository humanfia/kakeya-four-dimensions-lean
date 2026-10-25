import Submission.Obl.k4_finite_positive_prepared_models.Synthetic.ModelDefs

/-!
# Parameters of the synthetic model

For a stage `n ≥ 2` and rates `d₁ ∈ [0,1)`, `κ₁ ∈ (0,1]`, `ℓ > 0`, levels `d ≤ D` sit at the
scales `sc d = (m₀ + d) / (n m₀) ∈ [1/n, 1]`, with spacing `1/(n m₀)` small against
`1/((ℓ+2)(n+1))`. The resolution is `2^Λ` and the loss `2^(Λ/(n+1))`; `Λ` is large enough
for every rounding to fit the loss. Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_positive_prepared_models.Synthetic

noncomputable section

/-- The stage and the rates. -/
structure Par where
  n : ℕ
  d₁ : ℝ
  κ₁ : ℝ
  ℓ : ℝ
  hn : 2 ≤ n
  hd₁ : 0 ≤ d₁
  hd₁' : d₁ < 1
  hκ : 0 < κ₁
  hκ' : κ₁ ≤ 1
  hℓ : 0 < ℓ

namespace Par

variable (p : Par)

def m₀ : ℕ := ⌈4 * (p.ℓ + 2) * (p.n + 1)⌉₊ + 1
def D : ℕ := (p.n - 1) * p.m₀
def B : ℕ := p.D + 6
def e : ℕ := p.n + 1
def e₁ : ℕ := ⌈p.d₁ * p.e⌉₊
def Λ : ℕ := ⌈((p.B : ℝ) + 1) * p.n * p.m₀ / p.κ₁⌉₊ + 4 * (p.n + 1) * (p.B + p.n + 10)

/-- The scale of level `d`. -/
def sc (d : ℕ) : ℝ := ((p.m₀ + d : ℕ) : ℝ) / (p.n * p.m₀)

def T (d : ℕ) : ℕ := ⌊p.κ₁ * p.sc d * p.Λ⌋₊
def Ux (d : ℕ) : ℕ := p.T d + ⌊p.ℓ * p.sc d * p.Λ⌋₊
def Gh (d : ℕ) : ℕ := ⌊p.sc d * p.Λ / p.e⌋₊
def G : ℕ := p.n * p.Λ

/-- The loss exponent `Λ / (n+1)`. -/
def σ : ℝ := (p.Λ : ℝ) / (p.n + 1)

theorem n_pos : (0 : ℝ) < p.n := by have := p.hn; exact_mod_cast (by omega : 0 < p.n)
theorem m₀_pos : 0 < p.m₀ := by unfold m₀; omega
theorem m₀_pos' : (0 : ℝ) < p.m₀ := by exact_mod_cast p.m₀_pos
theorem nm₀_pos : (0 : ℝ) < p.n * p.m₀ := mul_pos p.n_pos p.m₀_pos'

theorem m₀_ge : 4 * (p.ℓ + 2) * (p.n + 1) < p.m₀ := by
  unfold m₀
  push_cast
  have := Nat.le_ceil (4 * (p.ℓ + 2) * ((p.n : ℝ) + 1))
  linarith

theorem sc_succ (d : ℕ) : p.sc (d + 1) = p.sc d + 1 / (p.n * p.m₀) := by
  unfold sc
  push_cast
  field_simp
  ring

theorem sc_zero : p.sc 0 = 1 / p.n := by
  unfold sc
  have := p.m₀_pos'
  have := p.n_pos
  simp only [Nat.add_zero]
  field_simp

theorem sc_D : p.sc p.D = 1 := by
  unfold sc D
  have := p.nm₀_pos
  have hn : 1 ≤ p.n := by have := p.hn; omega
  rw [div_eq_one_iff_eq this.ne']
  push_cast [Nat.cast_sub hn]
  ring

theorem sc_mono {d d' : ℕ} (h : d ≤ d') : p.sc d ≤ p.sc d' := by
  unfold sc
  apply div_le_div_of_nonneg_right _ p.nm₀_pos.le
  exact_mod_cast (by omega : p.m₀ + d ≤ p.m₀ + d')

theorem sc_pos (d : ℕ) : 0 < p.sc d := by
  unfold sc
  have := p.m₀_pos
  exact div_pos (by exact_mod_cast (by omega : 0 < p.m₀ + d)) p.nm₀_pos

theorem Λ_ge1 : ((p.B : ℝ) + 1) * p.n * p.m₀ / p.κ₁ ≤ p.Λ := by
  unfold Λ
  push_cast
  have := Nat.le_ceil (((p.B : ℝ) + 1) * p.n * p.m₀ / p.κ₁)
  have h2 : (0 : ℝ) ≤ 4 * (p.n + 1) * (p.B + p.n + 10) := by positivity
  linarith

theorem Λ_ge2 : 4 * ((p.n : ℝ) + 1) * (p.B + p.n + 10) ≤ p.Λ := by
  unfold Λ
  push_cast
  have : (0 : ℝ) ≤ ⌈((p.B : ℝ) + 1) * p.n * p.m₀ / p.κ₁⌉₊ := by positivity
  linarith

/-- One level step in time exponent units is at least `B + 1`. -/
theorem step_ge : (p.B : ℝ) + 1 ≤ p.κ₁ * p.Λ / (p.n * p.m₀) := by
  have h := p.Λ_ge1
  have hκ := p.hκ
  have hnm := p.nm₀_pos
  rw [le_div_iff₀ hnm]
  rw [div_le_iff₀ hκ] at h
  nlinarith

theorem σ_ge : 4 * ((p.B : ℝ) + p.n + 10) ≤ p.σ := by
  unfold σ
  rw [le_div_iff₀ (by positivity)]
  nlinarith [p.Λ_ge2]

theorem step_le_σ : p.Λ / (p.n * p.m₀) ≤ p.σ / (4 * (p.ℓ + 2)) := by
  unfold σ
  have hm := p.m₀_ge
  have hn := p.n_pos
  have hℓ := p.hℓ
  have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
  rw [div_div, div_le_div_iff₀ p.nm₀_pos (by positivity)]
  have : (p.n + 1 : ℝ) * (4 * (p.ℓ + 2)) ≤ p.n * p.m₀ := by
    have h1 : (1 : ℝ) ≤ p.n := by have := p.hn; exact_mod_cast (by omega : 1 ≤ p.n)
    nlinarith
  nlinarith

theorem T_succ (d : ℕ) : p.T d + p.B ≤ p.T (d + 1) := by
  unfold T
  rw [p.sc_succ, show p.κ₁ * (p.sc d + 1 / (p.n * p.m₀)) * p.Λ =
    p.κ₁ * p.sc d * p.Λ + p.κ₁ * p.Λ / (p.n * p.m₀) by field_simp]
  have h0 : 0 ≤ p.κ₁ * p.sc d * p.Λ := by
    have := p.hκ; have := p.sc_pos d; positivity
  have h1 : 0 ≤ p.κ₁ * p.Λ / (p.n * p.m₀) := by
    have := p.hκ; have := p.nm₀_pos; positivity
  have h2 : ⌊p.κ₁ * p.sc d * p.Λ⌋₊ + ⌊p.κ₁ * p.Λ / (p.n * p.m₀)⌋₊ ≤
      ⌊p.κ₁ * p.sc d * p.Λ + p.κ₁ * p.Λ / (p.n * p.m₀)⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith [Nat.floor_le h0, Nat.floor_le h1]
  have h3 : p.B + 1 ≤ ⌊p.κ₁ * p.Λ / (p.n * p.m₀)⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact p.step_ge
  omega

theorem T_zero : p.B + 1 ≤ p.T 0 := by
  unfold T
  apply Nat.le_floor
  rw [p.sc_zero]
  have h := p.step_ge
  have hm : (1 : ℝ) ≤ p.m₀ := by exact_mod_cast p.m₀_pos
  have hκ := p.hκ
  have hn := p.n_pos
  calc ((p.B + 1 : ℕ) : ℝ) = (p.B : ℝ) + 1 := by push_cast; ring
    _ ≤ p.κ₁ * p.Λ / (p.n * p.m₀) := h
    _ ≤ p.κ₁ * (1 / p.n) * p.Λ := by
        rw [div_le_iff₀ p.nm₀_pos]
        have : (0 : ℝ) ≤ p.κ₁ * p.Λ := by positivity
        field_simp
        nlinarith

theorem e₁_le : p.e₁ ≤ p.e := by
  unfold e₁ e
  apply Nat.ceil_le.mpr
  push_cast
  have := p.hd₁'
  have : (0 : ℝ) ≤ p.n + 1 := by positivity
  nlinarith

/-- The synthetic model data of the parameters. -/
def synth : Synth where
  B := p.B
  D := p.D
  T := p.T
  hB := by unfold B; omega
  hT0 := p.T_zero
  hT := p.T_succ
  Ux := p.Ux
  hUx := by
    intro d
    unfold Ux
    have h1 := p.T_succ d
    have h2 : ⌊p.ℓ * p.sc d * p.Λ⌋₊ ≤ ⌊p.ℓ * p.sc (d + 1) * p.Λ⌋₊ := by
      apply Nat.floor_le_floor
      have := p.sc_mono (Nat.le_succ d)
      have := p.hℓ
      have : (0 : ℝ) ≤ p.Λ := by positivity
      gcongr
    omega
  e := p.e
  e₁ := p.e₁
  he := p.e₁_le
  G := p.G
  Gh := p.Gh
  hGh := by
    intro d
    unfold Gh
    apply Nat.floor_le_floor
    have := p.sc_mono (Nat.le_succ d)
    have : (0 : ℝ) ≤ p.Λ := by positivity
    gcongr
  hGhG := by
    intro d hd
    unfold Gh G
    apply Nat.floor_le_of_le
    have h1 : p.sc d ≤ 1 := (p.sc_mono hd).trans p.sc_D.le
    have he : (1 : ℝ) ≤ p.e := by unfold e; push_cast; linarith [p.n_pos]
    have hn : (1 : ℝ) ≤ p.n := by have := p.hn; exact_mod_cast (by omega : 1 ≤ p.n)
    have hΛ : (0 : ℝ) ≤ p.Λ := by positivity
    push_cast
    rw [div_le_iff₀ (by linarith)]
    have := p.sc_pos d
    have k1 : p.sc d * p.Λ ≤ p.Λ := by nlinarith
    have k2 : (p.Λ : ℝ) ≤ p.n * p.Λ := by nlinarith
    have k3 : (p.n : ℝ) * p.Λ ≤ p.n * p.Λ * p.e := by
      have : (0 : ℝ) ≤ p.n * p.Λ := by positivity
      nlinarith
    linarith

theorem synth_hBD : 64 * (p.synth.D + 1) ≤ 2 ^ p.synth.B := by
  show 64 * (p.D + 1) ≤ 2 ^ (p.D + 6)
  rw [pow_add]
  have := Nat.lt_two_pow_self (n := p.D)
  omega

end Par

end

end Submission.Obl.k4_finite_positive_prepared_models.Synthetic
