import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.Basics

/-!
# Spread of a label

Two incidences `(l, t)`, `(l', t')` of one label differ in `x2` by `O(K δ + K q g)` and in
`x3` by `O(K a + K (1 + a/q) δ + K (1 + a/q²)(K q δ + K q g))`, where `δ` bounds their time
and first-position differences. The `x3` bound uses the horizontal slope bound and the
centering of the label, through
`L1 Δt + L2 Δx1 + L3 Δx2 = S1 Δt + S2 Δx1 + L3 (Δx2 + x1 Δt - t Δx1)`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem blk_time_close {T : ℕ} {j : ℕ} {t t' : ℝ} (ht : t ∈ blk T j) (ht' : t' ∈ blk T j) :
    |t - t'| ≤ ((2 : ℝ) ^ T)⁻¹ := by
  obtain ⟨h1, h2⟩ := ht
  obtain ⟨h1', h2'⟩ := ht'
  have e : ((j : ℝ) + 1) / 2 ^ T = (j : ℝ) / 2 ^ T + ((2 : ℝ) ^ T)⁻¹ := by rw [add_div, one_div]
  rw [e] at h2 h2'
  rw [abs_le]; constructor <;> linarith

theorem blk_mid_close {T : ℕ} {j : ℕ} {t : ℝ} (ht : t ∈ blk T j) :
    |t - ((j : ℝ) + 1 / 2) * ((2 : ℝ) ^ T)⁻¹| ≤ ((2 : ℝ) ^ T)⁻¹ / 2 := by
  obtain ⟨h1, h2⟩ := ht
  have e1 : (j : ℝ) / 2 ^ T = (j : ℝ) * ((2 : ℝ) ^ T)⁻¹ := by rw [div_eq_mul_inv]
  have e2 : ((j : ℝ) + 1) / 2 ^ T = ((j : ℝ) + 1) * ((2 : ℝ) ^ T)⁻¹ := by rw [div_eq_mul_inv]
  rw [e1] at h1; rw [e2] at h2
  rw [abs_le]; constructor <;> nlinarith

/-- First-position and time spread of a label. -/
theorem label_spread_basic {ν : Measure α} {μ : Measure (α × ℝ)} {π : Measure ℝ}
    {b : α → Fin 6 → ℝ} {N K d κ s χ : ℝ} {f : Fam α} (hf : f.Good ν μ π b N K d κ s χ)
    {i : Fin f.n} {p p' : α × ℝ} (hp : p.1 ∈ f.A i ∧ p.2 ∈ f.I i)
    (hp' : p'.1 ∈ f.A i ∧ p'.2 ∈ f.I i) :
    |p.2 - p'.2| ≤ f.q ∧ |x1 b p.1 p.2 - x1 b p'.1 p'.2| ≤ 3 * K * f.q := by
  have ht := blk_time_close hp.2 hp'.2
  have hq : f.q = ((2 : ℝ) ^ f.T)⁻¹ := rfl
  rw [← hq] at ht
  refine ⟨ht, ?_⟩
  have g1 := (hf.geom i p.1 hp.1 p.2 hp.2).1
  have g1' := (hf.geom i p'.1 hp'.1 p'.2 hp'.2).1
  have hc1 := hf.cbd i 1
  have e : x1 b p.1 p.2 - x1 b p'.1 p'.2 = (x1 b p.1 p.2 - f.c i 0 - p.2 * f.c i 1) -
      (x1 b p'.1 p'.2 - f.c i 0 - p'.2 * f.c i 1) + (p.2 - p'.2) * f.c i 1 := by ring
  rw [e]
  have h3 : |(p.2 - p'.2) * f.c i 1| ≤ f.q * K := by
    rw [abs_mul]; exact mul_le_mul ht hc1 (abs_nonneg _) (by unfold Fam.q; positivity)
  calc _ ≤ |x1 b p.1 p.2 - f.c i 0 - p.2 * f.c i 1| + |x1 b p'.1 p'.2 - f.c i 0 - p'.2 * f.c i 1| +
        |(p.2 - p'.2) * f.c i 1| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ K * f.q + K * f.q + f.q * K := add_le_add (add_le_add g1 g1') h3
    _ = 3 * K * f.q := by ring

/-- Second-position and hidden spread of a label, at time and first-position spread `δt, δ1`. -/
theorem label_spread {ν : Measure α} {μ : Measure (α × ℝ)} {π : Measure ℝ}
    {b : α → Fin 6 → ℝ} {N K d κ s χ : ℝ} {f : Fam α} (hf : f.Good ν μ π b N K d κ s χ)
    (hK : 1 ≤ K) (hN : 0 < N) {i : Fin f.n} {p p' : α × ℝ} (hp : p.1 ∈ f.B i ∧ p.2 ∈ f.I i)
    (hp' : p'.1 ∈ f.B i ∧ p'.2 ∈ f.I i) {δt δ1 : ℝ}
    (ht : |p.2 - p'.2| ≤ δt) (h1 : |x1 b p.1 p.2 - x1 b p'.1 p'.2| ≤ δ1) :
    |x2 b p.1 p.2 - x2 b p'.1 p'.2| ≤ K * δt + K * δ1 + 2 * (K * f.q * N ^ (-κ * s)) ∧
    |x3 b p.1 p.2 - x3 b p'.1 p'.2| ≤ 2 * (K * N ^ (-s)) + K * (1 + N ^ (-s) / f.q) * (δt + δ1) +
      K * (1 + N ^ (-s) / f.q ^ 2) *
        (5 / 2 * K * f.q * δt + 3 / 2 * K * f.q * δ1 + 2 * (K * f.q * N ^ (-κ * s))) := by
  have hK0 : 0 ≤ K := by linarith
  have hq : 0 < f.q := by unfold Fam.q; positivity
  have hpA : p.1 ∈ f.A i := hf.BA i hp.1
  have hpA' : p'.1 ∈ f.A i := hf.BA i hp'.1
  obtain ⟨-, g2, -⟩ := hf.geom i p.1 hpA p.2 hp.2
  obtain ⟨-, g2', -⟩ := hf.geom i p'.1 hpA' p'.2 hp'.2
  have g1 := (hf.geom i p.1 hpA p.2 hp.2).1
  have hc := hf.cbd i
  have hcen := hf.center i
  set g := N ^ (-κ * s)
  set a := N ^ (-s)
  set c := f.c i
  set t := p.2
  set t' := p'.2
  set X1 := x1 b p.1 p.2
  set X1' := x1 b p'.1 p'.2
  set X2 := x2 b p.1 p.2
  set X2' := x2 b p'.1 p'.2
  have hδt : 0 ≤ δt := (abs_nonneg _).trans ht
  have hδ1 : 0 ≤ δ1 := (abs_nonneg _).trans h1
  -- second position
  have hE2 : |(X2 - c 2 - t * c 3 - c 4 * X1) - (X2' - c 2 - t' * c 3 - c 4 * X1')| ≤
      2 * (K * f.q * g) := by
    refine (abs_sub _ _).trans ?_; linarith
  have hx2 : |X2 - X2'| ≤ K * δt + K * δ1 + 2 * (K * f.q * g) := by
    have e : X2 - X2' = c 3 * (t - t') + c 4 * (X1 - X1') +
        ((X2 - c 2 - t * c 3 - c 4 * X1) - (X2' - c 2 - t' * c 3 - c 4 * X1')) := by ring
    rw [e]
    calc _ ≤ |c 3 * (t - t')| + |c 4 * (X1 - X1')| +
          |(X2 - c 2 - t * c 3 - c 4 * X1) - (X2' - c 2 - t' * c 3 - c 4 * X1')| :=
          abs_add_three _ _ _
      _ ≤ K * δt + K * δ1 + 2 * (K * f.q * g) := by
          gcongr
          · rw [abs_mul]; exact mul_le_mul (hc 3) ht (abs_nonneg _) hK0
          · rw [abs_mul]; exact mul_le_mul (hc 4) h1 (abs_nonneg _) hK0
  refine ⟨hx2, ?_⟩
  -- hidden coordinate
  have hfit := hf.fit i p.1 hp.1 t hp.2
  have hfit' := hf.fit i p'.1 hp'.1 t' hp'.2
  have hsl := hf.slope i p.1 hp.1 t hp.2
  have hL3 := hf.L3bd i
  set L := f.L i
  -- centering
  have htm : |t - ((f.j i : ℕ) + 1 / 2 : ℝ) * f.q| ≤ f.q / 2 := blk_mid_close hp.2
  have hc31 : |c 3 + X1| ≤ 5 / 2 * K * f.q := by
    have e : c 3 + X1 = (c 3 + c 0 + (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q * c 1) +
        (X1 - c 0 - t * c 1) + (t - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q) * c 1 := by ring
    rw [e]
    have hA : |c 3 + c 0 + (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q * c 1| ≤ K * f.q := by
      linarith [abs_nonneg (c 4 - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q)]
    have hC : |(t - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q) * c 1| ≤ f.q / 2 * K := by
      rw [abs_mul]; exact mul_le_mul htm (hc 1) (abs_nonneg _) (by positivity)
    calc _ ≤ |c 3 + c 0 + (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q * c 1| + |X1 - c 0 - t * c 1| +
          |(t - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q) * c 1| := abs_add_three _ _ _
      _ ≤ K * f.q + K * f.q + f.q / 2 * K := add_le_add (add_le_add hA g1) hC
      _ = 5 / 2 * K * f.q := by ring
  have hc4t : |c 4 - t| ≤ 3 / 2 * K * f.q := by
    have hA : |c 4 - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q| ≤ K * f.q := by
      linarith [abs_nonneg (c 3 + c 0 + (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q * c 1)]
    have e : c 4 - t = (c 4 - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q) -
        (t - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q) := by ring
    rw [e]
    calc _ ≤ |c 4 - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q| +
          |t - (((f.j i : ℕ) : ℝ) + 1 / 2) * f.q| := abs_sub _ _
      _ ≤ K * f.q + f.q / 2 := add_le_add hA htm
      _ ≤ 3 / 2 * K * f.q := by nlinarith
  -- the twisted second-position difference
  have htw : |(X2 - X2') + X1 * (t - t') - t * (X1 - X1')| ≤
      5 / 2 * K * f.q * δt + 3 / 2 * K * f.q * δ1 + 2 * (K * f.q * g) := by
    have e : (X2 - X2') + X1 * (t - t') - t * (X1 - X1') =
        (c 3 + X1) * (t - t') + (c 4 - t) * (X1 - X1') +
        ((X2 - c 2 - t * c 3 - c 4 * X1) - (X2' - c 2 - t' * c 3 - c 4 * X1')) := by ring
    rw [e]
    calc _ ≤ |(c 3 + X1) * (t - t')| + |(c 4 - t) * (X1 - X1')| +
          |(X2 - c 2 - t * c 3 - c 4 * X1) - (X2' - c 2 - t' * c 3 - c 4 * X1')| :=
          abs_add_three _ _ _
      _ ≤ 5 / 2 * K * f.q * δt + 3 / 2 * K * f.q * δ1 + 2 * (K * f.q * g) := by
          gcongr
          · rw [abs_mul]; exact mul_le_mul hc31 ht (abs_nonneg _) (by positivity)
          · rw [abs_mul]; exact mul_le_mul hc4t h1 (abs_nonneg _) (by positivity)
  -- the affine difference
  have hdL : |f.fitVal i t X1 X2 - f.fitVal i t' X1' X2'| ≤
      K * (1 + a / f.q) * (δt + δ1) +
        K * (1 + a / f.q ^ 2) * (5 / 2 * K * f.q * δt + 3 / 2 * K * f.q * δ1 + 2 * (K * f.q * g)) := by
    unfold Fam.fitVal
    have e : (L 0 + L 1 * t + L 2 * X1 + L 3 * X2) - (L 0 + L 1 * t' + L 2 * X1' + L 3 * X2') =
        (L 1 - X1 * L 3) * (t - t') + (L 2 + t * L 3) * (X1 - X1') +
          L 3 * ((X2 - X2') + X1 * (t - t') - t * (X1 - X1')) := by ring
    rw [e]
    have hS1 : |L 1 - X1 * L 3| ≤ K * (1 + a / f.q) := by linarith [abs_nonneg (L 2 + t * L 3)]
    have hS2 : |L 2 + t * L 3| ≤ K * (1 + a / f.q) := by linarith [abs_nonneg (L 1 - X1 * L 3)]
    have ha : 0 ≤ a := Real.rpow_nonneg hN.le _
    have hpos : 0 ≤ K * (1 + a / f.q) := by positivity
    have hpos2 : 0 ≤ K * (1 + a / f.q ^ 2) := by positivity
    calc _ ≤ |(L 1 - X1 * L 3) * (t - t')| + |(L 2 + t * L 3) * (X1 - X1')| +
          |L 3 * ((X2 - X2') + X1 * (t - t') - t * (X1 - X1'))| := abs_add_three _ _ _
      _ ≤ K * (1 + a / f.q) * δt + K * (1 + a / f.q) * δ1 +
          K * (1 + a / f.q ^ 2) *
            (5 / 2 * K * f.q * δt + 3 / 2 * K * f.q * δ1 + 2 * (K * f.q * g)) := by
          gcongr
          · rw [abs_mul]; exact mul_le_mul hS1 ht (abs_nonneg _) hpos
          · rw [abs_mul]; exact mul_le_mul hS2 h1 (abs_nonneg _) hpos
          · rw [abs_mul]; exact mul_le_mul hL3 htw (abs_nonneg _) hpos2
      _ = _ := by ring
  have e : x3 b p.1 p.2 - x3 b p'.1 p'.2 = (x3 b p.1 p.2 - f.fitVal i t X1 X2) +
      (f.fitVal i t X1 X2 - f.fitVal i t' X1' X2') - (x3 b p'.1 p'.2 - f.fitVal i t' X1' X2') := by
    ring
  rw [e]
  calc _ ≤ |x3 b p.1 p.2 - f.fitVal i t X1 X2| + |f.fitVal i t X1 X2 - f.fitVal i t' X1' X2'| +
        |x3 b p'.1 p'.2 - f.fitVal i t' X1' X2'| := by
        refine (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K * a + (K * (1 + a / f.q) * (δt + δ1) + K * (1 + a / f.q ^ 2) *
          (5 / 2 * K * f.q * δt + 3 / 2 * K * f.q * δ1 + 2 * (K * f.q * g))) + K * a :=
        add_le_add (add_le_add hfit hdL) hfit'
    _ = _ := by ring

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
