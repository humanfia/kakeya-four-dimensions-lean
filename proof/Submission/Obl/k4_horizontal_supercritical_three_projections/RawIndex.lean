import Submission.Obl.k4_horizontal_supercritical_three_projections.RawGood

/-!
# The raw chart estimates at one index

At one index `k` the raw chart data (total chart cap, pure and angular scalar
cell caps, terminal support count) follow from the true blocks of the depth,
the original caps, and finitely many explicit numerical inequalities between
powers of `N` and `K`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Filter Parent
open Submission.Obl.k4_fixed_budget_quadratic_recovery
open scoped ENNReal

noncomputable section

theorem floor_div_eq_iff_mem_Ico {χ : ℝ} (hχ : 0 < χ) (β : ℤ) :
    {x : ℝ | ⌊x / χ⌋ = β} = Ico ((β : ℝ) * χ) (((β : ℝ) + 1) * χ) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Ico, Int.floor_eq_iff]
  rw [le_div_iff₀ hχ, div_lt_iff₀ hχ]

/-- Powers of `N` compare as their exponents. -/
theorem rpow_le_rpow_of_le_exp {N x y : ℝ} (hN : 1 ≤ N) (hxy : x ≤ y) :
    N ^ (-y) ≤ N ^ (-x) :=
  Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- `K`-losses compared with powers of `N`, in multiplicative form. -/
theorem mul_rpow_le_of_le {N C x y : ℝ} (hN : 0 < N) (hC : C ≤ N ^ (x - y)) :
    C * N ^ (-x) ≤ N ^ (-y) := by
  calc C * N ^ (-x) ≤ N ^ (x - y) * N ^ (-x) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hN.le _)
    _ = N ^ (-y) := by rw [← Real.rpow_add hN]; ring_nf

namespace HorizontalModel

variable {α : Type} [MeasurableSpace α] {m : HorizontalModel α}

/-- The original caps at one index and one range `R`. -/
def CapsAt (m : HorizontalModel α) (R : ℝ) (k : ℕ) : Prop :=
  ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
  (∀ a : ℤ, m.π k {w : ℝ | ⌊w / (m.N k ^ (-v))⌋ = a} ≤
    ENNReal.ofReal (m.K k * m.N k ^ (-m.S * v))) ∧
  (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a : ℤ),
    m.μ k {p | m.z k (m.N k) r p = q ∧
      ⌊(if h then MvPolynomial.eval (m.x k p.1 p.2) (m.P k)
        else (m.x k p.1 p.2) 3) / (m.N k ^ (-s))⌋ = a} ≤
      ENNReal.ofReal (m.K k * m.N k ^ (-3 * r - m.d * s))) ∧
  (∀ h : Bool, ∀ (q : Fin 3 → ℤ) (a v₀ : ℤ),
    m.μ k {p | m.z k (m.N k) r p = q ∧
      ⌊(if h then MvPolynomial.eval (m.x k p.1 p.2) (m.P k)
        else (m.x k p.1 p.2) 3) / (m.N k ^ (-s))⌋ = a ∧
      ⌊m.b k p.1 3 / (m.N k ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (m.K k * m.N k ^ (-3 * r - m.d * s)) *
        m.π k {w : ℝ | ⌊w / (m.N k ^ (-v))⌋ = v₀})

theorem Valid.capsAt (h : m.Valid) {R : ℝ} (hR : 1 < R) : ∀ᶠ k in atTop, m.CapsAt R k :=
  h.caps R hR

theorem z_eq (k : ℕ) (Nk r : ℝ) (p : α × ℝ) :
    m.z k Nk r p = (fun e => ⌊(![p.2, m.b k p.1 0 + p.2 * m.b k p.1 3,
      m.b k p.1 1 + p.2 * m.b k p.1 4] : Fin 3 → ℝ) e / Nk ^ (-r)⌋) := by
  funext e; fin_cases e <;> rfl

theorem rpow_cube_mul {N r s d : ℝ} (hN : 0 < N) :
    N ^ (-3 * r - d * s) = (N ^ (-r)) ^ 3 * (N ^ (-s)) ^ d := by
  rw [← Real.rpow_natCast (N ^ (-r)) 3, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le,
    ← Real.rpow_add hN]
  congr 1; push_cast; ring

/-- The pure fine cube caps with unit hidden bins. -/
theorem CapsAt.pure_cube {R : ℝ} {k : ℕ} (hc : m.CapsAt R k) (hR : 1 < R) {r : ℝ}
    (hr₀ : R⁻¹ ≤ r) (hr₁ : r ≤ R) (hN : 0 < m.N k) :
    ∀ (w : Fin 3 → ℤ) (j' : ℤ), m.μ k {p | (fun e => ⌊(![p.2, m.b k p.1 0 + p.2 * m.b k p.1 3,
        m.b k p.1 1 + p.2 * m.b k p.1 4] : Fin 3 → ℝ) e / m.N k ^ (-r)⌋) = w ∧
        ⌊m.b k p.1 2 + p.2 * m.b k p.1 5⌋ = j'} ≤
      ENNReal.ofReal (m.K k * (m.N k ^ (-r)) ^ 3) := by
  intro w j'
  have hR0 : 0 ≤ R := by linarith
  have hRR : R⁻¹ ≤ R := (inv_le_one_of_one_le₀ hR.le).trans hR.le
  have h := (hc r 0 R hr₀ hr₁ le_rfl hR0 hRR le_rfl).2.1 false w j'
  have hset : {p : α × ℝ | m.z k (m.N k) r p = w ∧
      ⌊(if false = true then MvPolynomial.eval (m.x k p.1 p.2) (m.P k)
        else (m.x k p.1 p.2) 3) / (m.N k ^ (-(0 : ℝ)))⌋ = j'} =
      {p | (fun e => ⌊(![p.2, m.b k p.1 0 + p.2 * m.b k p.1 3,
        m.b k p.1 1 + p.2 * m.b k p.1 4] : Fin 3 → ℝ) e / m.N k ^ (-r)⌋) = w ∧
        ⌊m.b k p.1 2 + p.2 * m.b k p.1 5⌋ = j'} := by
    ext p
    simp only [Set.mem_ofPred_eq, z_eq, Bool.false_eq_true, ↓reduceIte, neg_zero,
      Real.rpow_zero, div_one]
    rfl
  rw [hset] at h
  refine h.trans (le_of_eq ?_)
  rw [rpow_cube_mul hN (s := 0)]
  simp

/-- The joint caps of one direction bin, in the form of `DirectionCap`. -/
theorem CapsAt.directionCap {R : ℝ} {k : ℕ} (hc : m.CapsAt R k) {r s M : ℝ}
    (hr₀ : R⁻¹ ≤ r) (hr₁ : r ≤ R) (hs₀ : 0 ≤ s) (hs₁ : s ≤ R) (hM₀ : R⁻¹ ≤ M) (hM₁ : M ≤ R)
    (hN : 0 < m.N k) (β : ℤ) :
    DirectionCap (m.μ k) (m.b k) (m.π k) (m.K k) (m.N k ^ (-r)) (m.N k ^ (-M))
      (m.N k ^ (-s)) m.d β := by
  intro w j'
  have h := (hc r s M hr₀ hr₁ hs₀ hs₁ hM₀ hM₁).2.2 false w j' β
  have hset : {p : α × ℝ | m.z k (m.N k) r p = w ∧
      ⌊(if false = true then MvPolynomial.eval (m.x k p.1 p.2) (m.P k)
        else (m.x k p.1 p.2) 3) / (m.N k ^ (-s))⌋ = j' ∧
      ⌊m.b k p.1 3 / (m.N k ^ (-M))⌋ = β} =
      {p | (fun e => ⌊(![p.2, m.b k p.1 0 + p.2 * m.b k p.1 3,
        m.b k p.1 1 + p.2 * m.b k p.1 4] : Fin 3 → ℝ) e / m.N k ^ (-r)⌋) = w ∧
        ⌊(m.b k p.1 2 + p.2 * m.b k p.1 5) / m.N k ^ (-s)⌋ = j' ∧
        ⌊m.b k p.1 3 / m.N k ^ (-M)⌋ = β} := by
    ext p
    simp only [Set.mem_ofPred_eq, z_eq, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hset] at h
  refine h.trans (le_of_eq ?_)
  rw [rpow_cube_mul hN, mul_assoc]

end HorizontalModel

end

end Submission.Obl.k4_horizontal_supercritical_three_projections

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set Filter Parent
open scoped ENNReal

noncomputable section

/-- The dyadic block length is `g` up to `K`. -/
theorem block_length_bounds {N K κδ : ℝ} {T : ℕ} (hN : 0 < N) (hK : 1 ≤ K)
    (hT1 : N ^ κδ / K ≤ (2 : ℝ) ^ T) (hT2 : (2 : ℝ) ^ T ≤ K * N ^ κδ) :
    N ^ (-κδ) / K ≤ (2 : ℝ) ^ (-(T : ℤ)) ∧ (2 : ℝ) ^ (-(T : ℤ)) ≤ K * N ^ (-κδ) := by
  have hK0 : 0 < K := by linarith
  have hNp : 0 < N ^ κδ := Real.rpow_pos_of_pos hN _
  have h2 : (2 : ℝ) ^ (-(T : ℤ)) = ((2 : ℝ) ^ T)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hneg : N ^ (-κδ) = (N ^ κδ)⁻¹ := Real.rpow_neg hN.le _
  have h2p : 0 < (2 : ℝ) ^ T := by positivity
  rw [h2, hneg]
  constructor
  · have e : (N ^ κδ)⁻¹ / K = (K * N ^ κδ)⁻¹ := by field_simp
    rw [e]
    exact inv_anti₀ h2p hT2
  · have e : K * (N ^ κδ)⁻¹ = (N ^ κδ / K)⁻¹ := by field_simp
    rw [e]
    exact inv_anti₀ (by positivity) hT1

/-- `1 + a/q² ≤ 2K² a/g²` when `q ≥ g/K` and `a ≤ g²`... in the form used for the
contact and oscillation margins. -/
theorem one_add_div_sq_le {a q g K : ℝ} (ha : 0 < a) (hg : 0 < g) (hK : 1 ≤ K)
    (hq : g / K ≤ q) (hag : g ^ 2 ≤ a * K ^ 2) :
    1 + a / q ^ 2 ≤ 2 * K ^ 2 * (a / g ^ 2) := by
  have hK0 : 0 < K := by linarith
  have hgK : 0 < g / K := by positivity
  have hq0 : 0 < q := hgK.trans_le hq
  have h1 : a / q ^ 2 ≤ K ^ 2 * (a / g ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have hq2 : (g / K) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hgK.le hq 2
    have : K ^ 2 * (a / g ^ 2) * (g / K) ^ 2 = a := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ K ^ 2 * (a / g ^ 2))]
  have h2 : 1 ≤ K ^ 2 * (a / g ^ 2) := by
    have e : K ^ 2 * (a / g ^ 2) = K ^ 2 * a / g ^ 2 := by ring
    rw [e, one_le_div (by positivity)]
    linarith
  linarith

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
