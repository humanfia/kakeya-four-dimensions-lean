import Submission.Obl.k4_finite_positive_mixed_cover_realization.Path

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization

open MeasureTheory

/-- The finite candidate cover, keeping the supplied original assignments. -/
structure CoverData {W : ℕ} (p : PathData W) where
  level : ℕ
  gain : ℝ
  n : ℕ
  old : Fin n → Fin p.C
  test : Fin n → MvPolynomial (Fin 4) ℝ
  normal : Fin n → Fin 2 → ℝ
  bias : Fin n → ℝ
  assigned : Fin n → Set Trajectory
  counted : Fin n → Set Incidence
  time : Bool

/-- The cover's exact frozen certificate. -/
def CoverData.Valid {W : ℕ} {p : PathData W} (c : CoverData p)
    (Nk L : ℝ) (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain : ℝ) (m Mg Dg : ℕ) (ε : ℝ) : Prop :=
  c.level < m ∧ gain ≤ c.gain ∧ c.gain ≤ 1 / 8 ∧
  (∃ e : ℕ, c.gain = gain * (1 + ρ) ^ e) ∧
  p.r c.level + 2 * c.gain * L ≤ L ∧ (c.n : ℝ) ≤ Nk ^ Mg ∧
  (∀ b, p.lev (c.old b) = c.level ∧ 0 < ν (p.world (c.old b)) (p.assigned (c.old b)) ∧
    MeasurableSet (c.assigned b) ∧ c.assigned b ⊆ p.assigned (c.old b) ∧
    (∀ q, fmt 6 (Nk ^ Mg) Dg {w | (q, w) ∈ c.assigned b}) ∧
    MeasurableSet (c.counted b) ∧
    c.counted b ⊆ {z | z ∈ TerminalInc W p.C m p.lev p.world p.counted (p.world (c.old b)) ∧
      z.1 ∈ c.assigned b ∧ z.2 ∈ Set.Icc
        ((p.bin (c.old b) : ℝ) / (2 : ℝ) ^ p.T c.level)
        (((p.bin (c.old b) : ℝ) + 1) / (2 : ℝ) ^ p.T c.level)} ∧
    (if c.time then
      (c.test b).totalDegree ≤ 2 ∧ (∀ e, |(c.test b).coeff e| ≤ Nk ^ Mg) ∧
      (∀ l ∈ c.assigned b, Fits (Nk ^ (4 * ρ * c.gain * L + 4 * ε))
        (δ Nk (p.r c.level + c.gain * L)) (B (p.world (c.old b))) (c.test b) l
        (Set.Icc ((p.bin (c.old b) : ℝ) / (2 : ℝ) ^ p.T c.level)
          (((p.bin (c.old b) : ℝ) + 1) / (2 : ℝ) ^ p.T c.level))) ∧
      (∀ z ∈ c.counted b, B (p.world (c.old b)) / Nk ^ (4 * ρ * c.gain * L + 4 * ε) ≤
        |MvPolynomial.eval (x z.1 z.2) (MvPolynomial.pderiv (3 : Fin 4) (c.test b))|) ∧
      ENNReal.ofReal (Nk ^ (-((d₁ + 4 * ρ) * c.gain * L) - 4 * ε) /
        (2 : ℝ) ^ p.T c.level) * ν (p.world (c.old b)) (p.assigned (c.old b)) ≤
          ((ν (p.world (c.old b))).prod volume) (c.counted b)
    else
      (∑ e, (c.normal b e) ^ 2) = 1 ∧ |c.bias b| ≤ Nk ^ Mg ∧
      (∀ l ∈ c.assigned b, InStrip (p.T c.level) (p.velocity (c.old b))
        (p.frame (c.old b)) (c.normal b) (c.bias b)
        (Nk ^ (4 * ρ * c.gain * L + 4 * ε) * Nk ^ (-c.gain * L)) l) ∧
      ENNReal.ofReal (Nk ^ (-4 * ρ * c.gain * L - 4 * ε) /
        (2 : ℝ) ^ p.T c.level) * ν (p.world (c.old b)) (p.assigned (c.old b)) ≤
          ((ν (p.world (c.old b))).prod volume) (c.counted b))) ∧
  (∀ b b', b ≠ b' → c.old b = c.old b' → Disjoint (c.assigned b) (c.assigned b')) ∧
  (∀ b : Fin p.C, ((Finset.univ.filter (fun b' => c.old b' = b)).card : ℝ) ≤
    Nk ^ ((if c.time then (d₁ + 4 * ρ) else 4 * ρ) * c.gain * L + 4 * ε)) ∧
  (∀ b b', b ≠ b' → p.world (c.old b) = p.world (c.old b') →
    Disjoint (c.counted b) (c.counted b')) ∧
  ENNReal.ofReal (Nk ^ (-ε)) ≤ ∑ b, ENNReal.ofReal (ω (p.world (c.old b))) *
    ((ν (p.world (c.old b))).prod volume) (c.counted b)

lemma mixedCover_iff_data {W : ℕ} (p : PathData W) (Nk L : ℝ)
    (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (d₁ ρ gain : ℝ) (m Mg Dg : ℕ) (ε : ℝ) :
    MixedCover Nk L W ω ν B d₁ ρ gain m p.r p.T p.C p.lev p.world p.bin
      p.velocity p.frame p.assigned p.counted Mg Dg ε ↔
      ∃ c : CoverData p, c.Valid Nk L ω ν B d₁ ρ gain m Mg Dg ε := by
  constructor
  · rintro ⟨i, h, n, old, R, a, z, A, V, time, hv⟩
    exact ⟨⟨i, h, n, old, R, a, z, A, V, time⟩, hv⟩
  · rintro ⟨c, hc⟩
    exact ⟨c.level, c.gain, c.n, c.old, c.test, c.normal, c.bias,
      c.assigned, c.counted, c.time, hc⟩

end Submission.Obl.k4_finite_positive_mixed_cover_realization
