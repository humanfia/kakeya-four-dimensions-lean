import Submission.Obl.k4_unbounded_width_exclusion.Interface

noncomputable section

namespace Submission.Obl.k4_unbounded_width_exclusion

abbrev Trajectory := ℕ × (Fin 6 → ℝ)
abbrev Incidence := Trajectory × ℝ
abbrev Observation := EuclideanSpace ℝ (Fin 3) × ℤ

/-- All the data of one exact problem, before its validity assumptions. -/
structure Problem where
  N : ℕ → ℝ
  K : ℕ → ℝ
  L : ℝ
  d : ℝ
  W : ℕ → ℕ
  ω : (k : ℕ) → Fin (W k) → ℝ
  ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure Trajectory
  E : (k : ℕ) → Fin (W k) → Set Incidence
  P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ
  B : (k : ℕ) → Fin (W k) → ℝ
  f : ℝ → ℝ
  g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal
  G : (k : ℕ) → Fin (W k) → ℝ → (Observation × (Fin 2 → ℤ)) → ENNReal

def Problem.Valid (p : Problem) (S η : ℝ) : Prop :=
  prob p.N p.K p.L p.d S η p.W p.ω p.ν p.E p.P p.B p.f p.g p.G

def Problem.Terminal (p : Problem) (h : ℝ) : Prop :=
  term p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h

def Problem.horizon (p : Problem) : ℝ :=
  H p.N p.K p.L p.W p.ω p.ν p.E p.B p.f

def Problem.Narrow (p : Problem) (h w : ℝ) : Prop :=
  nt p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h w

/-- The same length-one maximizing test used in the frozen conclusion. -/
def Near (ds kr S η t : ℝ) (p : Problem) : Prop :=
  p.L = 1 ∧ p.Valid S η ∧ p.d < ds + t ∧ kr - t < p.horizon

def BoundedWidth (ds kr S η : ℝ) : Prop :=
  ∃ a w : ℝ, 0 < a ∧ 0 ≤ w ∧ ∀ t : ℝ, 0 < t →
    ∃ p : Problem, Near ds kr S η t p ∧ ¬ p.Narrow (kr + a) w

theorem bw_iff_boundedWidth (ds kr S η : ℝ) :
    bw ds kr S η ↔ BoundedWidth ds kr S η := by
  constructor
  · rintro ⟨a, w, ha, hw, h⟩
    refine ⟨a, w, ha, hw, fun t ht => ?_⟩
    obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hh, hn⟩ := h t ht
    exact ⟨⟨N, K, 1, d, W, ω, ν, E, P, B, f, g, G⟩, ⟨rfl, hp, hd, hh⟩, hn⟩
  · rintro ⟨a, w, ha, hw, h⟩
    refine ⟨a, w, ha, hw, fun t ht => ?_⟩
    obtain ⟨p, hnear, hn⟩ := h t ht
    obtain ⟨hL, hp, hd, hh⟩ := hnear
    cases p with
    | mk N K L d W ω ν E P B f g G =>
      dsimp only [Problem.L] at hL
      subst L
      exact ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hh, hn⟩

theorem not_boundedWidth_iff (ds kr S η : ℝ) :
    ¬ BoundedWidth ds kr S η ↔
      ∀ a : ℝ, 0 < a → ∀ w : ℝ, 0 ≤ w →
        ∃ t : ℝ, 0 < t ∧ ∀ p : Problem,
          Near ds kr S η t p → p.Narrow (kr + a) w := by
  classical
  constructor
  · intro hn a ha w hw
    by_contra h
    push Not at h
    exact hn ⟨a, w, ha, hw, h⟩
  · intro h hb
    obtain ⟨a, w, ha, hw, hnear⟩ := hb
    obtain ⟨t, ht, hall⟩ := h a ha w hw
    obtain ⟨p, hp, hn⟩ := hnear t ht
    exact hn (hall p hp)

theorem Near.mono {ds kr S η t t' : ℝ} {p : Problem}
    (h : Near ds kr S η t p) (htt' : t ≤ t') : Near ds kr S η t' p := by
  obtain ⟨hL, hp, hd, hh⟩ := h
  exact ⟨hL, hp, hd.trans_le (by linarith), lt_of_le_of_lt (by linarith) hh⟩

theorem exists_near {ds kr S η : ℝ} (h : es ds kr S η)
    {t : ℝ} (ht : 0 < t) : ∃ p : Problem, Near ds kr S η t p := by
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hh⟩ := h.2.2.2.2.1 t ht
  exact ⟨⟨N, K, 1, d, W, ω, ν, E, P, B, f, g, G⟩, rfl, hp, hd, hh⟩

end Submission.Obl.k4_unbounded_width_exclusion
