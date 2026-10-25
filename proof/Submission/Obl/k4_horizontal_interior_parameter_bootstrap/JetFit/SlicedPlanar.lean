import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedCount

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced fit: the planar step

`sliced_nearLine`: the occupied-cell representatives give collision triples
`(a(u), b(v), b(v'))` in the unit square whose dot products lie near the rescaled starting
scalars, a `d`-dimensional set; the planar input (`nearLine_of_dot_count`) then places the
time graph `τ ↦ λ s₂ (φ u₀ - φ u)` near a line.
-/

open MeasureTheory Set Metric

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

theorem sq_sign {s : ℝ} (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with h | h <;> subst h <;> norm_num

theorem abs_sign {s : ℝ} (hs : s = 1 ∨ s = -1) : |s| = 1 := by
  rcases hs with h | h <;> subst h <;> norm_num

/-- `aPt` as a point of the time graph. -/
theorem aPt_eq_graph (D : SlicedData Ω) {u₀ s₁ s₂ lam : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hlam : lam ≠ 0) (u : ℝ) :
    aPt D u₀ s₁ s₂ lam u = pt (lam * s₁ * (u - u₀))
      (lam * s₂ * (D.φ u₀ - D.φ (u₀ + s₁ * (lam * s₁ * (u - u₀)) / lam))) := by
  have : u₀ + s₁ * (lam * s₁ * (u - u₀)) / lam = u := by
    rcases hs₁ with h | h <;> subst h <;> field_simp <;> ring
  rw [this]; rfl

/-- `bPt` as a point of the slope graph. -/
theorem bPt_eq_graph (D : SlicedData Ω) {s₁ s₂ lam : ℝ} (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hlam : lam ≠ 0) (v : ℝ) :
    bPt D s₁ s₂ lam v = pt (lam * s₁ * D.G (s₂ * ((lam * s₂ * v + 1 / 2) - 1 / 2) / lam) + 1 / 2)
      (lam * s₂ * v + 1 / 2) := by
  have : s₂ * ((lam * s₂ * v + 1 / 2) - 1 / 2) / lam = v := by
    rcases hs₂ with h | h <;> subst h <;> field_simp <;> ring
  rw [this]; rfl

/-- Points in a common small product ball come from neighbouring cells. -/
theorem floor_close {x y p : ℝ} (hp : 0 < p) (h : |x - y| ≤ p) : |⌊x / p⌋ - ⌊y / p⌋| ≤ 1 := by
  have h' : |x / p - y / p| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hp, div_le_one hp]; exact h
  have := floor_mem_Icc_of_abs_le h'
  rw [Finset.mem_Icc] at this
  simp only [Nat.ceil_one, Nat.cast_one] at this
  rw [abs_le]; constructor <;> linarith [this.1, this.2]

theorem dist_le_of_prod {a a' : E2} {b b' c c' : E2} {r : ℝ}
    (h : dist ((a, b, c) : E2 × E2 × E2) (a', b', c') ≤ r) :
    dist a a' ≤ r ∧ dist b b' ≤ r ∧ dist c c' ≤ r := by
  rw [Prod.dist_eq, Prod.dist_eq] at h
  simp only at h
  exact ⟨(le_max_left _ _).trans h, ((le_max_left _ _).trans (le_max_right _ _)).trans h,
    ((le_max_right _ _).trans (le_max_right _ _)).trans h⟩

set_option maxHeartbeats 2000000 in
/-- **The planar step of the sliced fit**: the time graph of the pruned collisions lies near a
line in the sense of the planar input. -/
theorem sliced_nearLine {ε d : ℝ} (hε : 0 < ε) (hd : 0 ≤ d) (hεd : ε + d < 1) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ (p K : ℝ), 0 < p → p ≤ 1 → 1 ≤ K → p / (8 * K) ≤ δ₀ →
      5 * (8 * K + 5) ≤ (p / (8 * K)) ^ (-η) →
      3 * (4 * K) ^ 2 * (4 * K + 2) < (p / (8 * K)) ^ (-η * (1 - ε - d)) →
      27 * 179712 * K ^ 16 * p ^ 3 * (p / (8 * K)) ^ (η - 3) ≤ 1 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (D : SlicedData Ω), SlicedHyp D p K d →
      ∀ (u₀ s₁ s₂ : ℝ) (β₀ : ℤ) (K₁ : ℝ) (Occ : Finset (ℤ × ℤ × ℤ))
        (xpt : ℤ × ℤ × ℤ → (Ω × Ω) × ℝ),
      u₀ ∈ Icc (0:ℝ) 1 → (s₁ = 1 ∨ s₁ = -1) → (s₂ = 1 ∨ s₂ = -1) →
      1 ≤ 179712 * K ^ 16 * p ^ 3 * Occ.card →
      (∀ c ∈ Occ, xpt c ∈ Sstar D p u₀ K₁ s₁ s₂ β₀ ∩ cellSet D p c.1 c.2.1 c.2.2) →
      NearLine {a | ∃ τ ∈ {τ : ℝ | ∃ c ∈ Occ, τ = 1 / (4 * K) * s₁ * ((xpt c).2 - u₀)},
        a = pt τ (1 / (4 * K) * s₂ * (D.φ u₀ - D.φ (u₀ + s₁ * τ / (1 / (4 * K)))))} (p / (8 * K)) ε := by
  obtain ⟨η, δ₀, hη, hδ₀, hNL⟩ := nearLine_of_dot_count hε hd hεd
  refine ⟨η, δ₀, hη, hδ₀, ?_⟩
  intro p K hp hp1 hK hδδ₀ hA hB hDc Ω _ D H u₀ s₁ s₂ β₀ K₁ Occ xpt hu₀ hs₁ hs₂ hOcc hxpt
  have hK0 : 0 < K := by linarith
  set lam : ℝ := 1 / (4 * K) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamne : lam ≠ 0 := hlam0.ne'
  set δ : ℝ := p / (8 * K) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδlam : 2 * δ = lam * p := by rw [hδ, hlam]; field_simp; ring
  set g : ℝ → ℝ := fun τ => lam * s₂ * (D.φ u₀ - D.φ (u₀ + s₁ * τ / lam)) with hg
  set Tτ : Set ℝ := {τ : ℝ | ∃ c ∈ Occ, τ = lam * s₁ * ((xpt c).2 - u₀)} with hTτ
  set A : Set E2 := {a | ∃ τ ∈ Tτ, a = pt τ (g τ)} with hAdef
  set ψ : ℝ → ℝ := fun y => lam * s₁ * D.G (s₂ * (y - 1 / 2) / lam) + 1 / 2 with hψ
  set Ty : Set ℝ := {y | ∃ v : ℝ, |v| ≤ K ∧ y = lam * s₂ * v + 1 / 2} with hTy
  set B : Set E2 := {b | ∃ y ∈ Ty, b = pt (ψ y) y} with hBdef
  set trip : ℤ × ℤ × ℤ → E2 × E2 × E2 := fun c =>
    (aPt D u₀ s₁ s₂ lam (xpt c).2, bPt D s₁ s₂ lam (D.v (xpt c).1.1),
      bPt D s₁ s₂ lam (D.v (xpt c).1.2)) with htrip
  -- basic facts about the representatives
  have hxE : ∀ c ∈ Occ, ((xpt c).1.1, (xpt c).2) ∈ D.E ∧ ((xpt c).1.1, u₀) ∈ D.E ∧
      ((xpt c).1.2, (xpt c).2) ∈ D.E ∧ ((xpt c).1.2, u₀) ∈ D.E ∧
      ⌊D.L (xpt c).1.1 (xpt c).2 / p⌋ = ⌊D.L (xpt c).1.2 (xpt c).2 / p⌋ ∧
      ⌊D.L (xpt c).1.1 u₀ / p⌋ = β₀ ∧ 0 ≤ s₁ * ((xpt c).2 - u₀) ∧
      0 ≤ s₂ * (D.φ u₀ - D.φ (xpt c).2) ∧ ⌊(xpt c).2 / p⌋ = c.1 ∧
      ⌊D.v (xpt c).1.1 / p⌋ = c.2.1 ∧ ⌊D.v (xpt c).1.2 / p⌋ = c.2.2 := by
    intro c hc
    have hx := hxpt c hc
    have hS := hx.1
    have hcell := hx.2
    have hScol := hS.1.1
    have hquad := hS.2
    exact ⟨hScol.1.1.1, hScol.1.1.2, hScol.1.2.1.1, hScol.1.2.1.2, hScol.1.2.2, hScol.2,
      hquad.1, hquad.2, hcell.1, hcell.2.1, hcell.2.2⟩
  have hu01 : ∀ c ∈ Occ, (xpt c).2 ∈ Icc (0:ℝ) 1 := fun c hc => H.E01 _ (hxE c hc).1
  have hg_eq : ∀ c ∈ Occ, g (lam * s₁ * ((xpt c).2 - u₀)) = lam * s₂ * (D.φ u₀ - D.φ (xpt c).2) := by
    intro c hc
    have := aPt_eq_graph D (u₀ := u₀) (s₂ := s₂) hs₁ hlamne (xpt c).2
    simp only [aPt] at this
    have h2 := congrArg (fun z : E2 => z 1) this
    simp only [pt_one] at h2
    exact h2.symm
  -- the time graph is slack-Lipschitz
  have hgLip : ∀ τ ∈ Tτ, ∀ τ' ∈ Tτ, |g τ - g τ'| ≤ 2 * K * (|τ - τ'| + δ) := by
    rintro τ ⟨c, hc, rfl⟩ τ' ⟨c', hc', rfl⟩
    rw [hg_eq c hc, hg_eq c' hc']
    have e1 : lam * s₂ * (D.φ u₀ - D.φ (xpt c).2) - lam * s₂ * (D.φ u₀ - D.φ (xpt c').2) =
        lam * s₂ * (D.φ (xpt c').2 - D.φ (xpt c).2) := by ring
    have e2 : lam * s₁ * ((xpt c).2 - u₀) - lam * s₁ * ((xpt c').2 - u₀) =
        lam * s₁ * ((xpt c).2 - (xpt c').2) := by ring
    rw [e1, e2, abs_mul, abs_mul, abs_mul, abs_mul, abs_sign hs₁, abs_sign hs₂,
      abs_of_pos hlam0]
    simp only [mul_one]
    have hφ := H.φlip _ (hu01 c' hc') _ (hu01 c hc)
    rw [abs_sub_comm (xpt c').2] at hφ
    calc lam * |D.φ (xpt c').2 - D.φ (xpt c).2|
        ≤ lam * (K * (|(xpt c).2 - (xpt c').2| + p)) := mul_le_mul_of_nonneg_left hφ hlam0.le
      _ = K * (lam * |(xpt c).2 - (xpt c').2|) + K * (lam * p) := by ring
      _ = K * (lam * |(xpt c).2 - (xpt c').2|) + K * (2 * δ) := by rw [hδlam]
      _ ≤ 2 * K * (lam * |(xpt c).2 - (xpt c').2| + δ) := by
          have : 0 ≤ K * (lam * |(xpt c).2 - (xpt c').2|) := by positivity
          nlinarith
  -- the slope graph is Lipschitz
  have hψLip : ∀ y ∈ Ty, ∀ y' ∈ Ty, |ψ y - ψ y'| ≤ K * (|y - y'| + δ) := by
    rintro y ⟨v, hv, rfl⟩ y' ⟨v', hv', rfl⟩
    have hψv : ∀ w : ℝ, ψ (lam * s₂ * w + 1 / 2) = lam * s₁ * D.G w + 1 / 2 := by
      intro w
      have := bPt_eq_graph D (s₁ := s₁) hs₂ hlamne w
      have h0 := congrArg (fun z : E2 => z 0) this
      simp only [bPt, pt_zero] at h0
      simp only [hψ]; linarith
    rw [hψv, hψv]
    have e1 : lam * s₁ * D.G v + 1 / 2 - (lam * s₁ * D.G v' + 1 / 2) = lam * s₁ * (D.G v - D.G v') := by
      ring
    have e2 : lam * s₂ * v + 1 / 2 - (lam * s₂ * v' + 1 / 2) = lam * s₂ * (v - v') := by ring
    rw [e1, e2, abs_mul, abs_mul, abs_mul, abs_mul, abs_sign hs₁, abs_sign hs₂, abs_of_pos hlam0]
    simp only [mul_one]
    have hG := H.Glip v v'
    calc lam * |D.G v - D.G v'| ≤ lam * (K * |v - v'|) := mul_le_mul_of_nonneg_left hG hlam0.le
      _ = K * (lam * |v - v'|) := by ring
      _ ≤ K * (lam * |v - v'| + δ) := by nlinarith
  -- membership of the triples
  have haA : ∀ c ∈ Occ, aPt D u₀ s₁ s₂ lam (xpt c).2 ∈ A := by
    intro c hc
    refine ⟨lam * s₁ * ((xpt c).2 - u₀), ⟨c, hc, rfl⟩, ?_⟩
    rw [aPt_eq_graph D hs₁ hlamne]
  have hbB : ∀ v, |v| ≤ K → bPt D s₁ s₂ lam v ∈ B := by
    intro v hv
    exact ⟨lam * s₂ * v + 1 / 2, ⟨v, hv, rfl⟩, bPt_eq_graph D hs₂ hlamne v⟩
  -- the set of starting scalars, rescaled
  set S0 : Set ℝ := {x | ∃ l, (l, u₀) ∈ D.E ∧ x = D.L l u₀} with hS0
  set Sset : Set ℝ := {y | ∃ σ ∈ S0, y = lam ^ 2 * (σ - (β₀ : ℝ) * p)} with hSset
  refine hNL δ hδ0 hδδ₀ (4 * K) (by linarith) hB A B ?_ ?_ ?_ ?_ (trip '' Occ) ?_ ?_ Sset
    (lam ^ 2 * ((4 * K + 1) * p + p)) ?_ ?_ ?_
  · -- `A` in the unit square
    rintro a ⟨τ, ⟨c, hc, rfl⟩, rfl⟩
    rw [← aPt_eq_graph D hs₁ hlamne]
    have h := hxE c hc
    exact aPt_mem_unit H hK hs₁ hs₂ hu₀ (hu01 c hc) h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
  · -- `B` in the unit square
    rintro b ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    rw [← bPt_eq_graph D hs₂ hlamne]
    exact bPt_mem_unit H hK hs₁ hs₂ hv
  · -- regularity of `A`
    intro x ρ r hδρ hρr
    have hρ : 0 < ρ := hδ0.trans_le hδρ
    obtain ⟨m, ⟨cc, hcc⟩, hm⟩ := graph_coveredBy (T := Tτ) (ψ := g) (K := 2 * K) (s₀ := δ)
      (by linarith) hgLip hρ hδρ hρr x
    refine ⟨m, cc, hcc, hm.trans ?_⟩
    have hr1 : 1 ≤ r / ρ := by rw [le_div_iff₀ hρ]; linarith
    calc (4 * (2 * K) + 5) * (4 * r / ρ + 1) ≤ (8 * K + 5) * (5 * (r / ρ)) := by
          have : 4 * r / ρ = 4 * (r / ρ) := by ring
          rw [this]; nlinarith
      _ = 5 * (8 * K + 5) * (r / ρ) := by ring
      _ ≤ δ ^ (-η) * (r / ρ) := by gcongr
  · -- regularity of `B`
    intro x ρ r hδρ hρr
    have hρ : 0 < ρ := hδ0.trans_le hδρ
    obtain ⟨m, ⟨cc, hcc⟩, hm⟩ := graph2_coveredBy (T := Ty) (ψ := ψ) (K := K) (s₀ := δ)
      (by linarith) hψLip hρ hδρ hρr x
    refine ⟨m, cc, hcc, hm.trans ?_⟩
    have hr1 : 1 ≤ r / ρ := by rw [le_div_iff₀ hρ]; linarith
    calc (4 * K + 5) * (4 * r / ρ + 1) ≤ (8 * K + 5) * (5 * (r / ρ)) := by
          have : 4 * r / ρ = 4 * (r / ρ) := by ring
          rw [this]; nlinarith
      _ = 5 * (8 * K + 5) * (r / ρ) := by ring
      _ ≤ δ ^ (-η) * (r / ρ) := by gcongr
  · -- triples in `A × B × B`
    rintro t ⟨c, hc, rfl⟩
    exact ⟨haA c hc, hbB _ (H.vbound _), hbB _ (H.vbound _)⟩
  · -- covering lower bound
    intro m cc hcov
    -- coordinates of the rescaled points
    have ha0 : ∀ u, aPt D u₀ s₁ s₂ lam u 0 = lam * s₁ * (u - u₀) := fun u => by simp [aPt]
    have hb1 : ∀ v, bPt D s₁ s₂ lam v 1 = lam * s₂ * v + 1 / 2 := fun v => by simp [bPt]
    have hsepu : ∀ u u' : ℝ, |aPt D u₀ s₁ s₂ lam u 0 - aPt D u₀ s₁ s₂ lam u' 0| ≤ 2 * δ →
        |u - u'| ≤ p := by
      intro u u' h
      rw [ha0, ha0, hδlam] at h
      have : lam * s₁ * (u - u₀) - lam * s₁ * (u' - u₀) = lam * s₁ * (u - u') := by ring
      rw [this, abs_mul, abs_mul, abs_sign hs₁, mul_one, abs_of_pos hlam0] at h
      exact le_of_mul_le_mul_left h hlam0
    have hsepv : ∀ v v' : ℝ, |bPt D s₁ s₂ lam v 1 - bPt D s₁ s₂ lam v' 1| ≤ 2 * δ →
        |v - v'| ≤ p := by
      intro v v' h
      rw [hb1, hb1, hδlam] at h
      have : lam * s₂ * v + 1 / 2 - (lam * s₂ * v' + 1 / 2) = lam * s₂ * (v - v') := by ring
      rw [this, abs_mul, abs_mul, abs_sign hs₂, mul_one, abs_of_pos hlam0] at h
      exact le_of_mul_le_mul_left h hlam0
    have hsep : ∀ c ∈ Occ, ∀ c' ∈ Occ, dist (trip c) (trip c') ≤ 2 * δ →
        |c.1 - c'.1| ≤ 1 ∧ |c.2.1 - c'.2.1| ≤ 1 ∧ |c.2.2 - c'.2.2| ≤ 1 := by
      intro c hc c' hc' hd
      obtain ⟨d1, d2, d3⟩ := dist_le_of_prod hd
      have hc1 := hxE c hc
      have hc1' := hxE c' hc'
      have e1 := hsepu _ _ ((abs_sub_le_dist_E2_zero _ _).trans d1)
      have e2 := hsepv _ _ ((abs_sub_le_dist_E2_one _ _).trans d2)
      have e3 := hsepv _ _ ((abs_sub_le_dist_E2_one _ _).trans d3)
      refine ⟨?_, ?_, ?_⟩
      · rw [← hc1.2.2.2.2.2.2.2.2.1, ← hc1'.2.2.2.2.2.2.2.2.1]; exact floor_close hp e1
      · rw [← hc1.2.2.2.2.2.2.2.2.2.1, ← hc1'.2.2.2.2.2.2.2.2.2.1]; exact floor_close hp e2
      · rw [← hc1.2.2.2.2.2.2.2.2.2.2, ← hc1'.2.2.2.2.2.2.2.2.2.2]; exact floor_close hp e3
    have hinj : Set.InjOn trip Occ := by
      intro c hc c' hc' heq
      have hc1 := hxE c hc
      have hc1' := hxE c' hc'
      have hd : dist (trip c) (trip c') = 0 := by rw [heq, dist_self]
      have hz : dist (trip c) (trip c') ≤ 0 := hd.le
      obtain ⟨d1, d2, d3⟩ := dist_le_of_prod hz
      have u_eq : (xpt c).2 = (xpt c').2 := by
        have h := (abs_sub_le_dist_E2_zero _ _).trans d1
        rw [ha0, ha0] at h
        have : lam * s₁ * ((xpt c).2 - u₀) - lam * s₁ * ((xpt c').2 - u₀) =
            lam * s₁ * ((xpt c).2 - (xpt c').2) := by ring
        rw [this, abs_mul, abs_mul, abs_sign hs₁, mul_one, abs_of_pos hlam0] at h
        have : |(xpt c).2 - (xpt c').2| ≤ 0 := by
          by_contra hneg; push Not at hneg; nlinarith
        linarith [abs_nonneg ((xpt c).2 - (xpt c').2), abs_eq_zero.1 (le_antisymm this
          (abs_nonneg _)), sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm this (abs_nonneg _)))]
      have v_eq : ∀ v v' : ℝ, dist (bPt D s₁ s₂ lam v) (bPt D s₁ s₂ lam v') ≤ 0 → v = v' := by
        intro v v' h
        have h' := (abs_sub_le_dist_E2_one _ _).trans h
        rw [hb1, hb1] at h'
        have : lam * s₂ * v + 1 / 2 - (lam * s₂ * v' + 1 / 2) = lam * s₂ * (v - v') := by ring
        rw [this, abs_mul, abs_mul, abs_sign hs₂, mul_one, abs_of_pos hlam0] at h'
        have : |v - v'| ≤ 0 := by by_contra hneg; push Not at hneg; nlinarith
        exact sub_eq_zero.1 (abs_eq_zero.1 (le_antisymm this (abs_nonneg _)))
      have v1 := v_eq _ _ d2
      have v2 := v_eq _ _ d3
      have k1 : c.1 = c'.1 := by rw [← hc1.2.2.2.2.2.2.2.2.1, ← hc1'.2.2.2.2.2.2.2.2.1, u_eq]
      have k2 : c.2.1 = c'.2.1 := by
        rw [← hc1.2.2.2.2.2.2.2.2.2.1, ← hc1'.2.2.2.2.2.2.2.2.2.1, v1]
      have k3 : c.2.2 = c'.2.2 := by
        rw [← hc1.2.2.2.2.2.2.2.2.2.2, ← hc1'.2.2.2.2.2.2.2.2.2.2, v2]
      exact Prod.ext k1 (Prod.ext k2 k3)
    have hcard := card_le_of_triples_cover Occ trip δ hsep hinj cc hcov
    have hcardR : (Occ.card : ℝ) ≤ (m : ℝ) * 27 := by exact_mod_cast hcard
    have hpos : 0 < 27 * 179712 * K ^ 16 * p ^ 3 := by positivity
    have h1 : 27 * 179712 * K ^ 16 * p ^ 3 * δ ^ (η - 3) ≤ 27 * 179712 * K ^ 16 * p ^ 3 * m := by
      calc 27 * 179712 * K ^ 16 * p ^ 3 * δ ^ (η - 3) ≤ 1 := hDc
        _ ≤ 179712 * K ^ 16 * p ^ 3 * Occ.card := hOcc
        _ ≤ 179712 * K ^ 16 * p ^ 3 * ((m : ℝ) * 27) := by
            apply mul_le_mul_of_nonneg_left hcardR; positivity
        _ = 27 * 179712 * K ^ 16 * p ^ 3 * m := by ring
    exact le_of_mul_le_mul_left h1 hpos
  · -- the dot-product error is at most `4K δ`
    have : lam ^ 2 * ((4 * K + 1) * p + p) = (4 * K + 2) / (16 * K ^ 2) * p := by
      rw [hlam]; field_simp; ring
    rw [this, hδ]
    have h1 : (4 * K + 2) / (16 * K ^ 2) ≤ 4 * K / (8 * K) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    calc (4 * K + 2) / (16 * K ^ 2) * p ≤ 4 * K / (8 * K) * p := by gcongr
      _ = 4 * K * (p / (8 * K)) := by ring
  · -- dot products near the rescaled starting scalars
    rintro t ⟨c, hc, rfl⟩
    have h := hxE c hc
    refine ⟨lam ^ 2 * (D.L (xpt c).1.2 u₀ - (β₀ : ℝ) * p), ⟨_, ⟨_, h.2.2.2.1, rfl⟩, rfl⟩, ?_⟩
    simp only [htrip]
    rw [inner_aPt_bPt D hs₁ hs₂]
    have hclose : |D.L (xpt c).1.1 (xpt c).2 - D.L (xpt c).1.2 (xpt c).2| ≤ p := by
      have := Int.abs_sub_lt_one_of_floor_eq_floor h.2.2.2.2.1
      rw [← sub_div, abs_div, abs_of_pos hp, div_lt_one hp] at this
      exact this.le
    have hdot := collision_dot H h.2.1 h.2.2.2.1 h.1 h.2.2.1 hclose
    have hb1 : (β₀ : ℝ) * p ≤ D.L (xpt c).1.1 u₀ := by
      have := Int.floor_le (D.L (xpt c).1.1 u₀ / p); rw [h.2.2.2.2.2.1, le_div_iff₀ hp] at this
      exact this
    have hb2 : D.L (xpt c).1.1 u₀ < (β₀ : ℝ) * p + p := by
      have := Int.lt_floor_add_one (D.L (xpt c).1.1 u₀ / p)
      rw [h.2.2.2.2.2.1, div_lt_iff₀ hp] at this; linarith
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    gcongr
    set X := ((xpt c).2 - u₀) * (D.G (D.v (xpt c).1.1) - D.G (D.v (xpt c).1.2)) -
      (D.φ (xpt c).2 - D.φ u₀) * (D.v (xpt c).1.1 - D.v (xpt c).1.2)
    have : X - (D.L (xpt c).1.2 u₀ - (β₀ : ℝ) * p) =
        (X - (D.L (xpt c).1.2 u₀ - D.L (xpt c).1.1 u₀)) - (D.L (xpt c).1.1 u₀ - (β₀ : ℝ) * p) := by
      ring
    rw [this]
    have hθ : |D.L (xpt c).1.1 u₀ - (β₀ : ℝ) * p| ≤ p := by
      rw [abs_le]; constructor <;> linarith
    calc |(X - (D.L (xpt c).1.2 u₀ - D.L (xpt c).1.1 u₀)) - (D.L (xpt c).1.1 u₀ - (β₀ : ℝ) * p)|
        ≤ |X - (D.L (xpt c).1.2 u₀ - D.L (xpt c).1.1 u₀)| + |D.L (xpt c).1.1 u₀ - (β₀ : ℝ) * p| :=
          abs_sub _ _
      _ ≤ (4 * K + 1) * p + p := add_le_add hdot hθ
  · -- local count of the rescaled starting scalars
    have hc := localCount_rescale (S := S0) (c := (β₀ : ℝ) * p) (by positivity : 0 < lam ^ 2)
      (show lam ^ 2 * p ≤ δ by
        rw [hlam, hδ]
        have : (1 / (4 * K)) ^ 2 * p = p / (16 * K ^ 2) := by field_simp; ring
        rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
        have h8 : 8 * K ≤ 16 * K ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h8 hp.le]) (H.count u₀)
    intro a L s' hs' hsL
    obtain ⟨m, cc, hcov, hm⟩ := hc a L s' hs' hsL
    refine ⟨m, cc, hcov, hm.trans ?_⟩
    have : 0 ≤ (L / s') ^ d := by
      apply Real.rpow_nonneg; apply div_nonneg <;> linarith
    nlinarith


end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
