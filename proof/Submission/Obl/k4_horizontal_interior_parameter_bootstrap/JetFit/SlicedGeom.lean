import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedOccupied

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced fit: the planar configuration

* `aPt`, `bPt`: the rescaled points `a(u)` and `b(v)` of the collision triples, in the unit square
  after the quadrant restriction ("Reflect both planar sets by the same coordinate reflection,
  dilate each ... and translate only the second set");
* `inner_aPt_bPt`: their dot products are `λ²` times the collision dot product;
* `localCount_rescale`: the local `d`-count of the starting scalars passes to the dot products;
* `card_le_of_triples_cover`: triples from distinct cells need many balls to cover;
* `graph2_coveredBy`: regularity of the slope graph (over the second coordinate).
-/

open MeasureTheory Set Metric

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The rescaled time point `a(u) = λ (s₁(u - u₀), s₂(φ u₀ - φ u))`. -/
def aPt (D : SlicedData Ω) (u₀ s₁ s₂ lam u : ℝ) : E2 :=
  pt (lam * s₁ * (u - u₀)) (lam * s₂ * (D.φ u₀ - D.φ u))

/-- The rescaled slope point `b(v) = (λ s₁ G v + 1/2, λ s₂ v + 1/2)`. -/
def bPt (D : SlicedData Ω) (s₁ s₂ lam v : ℝ) : E2 :=
  pt (lam * s₁ * D.G v + 1 / 2) (lam * s₂ * v + 1 / 2)

theorem inner_aPt_bPt (D : SlicedData Ω) {u₀ s₁ s₂ lam : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1)
    (hs₂ : s₂ = 1 ∨ s₂ = -1) (u v v' : ℝ) :
    inner ℝ (aPt D u₀ s₁ s₂ lam u) (bPt D s₁ s₂ lam v - bPt D s₁ s₂ lam v') =
      lam ^ 2 * ((u - u₀) * (D.G v - D.G v') - (D.φ u - D.φ u₀) * (v - v')) := by
  have h1 : s₁ ^ 2 = 1 := by rcases hs₁ with h | h <;> simp [h]
  have h2 : s₂ ^ 2 = 1 := by rcases hs₂ with h | h <;> simp [h]
  have : bPt D s₁ s₂ lam v - bPt D s₁ s₂ lam v' =
      pt (lam * s₁ * (D.G v - D.G v')) (lam * s₂ * (v - v')) := by
    ext i; fin_cases i <;> simp [bPt, pt] <;> ring
  rw [this, aPt, inner_pt]
  simp only [pt_zero, pt_one]
  linear_combination (lam ^ 2 * ((u - u₀) * (D.G v - D.G v'))) * h1 +
    (lam ^ 2 * ((D.φ u₀ - D.φ u) * (v - v'))) * h2

theorem aPt_mem_unit {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hK : 1 ≤ K)
    {u₀ s₁ s₂ u : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hu₀ : u₀ ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) (hq1 : 0 ≤ s₁ * (u - u₀))
    (hq2 : 0 ≤ s₂ * (D.φ u₀ - D.φ u)) :
    ∀ i : Fin 2, 0 ≤ aPt D u₀ s₁ s₂ (1 / (4 * K)) u i ∧ aPt D u₀ s₁ s₂ (1 / (4 * K)) u i ≤ 1 := by
  have hK0 : 0 < K := by linarith
  have hlam : 0 < 1 / (4 * K) := by positivity
  have hlam1 : 1 / (4 * K) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hb1 : s₁ * (u - u₀) ≤ 1 := by
    rcases hs₁ with h | h <;> subst h <;> linarith [hu.1, hu.2, hu₀.1, hu₀.2]
  have hb2 : s₂ * (D.φ u₀ - D.φ u) ≤ 2 * K := by
    have a := H.φbound _ hu₀
    have b := H.φbound _ hu
    rcases hs₂ with h | h <;> subst h <;> linarith [(abs_le.1 a).1, (abs_le.1 a).2,
      (abs_le.1 b).1, (abs_le.1 b).2]
  intro i
  fin_cases i
  · simp only [aPt, Fin.zero_eta, pt_zero]
    constructor
    · rw [mul_assoc]; positivity
    · calc 1 / (4 * K) * s₁ * (u - u₀) = 1 / (4 * K) * (s₁ * (u - u₀)) := by ring
        _ ≤ 1 / 4 * 1 := mul_le_mul hlam1 hb1 hq1 (by norm_num)
        _ ≤ 1 := by norm_num
  · simp only [aPt, Fin.mk_one, pt_one]
    constructor
    · rw [mul_assoc]; positivity
    · calc 1 / (4 * K) * s₂ * (D.φ u₀ - D.φ u) = 1 / (4 * K) * (s₂ * (D.φ u₀ - D.φ u)) := by ring
        _ ≤ 1 / (4 * K) * (2 * K) := mul_le_mul_of_nonneg_left hb2 hlam.le
        _ = 1 / 2 := by field_simp; ring
        _ ≤ 1 := by norm_num

theorem bPt_mem_unit {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hK : 1 ≤ K)
    {s₁ s₂ v : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) (hv : |v| ≤ K) :
    ∀ i : Fin 2, 0 ≤ bPt D s₁ s₂ (1 / (4 * K)) v i ∧ bPt D s₁ s₂ (1 / (4 * K)) v i ≤ 1 := by
  have hK0 : 0 < K := by linarith
  have hG := H.Gbound v hv
  have e1 : |1 / (4 * K) * s₁ * D.G v| ≤ 1 / 4 := by
    have : |s₁| = 1 := by rcases hs₁ with h | h <;> simp [h]
    rw [abs_mul, abs_mul, this, mul_one, abs_of_pos (by positivity : (0:ℝ) < 1 / (4 * K))]
    calc 1 / (4 * K) * |D.G v| ≤ 1 / (4 * K) * K := by gcongr
      _ = 1 / 4 := by field_simp
  have e2 : |1 / (4 * K) * s₂ * v| ≤ 1 / 4 := by
    have : |s₂| = 1 := by rcases hs₂ with h | h <;> simp [h]
    rw [abs_mul, abs_mul, this, mul_one, abs_of_pos (by positivity : (0:ℝ) < 1 / (4 * K))]
    calc 1 / (4 * K) * |v| ≤ 1 / (4 * K) * K := by gcongr
      _ = 1 / 4 := by field_simp
  intro i
  fin_cases i
  · simp only [bPt, Fin.zero_eta, pt_zero]
    constructor <;> linarith [(abs_le.1 e1).1, (abs_le.1 e1).2]
  · simp only [bPt, Fin.mk_one, pt_one]
    constructor <;> linarith [(abs_le.1 e2).1, (abs_le.1 e2).2]

/-- Local counts survive an affine rescaling `σ ↦ μ (σ - c)`, `μ > 0`, once `μ p ≤ δ`. -/
theorem localCount_rescale {S : Set ℝ} {p K d μ c δ : ℝ} (hμ : 0 < μ) (hδ : μ * p ≤ δ)
    (hS : LocalCount S p K d) : LocalCount {y | ∃ σ ∈ S, y = μ * (σ - c)} δ K d := by
  intro a L s hs hsL
  obtain ⟨m, cc, hcov, hm⟩ := hS (a / μ + c) (L / μ) (s / μ)
    (by rw [le_div_iff₀ hμ]; linarith) (div_le_div_of_nonneg_right hsL hμ.le)
  refine ⟨m, fun j => μ * (cc j - c), ?_, ?_⟩
  · rintro y ⟨⟨σ, hσ, rfl⟩, hy⟩
    rw [mem_Icc] at hy
    have hσI : σ ∈ S ∩ Icc (a / μ + c) (a / μ + c + L / μ) := by
      refine ⟨hσ, ?_, ?_⟩
      · rw [div_add' _ _ _ hμ.ne', div_le_iff₀ hμ]; nlinarith
      · have : a / μ + c + L / μ = (a + μ * c + L) / μ := by field_simp
        rw [this, le_div_iff₀ hμ]; nlinarith
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hcov hσI)
    refine mem_iUnion.2 ⟨j, ?_⟩
    rw [mem_closedBall, Real.dist_eq] at hj ⊢
    have : μ * (σ - c) - μ * (cc j - c) = μ * (σ - cc j) := by ring
    rw [this, abs_mul, abs_of_pos hμ]
    calc μ * |σ - cc j| ≤ μ * (s / μ) := mul_le_mul_of_nonneg_left hj hμ.le
      _ = s := by field_simp
  · calc (m : ℝ) ≤ K * (L / μ / (s / μ)) ^ d := hm
      _ = K * (L / s) ^ d := by congr 2; field_simp

/-- Covering lower bound for a finite family of triples indexed by cells, when two triples in a
common closed `δ`-ball come from neighbouring cells. -/
theorem card_le_of_triples_cover (Occ : Finset (ℤ × ℤ × ℤ)) (trip : ℤ × ℤ × ℤ → E2 × E2 × E2)
    (δ : ℝ) (hsep : ∀ c ∈ Occ, ∀ c' ∈ Occ, dist (trip c) (trip c') ≤ 2 * δ →
      |c.1 - c'.1| ≤ 1 ∧ |c.2.1 - c'.2.1| ≤ 1 ∧ |c.2.2 - c'.2.2| ≤ 1)
    (hinj : Set.InjOn trip Occ) {m : ℕ} (cc : Fin m → E2 × E2 × E2)
    (hcov : (trip '' Occ) ⊆ ⋃ j, closedBall (cc j) δ) : Occ.card ≤ m * 27 := by
  classical
  have hcard : (Occ.image trip).card = Occ.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  refine card_le_of_coveredBy (S := trip '' Occ) (Occ.image trip)
    (fun x hx => by simpa using hx) ?_ cc hcov
  intro z
  by_cases hne : ((Occ.image trip).filter (fun x => x ∈ closedBall z δ)).Nonempty
  · obtain ⟨t₀, ht₀⟩ := hne
    obtain ⟨ht₀P, ht₀z⟩ := Finset.mem_filter.1 ht₀
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.1 ht₀P
    set box : Finset (ℤ × ℤ × ℤ) := Finset.Icc (c₀.1 - 1) (c₀.1 + 1) ×ˢ
      (Finset.Icc (c₀.2.1 - 1) (c₀.2.1 + 1) ×ˢ Finset.Icc (c₀.2.2 - 1) (c₀.2.2 + 1))
    have hsub : (Occ.image trip).filter (fun x => x ∈ closedBall z δ) ⊆ box.image trip := by
      intro t ht
      obtain ⟨htP, htz⟩ := Finset.mem_filter.1 ht
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 htP
      have hd : dist (trip c) (trip c₀) ≤ 2 * δ := by
        have := dist_triangle (trip c) z (trip c₀)
        rw [mem_closedBall] at htz ht₀z
        rw [dist_comm z] at this
        linarith
      obtain ⟨h1, h2, h3⟩ := hsep c hc c₀ hc₀ hd
      refine Finset.mem_image.2 ⟨c, ?_, rfl⟩
      simp only [box, Finset.mem_product, Finset.mem_Icc]
      rw [abs_le] at h1 h2 h3
      omega
    calc ((Occ.image trip).filter (fun x => x ∈ closedBall z δ)).card ≤ (box.image trip).card :=
          Finset.card_le_card hsub
      _ ≤ box.card := Finset.card_image_le
      _ = 27 := by
          simp only [box, Finset.card_product, Int.card_Icc]
          have e : ∀ a : ℤ, (a + 1 + 1 - (a - 1)).toNat = 3 := fun a => by omega
          rw [e, e, e]
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp

/-- The coordinate swap of the plane, an isometric involution. -/
def swapE2 (x : E2) : E2 := pt (x 1) (x 0)

theorem dist_swapE2 (x y : E2) : dist (swapE2 x) (swapE2 y) = dist x y := by
  rw [dist_E2, dist_E2]; simp [swapE2]; ring_nf

theorem swapE2_swapE2 (x : E2) : swapE2 (swapE2 x) = x := by
  ext i; fin_cases i <;> simp [swapE2, pt]

/-- Regularity of a graph over the second coordinate. -/
theorem graph2_coveredBy {T : Set ℝ} {ψ : ℝ → ℝ} {K s₀ : ℝ} (hK : 0 ≤ K)
    (hψ : ∀ u ∈ T, ∀ u' ∈ T, |ψ u - ψ u'| ≤ K * (|u - u'| + s₀))
    {ρ r : ℝ} (hρ : 0 < ρ) (hs₀ : s₀ ≤ ρ) (hρr : ρ ≤ r) (x : E2) :
    ∃ m : ℕ, CoveredBy ({a : E2 | ∃ u ∈ T, a = pt (ψ u) u} ∩ ball x r) ρ m ∧
      (m : ℝ) ≤ (4 * K + 5) * (4 * r / ρ + 1) := by
  obtain ⟨m, ⟨cc, hcc⟩, hm⟩ := graph_coveredBy hK hψ hρ hs₀ hρr (swapE2 x)
  refine ⟨m, ⟨fun j => swapE2 (cc j), ?_⟩, hm⟩
  rintro a ⟨⟨u, hu, rfl⟩, ha⟩
  have hmem : pt u (ψ u) ∈ {a : E2 | ∃ u ∈ T, a = pt u (ψ u)} ∩ ball (swapE2 x) r := by
    refine ⟨⟨u, hu, rfl⟩, ?_⟩
    rw [mem_ball] at ha ⊢
    have : pt u (ψ u) = swapE2 (pt (ψ u) u) := by ext i; fin_cases i <;> simp [swapE2]
    rw [this, dist_swapE2]; exact ha
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hcc hmem)
  refine mem_iUnion.2 ⟨j, ?_⟩
  rw [mem_closedBall] at hj ⊢
  have : pt (ψ u) u = swapE2 (pt u (ψ u)) := by ext i; fin_cases i <;> simp [swapE2]
  rw [this, dist_swapE2]; exact hj

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
