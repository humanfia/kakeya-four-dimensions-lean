import Submission.Obl.k4_horizontal_strict_parameter_step.ChartAssembly
import Submission.Obl.k4_horizontal_strict_parameter_step.StrictFromRawCharts

/-!
# The chart half of the strict step, for every prepared input

`rawStepPreparation_of_compared` turns the comparison half `ComparedStep` into x0852's
`RawStepPreparation`: the mesh caps come from the second hypothesis block at one fixed mesh
exponent, the a.e. bounds from the first and third blocks, and all numerical scale conditions
of `rawChartFamily_of_compared` hold for large samples once `sMax ≤ e₀/10`.
-/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter
open Submission.Lib.K4MovingMeshBoxes

noncomputable section

/-- Powers of a large base beat any constant. -/
theorem eventually_const_le_rpow (C p : ℝ) (hp : 0 < p) :
    ∀ᶠ x : ℝ in atTop, C ≤ x ^ p :=
  (tendsto_rpow_atTop hp).eventually (eventually_ge_atTop C)

/-- A constant multiple of a smaller power is below a larger one. -/
theorem const_mul_rpow_le {x C p q : ℝ} (hx : 0 < x) (hC : C ≤ x ^ (q - p)) :
    C * x ^ p ≤ x ^ q := by
  have : x ^ q = x ^ (q - p) * x ^ p := by
    rw [← Real.rpow_add hx]
    ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hx.le _)

theorem zc_eq_baseMesh {α : Type} (b : ℕ → α → Fin 6 → ℝ) (k : ℕ) (Nk r : ℝ) (p : α × ℝ) :
    zc b k Nk r p = baseMesh (Nk ^ (-r)) (basePoint (b k p.1) p.2) := by
  funext e
  fin_cases e <;> rfl

theorem floor_div_eq_set {χ : ℝ} (hχ : 0 < χ) (v : ℤ) :
    {w : ℝ | ⌊w / χ⌋ = v} = Ico ((v : ℝ) * χ) (((v : ℝ) + 1) * χ) := by
  ext w
  simp only [mem_setOf_eq, mem_Ico, Int.floor_eq_iff, le_div_iff₀ hχ, div_lt_iff₀ hχ]

/-- The second hypothesis block gives the mesh caps at every fixed mesh exponent. -/
theorem eventually_meshCapAt {N K : ℕ → ℝ} {d S : ℝ} {α : Type} [MeasurableSpace α]
    {μ : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ}
    {P : ℕ → MvPolynomial (Fin 4) ℝ} (hN : ∀ k, 2 ≤ N k) (h2 : Hyp2 N K d S μ π b P)
    {r₀ e₀ : ℝ} (hr₀ : 0 < r₀) (he₀ : 0 < e₀) :
    ∀ᶠ k in atTop, MeshCapAt (μ k) (π k) (b k) d (K k) (N k ^ (-e₀)) (N k ^ (-r₀)) := by
  set R : ℝ := r₀ + e₀ + r₀⁻¹ + e₀⁻¹ + 2 with hRdef
  have hr₀i : 0 < r₀⁻¹ := inv_pos.mpr hr₀
  have he₀i : 0 < e₀⁻¹ := inv_pos.mpr he₀
  have hR : 1 < R := by linarith
  have hRpos : 0 < R := by linarith
  have hRinv : ∀ x : ℝ, 0 < x → x⁻¹ ≤ R → R⁻¹ ≤ x := by
    intro x hx hxR
    rw [inv_le_comm₀ hRpos hx]
    exact hxR
  filter_upwards [h2 R hR] with k hk
  intro ω hmω hω1 z j v
  have hNk : 1 < N k := by linarith [hN k]
  have hNk0 : 0 < N k := by linarith
  have hm0 : 0 < N k ^ (-r₀) := Real.rpow_pos_of_pos hNk0 _
  have hω0 : 0 < ω := hm0.trans_le hmω
  set s : ℝ := -Real.logb (N k) ω with hsdef
  have hNs : N k ^ (-s) = ω := by
    rw [hsdef, neg_neg, Real.rpow_logb hNk0 hNk.ne' hω0]
  have hs0 : 0 ≤ s := by
    rw [hsdef, neg_nonneg]
    exact Real.logb_nonpos hNk hω0.le hω1
  have hsr : s ≤ r₀ := by
    rw [hsdef, neg_le]
    have := Real.logb_le_logb_of_le hNk hm0 hmω
    rwa [Real.logb_rpow hNk0 hNk.ne'] at this
  have hχ : 0 < N k ^ (-e₀) := Real.rpow_pos_of_pos hNk0 _
  have hcap := (hk r₀ s e₀ (hRinv r₀ hr₀ (by linarith)) (by linarith) hs0 (by linarith)
    (hRinv e₀ he₀ (by linarith)) (by linarith)).2.2 false z j v
  simp only [Bool.false_eq_true, if_false] at hcap
  rw [floor_div_eq_set hχ v] at hcap
  have hset : {p : α × ℝ | baseMesh (N k ^ (-r₀)) (basePoint (b k p.1) p.2) = z ∧
      ⌊(b k p.1 2 + p.2 * b k p.1 5) / ω⌋ = j ∧ ⌊b k p.1 3 / N k ^ (-e₀)⌋ = v} =
      {p | zc b k (N k) r₀ p = z ∧ ⌊xs b k p.1 p.2 3 / N k ^ (-s)⌋ = j ∧
        ⌊b k p.1 3 / N k ^ (-e₀)⌋ = v} := by
    ext p
    simp only [mem_setOf_eq, zc_eq_baseMesh, hNs]
    rfl
  rw [hset]
  refine hcap.trans (le_of_eq ?_)
  congr 2
  rw [← hNs, ← Real.rpow_natCast, ← Real.rpow_mul hNk0.le, ← Real.rpow_mul hNk0.le,
    mul_assoc, ← Real.rpow_add hNk0]
  congr 2
  push_cast
  ring

/-- The first and third hypothesis blocks give the horizontal contact and the coefficient
bounds almost everywhere in the incidence law. -/
theorem eventually_ae_good {N K : ℕ → ℝ} {d κ ℓ U e₀ : ℝ} {α : Type} [MeasurableSpace α]
    {ν : ℕ → Measure α} {μ ρ : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {P : ℕ → MvPolynomial (Fin 4) ℝ} {T n : ℕ → ℝ → ℕ}
    {j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)}
    {A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α}
    {c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ}
    {F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ}
    (hU : 0 < U) (h1 : Hyp1 K ν μ ρ π b P) (h3 : Hyp3 N K d κ ℓ U e₀ ν μ π b P T n j A B c F) :
    ∀ᶠ k in atTop, ∀ᵐ p ∂μ k, |b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀) ∧
      |b k p.1 0| ≤ K k ∧ |b k p.1 3| ≤ K k := by
  set R : ℝ := U⁻¹ + 2 with hRdef
  have hUi : 0 < U⁻¹ := inv_pos.mpr hU
  have hR : 1 < R := by linarith
  have hRU : R⁻¹ ≤ U := by
    rw [inv_le_comm₀ (by linarith) hU]
    linarith
  filter_upwards [h3 R hR] with k hk
  obtain ⟨-, -, -, -, hlab, hcov, -⟩ := hk U hRU le_rfl
  have hhor : ∀ᵐ p ∂μ k, |b k p.1 4 + b k p.1 0| ≤ N k ^ (-e₀) := by
    rcases isEmpty_or_nonempty (Fin (n k U)) with hne | ⟨⟨i⟩⟩
    · filter_upwards [hcov] with p hp
      obtain ⟨i, -⟩ := hp
      exact isEmptyElim i
    · exact ((hlab i).2.2.2.2.2.2.2.2 rfl).2.1
  obtain ⟨-, -, -, hμ, -, -, -, -, hbν, -⟩ := h1 k
  have hbν' : ∀ᵐ l ∂ν k, |b k l 0| ≤ K k ∧ |b k l 3| ≤ K k := by
    filter_upwards [hbν] with l hl
    constructor
    · linarith [abs_nonneg (b k l 1), abs_nonneg (b k l 3), abs_nonneg (b k l 4)]
    · linarith [abs_nonneg (b k l 0), abs_nonneg (b k l 1), abs_nonneg (b k l 4)]
  have hprod : ∀ᵐ p ∂(ν k).prod (volume : Measure ℝ), |b k p.1 0| ≤ K k ∧ |b k p.1 3| ≤ K k := by
    rw [ae_iff] at hbν' ⊢
    have hset : {p : α × ℝ | ¬(|b k p.1 0| ≤ K k ∧ |b k p.1 3| ≤ K k)} =
        {l : α | ¬(|b k l 0| ≤ K k ∧ |b k l 3| ≤ K k)} ×ˢ (univ : Set ℝ) := by
      ext p
      simp
    rw [hset, Measure.prod_prod, hbν', zero_mul]
  have hbμ : ∀ᵐ p ∂μ k, |b k p.1 0| ≤ K k ∧ |b k p.1 3| ≤ K k :=
    (Measure.absolutelyContinuous_of_le_smul hμ).ae_le hprod
  filter_upwards [hhor, hbμ] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- All numerical scale conditions of the chart half, for a large base `x`, with the mesh
exponent `(1+u)s₀ + c' + 3δ + 1`. -/
theorem eventually_chart_scales {δ ξ e₀ u s₀ c' : ℝ} (hδ : 0 < δ) (hδξ : 12 * δ ≤ ξ)
    (hs₀ : 0 < s₀) (hu : 0 ≤ u) (hc' : 0 ≤ c') (he : δ + (1 + u) * s₀ + c' < e₀) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧
      806400 * x ^ (6 * δ) ≤ x ^ ξ ∧ 2 * x ^ (-s₀) ≤ 1 ∧
      8 * x ^ δ * x ^ (-((1 + u) * s₀ + c' + 3 * δ + 1)) ≤ x ^ (-c') ∧
      3 * x ^ δ * x ^ (-((1 + u) * s₀ + c' + 3 * δ + 1)) ≤
        x ^ (-(u * s₀)) * x ^ (-c') ∧
      x ^ (-e₀) ≤ x ^ (-(u * s₀)) * x ^ (-c') ∧
      x ^ (-((1 + u) * s₀ + c' + 3 * δ + 1)) ≤ 2 * x ^ (-s₀) * x ^ (-c') ∧
      2 * x ^ δ * x ^ (-((1 + u) * s₀ + c' + 3 * δ + 1)) +
        (6 * x ^ δ / x ^ (-(u * s₀))) *
          (x ^ (-e₀) + 3 * x ^ δ * x ^ (-((1 + u) * s₀ + c' + 3 * δ + 1))) ≤
        2 * x ^ (-s₀) * x ^ (-c') := by
  set r₀ : ℝ := (1 + u) * s₀ + c' + 3 * δ + 1 with hr₀
  have hus : 0 ≤ u * s₀ := mul_nonneg hu hs₀.le
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_le_rpow 806400 (ξ - 6 * δ) (by linarith),
    eventually_const_le_rpow 2 s₀ hs₀,
    eventually_const_le_rpow 8 ((1 + u) * s₀ + 2 * δ + 1) (by nlinarith),
    eventually_const_le_rpow 3 (s₀ + 2 * δ + 1) (by linarith),
    eventually_const_le_rpow 3 (u * s₀ + 2 * δ + 1) (by linarith),
    eventually_const_le_rpow 9 (e₀ - δ - (1 + u) * s₀ - c') (by linarith),
    eventually_const_le_rpow 27 (δ + 1) (by linarith)] with x hx1 hA hB hC hD' hE hF hG
  have hx : 0 < x := by linarith
  have hmul : ∀ p q : ℝ, x ^ p * x ^ q = x ^ (p + q) := fun p q => (Real.rpow_add hx p q).symm
  refine ⟨hx1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact const_mul_rpow_le hx (by convert hA using 2; try ring)
  · have := const_mul_rpow_le (p := -s₀) (q := 0) hx (by convert hB using 2; try ring)
    rwa [Real.rpow_zero] at this
  · rw [mul_assoc, hmul]
    exact const_mul_rpow_le hx (by convert hC using 2; try ring)
  · rw [mul_assoc, hmul, hmul]
    exact const_mul_rpow_le hx (by convert hD' using 2; try ring)
  · rw [hmul]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
  · rw [mul_assoc, hmul]
    have h1 : x ^ (-r₀) ≤ x ^ (-s₀ + -c') :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
    have h2 : 0 ≤ x ^ (-s₀ + -c') := Real.rpow_nonneg hx.le _
    linarith
  · -- the rounding condition: three terms, each a third of the bound
    have hdiv : 6 * x ^ δ / x ^ (-(u * s₀)) = 6 * x ^ (δ + u * s₀) := by
      rw [mul_div_assoc, ← Real.rpow_sub hx]
      ring_nf
    rw [hdiv, mul_assoc 2 (x ^ (-s₀)), hmul]
    have t1 : 3 * (2 * x ^ δ * x ^ (-r₀)) ≤ 2 * x ^ (-s₀ + -c') := by
      have := const_mul_rpow_le (C := 3) (p := δ + -r₀) (q := -s₀ + -c') hx
        (by convert hE using 2; try ring)
      rw [mul_assoc 2, hmul]
      linarith
    have t2 : 3 * (6 * x ^ (δ + u * s₀) * x ^ (-e₀)) ≤ 2 * x ^ (-s₀ + -c') := by
      have := const_mul_rpow_le (C := 9) (p := δ + u * s₀ + -e₀) (q := -s₀ + -c') hx
        (by convert hF using 2; try ring)
      rw [mul_assoc 6, hmul]
      linarith
    have t3 : 3 * (6 * x ^ (δ + u * s₀) * (3 * x ^ δ * x ^ (-r₀))) ≤
        2 * x ^ (-s₀ + -c') := by
      have := const_mul_rpow_le (C := 27) (p := δ + u * s₀ + (δ + -r₀)) (q := -s₀ + -c') hx
        (by convert hG using 2; try ring)
      have e1 : 6 * x ^ (δ + u * s₀) * (3 * x ^ δ * x ^ (-r₀)) =
          18 * x ^ (δ + u * s₀ + (δ + -r₀)) := by
        rw [Real.rpow_add hx (δ + u * s₀) (δ + -r₀), Real.rpow_add hx δ (-r₀)]
        ring
      rw [e1]
      linarith
    have e2 : 6 * x ^ (δ + u * s₀) * (x ^ (-e₀) + 3 * x ^ δ * x ^ (-r₀)) =
        6 * x ^ (δ + u * s₀) * x ^ (-e₀) + 6 * x ^ (δ + u * s₀) * (3 * x ^ δ * x ^ (-r₀)) := by
      ring
    rw [e2]
    linarith

/-- The chart half of the strict step for every prepared input: the comparison half gives
x0852's `RawStepPreparation`. The buffer is shrunk to `e₀/10`. -/
theorem rawStepPreparation_of_compared (hA : ComparedStep) : RawStepPreparation := by
  intro hScalar hRow hMatch d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he
  obtain ⟨s₁, hs₁, hA'⟩ := hA hScalar hRow hMatch d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he
  refine ⟨min s₁ (e₀ / 10), lt_min hs₁ (by positivity), ?_⟩
  intro sMax hsMax hsMax₁ u θ hu hu1 hθ hθmax hEng
  have hC := hA' sMax hsMax (hsMax₁.trans (min_le_left _ _)) u θ hu hu1 hθ hθmax hEng
  have hsMaxe : sMax ≤ e₀ / 10 := hsMax₁.trans (min_le_right _ _)
  intro N K hN hNt hK α _ ν μ ρ π b P T n j A B c F h1 h2 h3 h4
  have hL := hC N K hN hNt hK α ν μ ρ π b P T n j A B c F h1 h2 h3 h4
  intro s hs hss ξ hξ
  have hL' := hL s hs hss
  simp only at hL' ⊢
  set s₀ : ℝ := s / (1 + θ) with hs₀def
  set cc : ℝ := θ * s₀ with hccdef
  set c' : ℝ := cc * (1000 / (1 - d)) with hc'def
  set δ : ℝ := min (ξ / 12) (e₀ / 10) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδξ : 12 * δ ≤ ξ := by
    have : δ ≤ ξ / 12 := min_le_left _ _
    linarith
  have hδe : δ ≤ e₀ / 10 := min_le_right _ _
  have hθ1 : 1 ≤ 1 + θ := by linarith
  have hs₀ : 0 < s₀ := div_pos hs (by linarith)
  have hs₀s : s₀ ≤ s := div_le_self hs.le hθ1
  have hu0 : 0 ≤ u := by linarith
  have hd1' : 0 < 1 - d := by linarith
  have hc'0 : 0 ≤ c' := by positivity
  have hc'le : c' ≤ s₀ / 10 := by
    have hθ' : θ * (1000 / (1 - d)) ≤ (u - 2 * κ) / 10 := by
      rw [← mul_div_assoc, div_le_iff₀ hd1']
      have := mul_le_mul_of_nonneg_right hθmax (by norm_num : (0 : ℝ) ≤ 1000)
      have heq : (1 - d) / 10000 * (u - 2 * κ) * 1000 = (u - 2 * κ) / 10 * (1 - d) := by ring
      linarith
    have hκu : (u - 2 * κ) / 10 ≤ 1 / 10 := by linarith
    calc c' = θ * (1000 / (1 - d)) * s₀ := by rw [hc'def, hccdef]; ring
      _ ≤ (1 / 10) * s₀ := mul_le_mul_of_nonneg_right (hθ'.trans hκu) hs₀.le
      _ = s₀ / 10 := by ring
  have he' : δ + (1 + u) * s₀ + c' < e₀ := by
    have h1' : (1 + u) * s₀ ≤ 2 * s₀ := by nlinarith
    have h2' : s₀ < e₀ / 10 := lt_of_le_of_lt hs₀s (lt_of_lt_of_le hss hsMaxe)
    linarith
  set r₀ : ℝ := (1 + u) * s₀ + c' + 3 * δ + 1 with hr₀def
  have hr₀ : 0 < r₀ := by positivity
  filter_upwards [hL' δ hδ, eventually_meshCapAt hN h2 hr₀ he, eventually_ae_good hU h1 h3,
    hNt.eventually (eventually_chart_scales hδ hδξ hs₀ hu0 hc'0 he'), hK.2 δ hδ]
    with k hLk hcapk hgoodk hsck hKk
  obtain ⟨L⟩ := hLk
  obtain ⟨hb, hν, hπ, hμ, hρ, hμt, -⟩ := h1 k
  haveI := hν
  haveI : IsFiniteMeasure (π k) := by haveI := hπ; infer_instance
  obtain ⟨hx1, hloss, ha1, hm8, hmD3, hχD, hma, hround3⟩ := hsck
  have hNk : 0 < N k := by linarith [hN k]
  have hD : N k ^ (-u * s₀) = N k ^ (-(u * s₀)) := by rw [neg_mul]
  have hζ : (N k ^ (-cc)) ^ (1000 / (1 - d)) = N k ^ (-c') := by
    rw [← Real.rpow_mul hNk.le, hc'def]
    ring_nf
  have hKk1 : 1 ≤ K k := hK.1 k
  have hMδ : 1 ≤ N k ^ δ := Real.one_le_rpow hx1 hδ.le
  have hK3 : K k + 2 ≤ 3 * N k ^ δ := by linarith
  have hm0 : 0 < N k ^ (-r₀) := Real.rpow_pos_of_pos hNk _
  have hD0 : 0 < N k ^ (-(u * s₀)) := Real.rpow_pos_of_pos hNk _
  refine rawChartFamily_of_compared (m := N k ^ (-r₀)) (K := K k) L hb hd hd1.le hx1 hδ hKk1
    hKk hloss (by rw [hD]; exact hD0)
    (by rw [hD]; exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by nlinarith))
    (Real.rpow_pos_of_pos hNk _)
    (by rw [hζ]; exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)) hm0
    (by rw [hζ]; exact hm8)
    (by
      rw [hD, hζ]
      exact (mul_le_mul_of_nonneg_right hK3 hm0.le).trans hmD3)
    (by rw [hD, hζ]; exact hχD)
    (by rw [hζ]; exact hma) ha1
    (by
      rw [hD, hζ]
      refine le_trans ?_ hround3
      gcongr)
    hμ hρ hμt hgoodk hcapk

end

end Submission.Obl.k4_horizontal_strict_parameter_step
