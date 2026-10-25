import Submission.Obl.k4_retained_edge_planar_rigidity.CommonSets
import Submission.Obl.k4_retained_edge_planar_rigidity.Budget
import Submission.Obl.k4_retained_edge_planar_rigidity.CollisionFit
import Submission.Obl.k4_retained_edge_planar_rigidity.GeneratedSupport
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.FlatCoeff

/-!
# Retained-edge planar rigidity (paper Proposition 7.6)

The final assembly. Fix `S, ε`. With `s = min S 1`, `β = min ε 1 / 100` and `e₀ = β/10`, the flat
coefficient law (`flat_generated`, from the Fourier-decay input) fixes `n, k`; the collision count
is `d = ⌈3/β⌉ + 2`, and the input exponent `η` is small against `β` and the fixed support degree
`200 * closureDeg 27 d k n`. For every small `h` the numerical budget (`eventually_budget`) holds.
At such an `h`, with `K = h^(-η)`, the graph data give common sets and the restricted ratio law
(`common_sets`), the flat law of the generated coefficients, their support bound
(`generated_support_bound`), the marginal cap of the uniform law on the retained original edges
(`retained_edge_marginal`); the collision argument gives a bounded parallel line fit
(`fit_of_collision`), and undoing the dilation of the second endpoints selects the original edges
(`retained_edges_of_fit`).
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise
open Filter Topology

noncomputable section

/-- The frozen statement's assertion at the mesh `h` with loss `K`. -/
def PlanarRigidityAt (h K S ε : ℝ) : Prop :=
  ∀ (m : ℕ) (w κ : Fin m → ℝ) (A B : Finset (ℝ × ℝ)) (G : Fin m → Finset ((ℝ × ℝ) × (ℝ × ℝ))), (∀ x ∈ A, ∃ a b : ℤ, x = (h * a, h * b)) → (∀ y ∈ B, ∃ a b : ℤ, y = (h * a, h * b)) → (∀ x ∈ A, |x.1| ≤ K ∧ |x.2| ≤ K) → (∀ y ∈ B, |y.1| ≤ K ∧ |y.2| ≤ K) → (1 / (K * h) ≤ (A.card : ℝ)) → ((A.card : ℝ) ≤ K / h) → (1 / (K * h) ≤ (B.card : ℝ)) → ((B.card : ℝ) ≤ K / h) → (∀ i : Fin m, 0 ≤ w i) → ((∑ i : Fin m, w i) = 1) → (∀ i : Fin m, 1 / K ≤ |κ i| ∧ |κ i| ≤ K) → (∀ x r : ℝ, h ≤ r → r ≤ 1 → (∑ i : Fin m, if κ i ∈ Set.Icc x (x + r) then w i else 0) ≤ K * r ^ S) → (∀ i : Fin m, G i ⊆ A ×ˢ B) → (∀ i : Fin m, 1 / (K * h ^ 2) ≤ ((G i).card : ℝ)) → (∀ i : Fin m, (((G i).image (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => (⌊(p.1.1 + κ i * p.2.1) / h⌋, ⌊(p.1.2 + κ i * p.2.2) / h⌋))).card : ℝ) ≤ K / h) → (∀ (i : Fin m) (x y : ℝ), (((G i).filter (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) => p.1.1 ∈ Set.Ico x (x + h) ∧ p.2.1 ∈ Set.Ico y (y + h))).card : ℝ) ≤ K * h ^ 2 * ((G i).card : ℝ)) → ∃ i : Fin m, ∃ G' : Finset ((ℝ × ℝ) × (ℝ × ℝ)), G' ⊆ G i ∧ h ^ ε / h ^ 2 ≤ (G'.card : ℝ) ∧ ∃ ℓ c₁ c₂ : ℝ, |ℓ| + |c₁| + |c₂| ≤ h ^ (-ε) ∧ ∀ p ∈ G', |p.1.2 - ℓ * p.1.1 - c₁| + |p.2.2 - ℓ * p.2.1 - c₂| ≤ h ^ (1 - ε)

/-- Planar rigidity at one mesh `h` at which the numerical budget and the flat law hold. -/
theorem rigidity_at {S ε s β e₀ η η₀ h₁ c C₀ h : ℝ} {d k n : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hsS : s ≤ S) (hc : 0 < c) (hC₀ : 0 < C₀)
    (hT5 : GraphBSG c C₀)
    (hflat : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ν t : ι → ℝ) (R K : ℝ), 0 < R →
      (∀ i, 0 ≤ ν i) → ∑ i, ν i = 1 → (∀ i, |t i| ≤ R) → K ≤ h ^ (-η₀) →
      (∀ x u : ℝ, h ≤ u → u ≤ 1 →
        (∑ i, if t i / R ∈ Set.Icc (x - u) (x + u) then ν i else 0) ≤ K * u ^ s) →
      ∀ x : ℝ, lawMass (genW ν n k) (genVal t R n k) (Set.Icc (x - h) (x + h)) ≤
        60 * h ^ (1 - e₀))
    (hβ : 0 < β) (hβ1 : β ≤ 1 / 100)
    (hB : Budget h η β e₀ ε η₀ h₁ c C₀ d k n) :
    PlanarRigidityAt h (h ^ (-η)) S ε := by
  intro m w κ A B G hAlat hBlat hAb hBb hA1 hA2 hB1 hB2 hw0 hw1 hκ hcap hG hGc hsum hrect
  classical
  have hh := hB.pos
  have hh1 := hB.le_one
  set K := h ^ (-η) with hK
  set L : ℝ := 1 / h with hL
  have hLpos : 0 < L := by positivity
  have hK20 : 2 ^ 20 ≤ K := hB.K_ge
  have hK1 : 1 ≤ K := le_trans (by norm_num) hK20
  have hK0 : 0 < K := by linarith
  -- the frozen hypotheses in the form `L = 1/h`
  have hA1' : L / K ≤ A.card := by rw [hL, div_div, mul_comm]; exact hA1
  have hA2' : (A.card : ℝ) ≤ K * L := by rw [hL, mul_one_div]; exact hA2
  have hB1' : L / K ≤ B.card := by rw [hL, div_div, mul_comm]; exact hB1
  have hB2' : (B.card : ℝ) ≤ K * L := by rw [hL, mul_one_div]; exact hB2
  have hGc' : ∀ i, L ^ 2 / K ≤ (G i).card := fun i => by
    rw [hL, div_pow, one_pow, div_div, mul_comm]; exact hGc i
  have hsum' : ∀ i, ((cells h ((G i).image (fun p => p.1 + κ i • p.2))).card : ℝ) ≤ K * L :=
    fun i => by rw [cells_image_add_smul, hL, mul_one_div]; exact hsum i
  have hcap' : ∀ x r : ℝ, h ≤ r → r ≤ 1 →
      (∑ i, if κ i ∈ Set.Icc x (x + r) then w i else 0) ≤ K * r ^ s := by
    intro x r hr hr1
    refine (hcap x r hr hr1).trans (mul_le_mul_of_nonneg_left ?_ hK0.le)
    exact Real.rpow_le_rpow_of_exponent_ge (lt_of_lt_of_le hh hr) hr1 hsS
  -- common sets and the restricted ratio law
  obtain ⟨i₀, A₀, B₀, I', ν, t, hA₀, hB₀, hRcard, hD, hν0, hν1, htR, htle, htcap⟩ :=
    common_sets hc hC₀ hT5 hh hh1 hLpos hK20 hB.K_ge_c hB.K_ge_C₀ hs hs1 hAlat hBlat hA1' hA2'
      hB1' hB2' hw0 hw1 hκ hcap' hG hGc' hsum'
  have hκ₀ne : κ i₀ ≠ 0 := fun h0 => by
    have h1 := (hκ i₀).1
    rw [h0, abs_zero] at h1
    have : (0 : ℝ) < 1 / K := by positivity
    linarith
  have hκ₀inv : |(κ i₀)⁻¹| ≤ K := by
    rw [abs_inv, inv_le_comm₀ (abs_pos.mpr hκ₀ne) hK0, ← one_div]
    exact (hκ i₀).1
  -- the retained original edges
  set R := (G i₀).filter (fun p => p.1 ∈ A₀ ∧ p.2 ∈ B₀) with hRdef
  have hRpos : (0 : ℝ) < R.card := lt_of_lt_of_le (by positivity) hRcard
  have hRne : R.Nonempty := Finset.card_pos.mp (by exact_mod_cast hRpos)
  -- the flat law of the generated coefficients
  have hflatR := hflat (Fin m) ν t (K ^ 2) (K ^ 172) (by positivity) hν0 hν1 htle hB.K_flat htcap
  -- the marginal cap of the uniform law on the retained edges
  have hGcard : ((G i₀).card : ℝ) ≤ K ^ 42 * R.card := by
    have h1 : ((G i₀).card : ℝ) ≤ (A ×ˢ B).card := by
      exact_mod_cast Finset.card_le_card (hG i₀)
    rw [Finset.card_product, Nat.cast_mul] at h1
    calc ((G i₀).card : ℝ) ≤ A.card * B.card := h1
      _ ≤ (K * L) * (K * L) := mul_le_mul hA2' hB2' (by positivity) (by positivity)
      _ = K ^ 42 * (L ^ 2 / K ^ 40) := by field_simp
      _ ≤ K ^ 42 * R.card := by gcongr
  have hBh : (B.card : ℝ) * h ≤ K := (le_div_iff₀ hh).mp hB2
  have hmarg : ∀ x r : ℝ, 0 ≤ r →
      (∑ e : R, (1 / (R.card : ℝ)) * (if |e.val.1.1 - x| ≤ r then 1 else 0)) ≤
        2 * K ^ 44 * (r + h) := by
    intro x r hr
    have := retained_edge_marginal hh hK0.le (by positivity : (0 : ℝ) ≤ K ^ 42) hRne
      (Finset.filter_subset _ _) (fun e he => (Finset.mem_product.mp (hG i₀ he)).2) hBh hGcard
      (hrect i₀) x r hr
    calc _ ≤ 2 * K ^ 2 * K ^ 42 * (r + h) := this
      _ = 2 * K ^ 44 * (r + h) := by ring
  -- endpoints
  have hmemR : ∀ e : R, e.val.1 ∈ A₀ ∧ e.val.2 ∈ B₀ := fun e => (Finset.mem_filter.mp e.2).2
  have hmemG : ∀ e : R, e.val.1 ∈ A ∧ e.val.2 ∈ B := fun e =>
    Finset.mem_product.mp (hG i₀ (Finset.mem_filter.mp e.2).1)
  have hKK : K ≤ K ^ 2 := le_self_pow₀ hK1 (by norm_num)
  have ha : ∀ e : R, |(e.val.1).1| ≤ K ^ 2 ∧ |(e.val.1).2| ≤ K ^ 2 := fun e =>
    ⟨((hAb _ (hmemG e).1).1).trans hKK, ((hAb _ (hmemG e).1).2).trans hKK⟩
  have hb : ∀ e : R, |(-(κ i₀ • e.val.2)).1| ≤ K ^ 2 ∧ |(-(κ i₀ • e.val.2)).2| ≤ K ^ 2 := by
    intro e
    have hy := hBb _ (hmemG e).2
    simp only [Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_neg,
      abs_mul]
    constructor
    · calc |κ i₀| * |e.val.2.1| ≤ K * K := mul_le_mul (hκ i₀).2 hy.1 (abs_nonneg _) hK0.le
        _ = K ^ 2 := by ring
    · calc |κ i₀| * |e.val.2.2| ≤ K * K := mul_le_mul (hκ i₀).2 hy.2 (abs_nonneg _) hK0.le
        _ = K ^ 2 := by ring
  have haE : ∀ e : R, e.val.1 ∈ A₀ := fun e => (hmemR e).1
  have hbF : ∀ e : R, -(κ i₀ • e.val.2) ∈ -(κ i₀ • B₀) := fun e =>
    Finset.mem_neg.mpr ⟨_, Finset.smul_mem_smul_finset (hmemR e).2, rfl⟩
  -- the support bound of the generated coefficient sums
  have hM : ∀ γ : Fin d × Bool → (Fin k → Fin n → Fin m),
      ((cells h (∑ i, (genVal t (K ^ 2) n k (γ (i, true)) • A₀ +
        genVal t (K ^ 2) n k (γ (i, false)) • (-(κ i₀ • B₀))))).card : ℝ) ≤
        ClosureData.closureConst (K ^ 200) 27 d k n * (1 / h) :=
    fun γ => generated_support_bound hD t htR (one_le_pow₀ hK1) d k n γ
  have hMpos : 0 < ClosureData.closureConst (K ^ 200) 27 d k n * (1 / h) := by
    simp only [ClosureData.closureConst, ClosureData.Bn, ClosureData.M1]
    positivity
  have hp : 0 < h ^ β := Real.rpow_pos_of_pos hh β
  have hp1 : h ^ β ≤ 1 := Real.rpow_le_one hh.le hh1 hβ.le
  have hΔ : 0 < h ^ (1 - 4 * β) := Real.rpow_pos_of_pos hh _
  have hΔ1 : h ^ (1 - 4 * β) ≤ 1 := Real.rpow_le_one hh.le hh1 (by linarith)
  -- the collision argument
  obtain ⟨ℓ, c₁, c₂, hcoef, hmass⟩ := fit_of_collision (𝔈 := R) (α := Fin k → Fin n → Fin m)
    (fun _ => 1 / (R.card : ℝ)) (fun _ => by positivity) (uniform_edge_sum hRne)
    (genW ν n k) (genW_nonneg hν0 n k) (sum_genW hν1 n k) (genVal t (K ^ 2) n k)
    (fun e => e.val.1) (fun e => -(κ i₀ • e.val.2)) haE hbF (m := d)
    (C := 2 * K ^ 44) (D := K ^ 2) (p := h ^ β) (q := h ^ β) (Δ := h ^ (1 - 4 * β))
    (φ := 60 * h ^ (1 - e₀)) (M := ClosureData.closureConst (K ^ 200) 27 d k n * (1 / h))
    hh (by nlinarith [one_le_pow₀ (n := 44) hK1]) (one_le_pow₀ hK1) hp hp1 hp hΔ hΔ1 hMpos
    hflatR hmarg ha hb hM hB.budget hB.small
  -- undo the dilation of the second endpoints and select original edges
  have hmass' : h ^ β ≤ ∑ e : R, (1 / (R.card : ℝ)) *
      (if |e.val.1.2 - ℓ * e.val.1.1 - c₁| +
        |(-κ i₀) * e.val.2.2 - ℓ * ((-κ i₀) * e.val.2.1) - c₂| ≤
          16 * (2 * K ^ 44) * K ^ 2 * h ^ (1 - 4 * β) / (h ^ β * h ^ β) then 1 else 0) := by
    refine hmass.le.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, neg_mul]
  obtain ⟨G', hG'R, hG'card, c₂', hcoef', hfit⟩ := retained_edges_of_fit hRne hK1
    (neg_ne_zero.mpr hκ₀ne) (by rwa [inv_neg, abs_neg]) hcoef hmass'
  refine ⟨i₀, G', hG'R.trans (Finset.filter_subset _ _), ?_, ℓ, c₁, c₂', ?_, ?_⟩
  · calc h ^ ε / h ^ 2 ≤ h ^ β * ((1 / h) ^ 2 / K ^ 40) := hB.count
      _ ≤ h ^ β * R.card := by gcongr
      _ ≤ G'.card := hG'card
  · exact hcoef'.trans hB.coeff
  · intro p hp'
    exact (hfit p hp').trans hB.error

/-- **Retained-edge planar rigidity** from the Fourier-decay input. -/
theorem main : OSSDecay → ∀ S : ℝ, 0 < S → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ h₀ : ℝ,
    0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ → PlanarRigidityAt h (h ^ (-η)) S ε := by
  intro hT4 S hS ε hε
  classical
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = min S 1 := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ lt_min hS one_pos
  have hs1 : s ≤ 1 := hsdef ▸ min_le_right _ _
  have hsS : s ≤ S := hsdef ▸ min_le_left _ _
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = min ε 1 / 100 := ⟨_, rfl⟩
  have hmin : 0 < min ε 1 := lt_min hε one_pos
  have hβ : 0 < β := by rw [hβdef]; positivity
  have hβ1 : β ≤ 1 / 100 := by have := min_le_right ε 1; rw [hβdef]; linarith
  have hβε : 100 * β ≤ ε := by have := min_le_left ε 1; rw [hβdef]; linarith
  obtain ⟨e₀, he₀def⟩ : ∃ e₀ : ℝ, e₀ = β / 10 := ⟨_, rfl⟩
  have he₀ : 0 < e₀ := by rw [he₀def]; positivity
  have he₀1 : e₀ ≤ 1 := by rw [he₀def]; linarith
  have he₀β : 10 * e₀ ≤ β := by rw [he₀def]; linarith
  obtain ⟨c, C₀, hc, hC₀, hT5⟩ := graphBSG_exists
  obtain ⟨n, k, η₀, h₁, hη₀, hh₁, hflat⟩ := flat_generated hT4 hs he₀ he₀1
  obtain ⟨d, hddef⟩ : ∃ d : ℕ, d = ⌈3 / β⌉₊ + 2 := ⟨_, rfl⟩
  have hd : 2 ≤ d := by omega
  have hdβ : 3 ≤ ((d : ℝ) - 1) * β := by
    have h1 : 3 / β ≤ (⌈3 / β⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((d : ℝ) - 1) = (⌈3 / β⌉₊ : ℝ) + 1 := by rw [hddef]; push_cast; ring
    have h3 : (3 / β) * β = 3 := by field_simp
    rw [h2]
    nlinarith
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = ((200 * closureDeg 27 d k n : ℕ) : ℝ) := ⟨_, rfl⟩
  have hP : 0 ≤ P := hPdef ▸ Nat.cast_nonneg _
  have hden : 0 < P + 44 * (d : ℝ) + 2 := by positivity
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (η₀ / 172) (β / (P + 44 * d + 2)) := ⟨_, rfl⟩
  have hη : 0 < η := hηdef ▸ lt_min (by positivity) (div_pos hβ hden)
  have hηη₀ : 172 * η ≤ η₀ := by
    have := min_le_left (η₀ / 172) (β / (P + 44 * d + 2)); rw [hηdef]; linarith
  have hηβ : (((200 * closureDeg 27 d k n : ℕ) : ℝ) + 44 * d + 2) * η ≤ β := by
    rw [← hPdef]
    have := min_le_right (η₀ / 172) (β / (P + 44 * d + 2))
    calc (P + 44 * d + 2) * η ≤ (P + 44 * d + 2) * (β / (P + 44 * d + 2)) := by
          rw [hηdef]; gcongr
      _ = β := by field_simp
  obtain ⟨h₀, hh₀, hbud⟩ := exists_of_eventually
    (eventually_budget (c := c) (C₀ := C₀) hβ hβ1 hβε he₀β hd hdβ hη hηη₀ hηβ hh₁)
  refine ⟨η, hη, h₀, hh₀, fun h hh hhlt => ?_⟩
  have hB := hbud h hh hhlt
  exact rigidity_at hs hs1 hsS hc hC₀ hT5 (hflat h hh hB.lt_h₁) hβ hβ1 hB

end

end Submission.Obl.k4_retained_edge_planar_rigidity
