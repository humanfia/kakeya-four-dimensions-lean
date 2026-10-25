import Mathlib
import Submission.Obl.k4_horizontal_coefficient_count.LMLight
import Submission.Obl.k4_horizontal_coefficient_count.LMExtract
import Submission.Obl.k4_scalar_coefficient_clustering
import Submission.Obl.k4_plank_estimate

/-!
# The light-mass estimate along the frozen sequence

At a fixed depth `0 < s ≤ U`, `s < e₀`, and a fixed lightness exponent `ε₁`,
the labels of light code cells carry current mass at most `N^(-δ)` for some
`δ > 0` and all large indices.  The only input besides the frozen hypotheses
is the support count of `DepthData` (`DepthData.SupportCount`), stated for every
single-depth data satisfying `DepthData.Hyp`.
-/

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

open Submission.Obl.k4_critical_switching_state_preparation (Data)

variable {α : Type} [MeasurableSpace α]

/-- Subpower sequences beat every fixed polynomial. -/
theorem eventually_poly_le {N K : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k)
    (hNt : Tendsto N atTop atTop) (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (C : ℝ) (p : ℕ) {τ : ℝ} (hτ : 0 < τ) : ∀ᶠ k in atTop, C * K k ^ p ≤ N k ^ τ := by
  have hτ' : 0 < τ / (2 * ((p : ℝ) + 1)) := by positivity
  have hbig : ∀ᶠ k in atTop, |C| ≤ N k ^ (τ / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp hNt).eventually
      (eventually_ge_atTop |C|)
  filter_upwards [hsub _ hτ', hbig] with k hk hC
  have hN0 : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  have hK0 : 0 ≤ K k := by linarith [hK k]
  have h1 : K k ^ p ≤ N k ^ (τ / 2) := by
    calc K k ^ p ≤ (N k ^ (τ / (2 * ((p : ℝ) + 1)))) ^ p := pow_le_pow_left₀ hK0 hk p
      _ = N k ^ (τ / (2 * ((p : ℝ) + 1)) * p) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      _ ≤ N k ^ (τ / 2) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hKp : 0 ≤ K k ^ p := pow_nonneg hK0 p
  calc C * K k ^ p ≤ |C| * K k ^ p := mul_le_mul_of_nonneg_right (le_abs_self C) hKp
    _ ≤ N k ^ (τ / 2) * N k ^ (τ / 2) := mul_le_mul hC h1 hKp (Real.rpow_nonneg hN0.le _)
    _ = N k ^ τ := by rw [← Real.rpow_add hN0]; ring_nf

/-- Scalar clustering at one value of `N`, in the form used by `light_mass_le`. -/
theorem clusterOracle_of {d s ε η N : ℝ} (hN : 1 < N)
    (hCS : ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α)
      (a : α → EuclideanSpace ℝ (Fin 3)) (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)),
      Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
      (∀ l : α, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) →
      ENNReal.ofReal (N ^ (-η)) ≤ (ν.prod MeasureTheory.volume) E →
      (F.card : ℝ) ≤ N ^ η * (N ^ (-s)) ^ (-1 - d) →
      (∀ l : α, ∀ t : ℝ, (l, t) ∈ E →
        (⌊t / (N ^ (-s))⌋, ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / (N ^ (-s))⌋) ∈ F) →
      (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-s) ≤ r →
        ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d)) →
      ∃ q : Fin 3 → ℤ, ENNReal.ofReal (N ^ (-s * d - ε)) ≤
        ν {l | (∀ j : Fin 3, ⌊a l j / (N ^ (-s))⌋ = q j) ∧
          ENNReal.ofReal (N ^ (-ε)) ≤ MeasureTheory.volume {t : ℝ | (l, t) ∈ E}}) :
    ClusterOracle (N ^ (-s)) d (N ^ η) (N ^ (-ε)) := by
  intro β _ ν f E F hf hE hEsub hfn hν hνE hF hsupp hfrost
  have hN0 : 0 < N := by linarith
  have hinv : (N ^ η)⁻¹ = N ^ (-η) := (Real.rpow_neg hN0.le η).symm
  rw [hinv] at hνE
  obtain ⟨q, hq⟩ := hCS β ν f E F hf hE hEsub hfn hν hνE hF hsupp hfrost
  refine ⟨q, le_trans (le_of_eq ?_) hq⟩
  congr 1
  rw [show -s * d - ε = (-s) * d + (-ε) by ring, Real.rpow_add hN0, Real.rpow_mul hN0.le]

/-- The light-mass estimate along the frozen sequence. -/
theorem light_mass_eventually (cfg : Data α) (hN : ∀ k, 2 ≤ cfg.N k)
    (hNt : Tendsto cfg.N atTop atTop) (hK : ∀ k, 1 ≤ cfg.K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.K k ≤ cfg.N k ^ ε)
    (hd0 : 0 ≤ cfg.d) (hd1 : cfg.d < 1) (hκ0 : 0 < cfg.κ) (hκ : 2 * cfg.κ < 1)
    (hℓ : cfg.ℓ = cfg.κ) (he0 : 0 < cfg.e₀)
    (hbasic : cfg.Basic) (hcaps : cfg.Caps) (hatlas : cfg.Atlas)
    (C₀ : ℝ) (p : ℕ) (hsupp : ∀ H : DepthData α, H.Hyp → H.SupportCount (C₀ * H.K ^ p))
    {s : ℝ} (hs0 : 0 < s) (hsU : s ≤ cfg.U) (hse : s < cfg.e₀) {ε₁ : ℝ} (hε₁ : 0 < ε₁) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ k in atTop,
      cfg.ρ k (lmLight (cfg.ρ k) (cfg.π k) (cfg.b k) (cfg.N k ^ (-cfg.e₀)) (cfg.N k ^ (-s))
        cfg.d (cfg.N k ^ ε₁) (goodSet (cfg.b k) (cfg.K k) (cfg.N k ^ (-cfg.e₀))) ×ˢ univ) ≤
        ENNReal.ofReal (cfg.N k ^ (-δ)) := by
  obtain ⟨η, hη, N₀, -, hCS⟩ := Submission.k4_scalar_coefficient_clustering
    Submission.k4_plank_estimate cfg.d s (ε₁ / 2) hd0 hd1 hs0 (by positivity)
  refine ⟨η / 4, by positivity, ?_⟩
  filter_upwards [eventually_depthDataAt_hyp cfg hN hK hsub hd0 hd1 hκ0 hκ hℓ he0 hbasic hcaps
      hatlas hs0 hsU hse, hNt.eventually_ge_atTop N₀,
    eventually_poly_le hN hNt hK hsub C₀ p hη,
    eventually_poly_le hN hNt hK hsub 2574 4 hη,
    eventually_poly_le hN hNt hK hsub 17 2 (by positivity : 0 < η / 4)] with k hH hNk hc1 hc2 hc3
  have hN0 : 0 < cfg.N k := by linarith [hN k]
  have hN1 : 1 < cfg.N k := by linarith [hN k]
  have hKk := hK k
  set H := depthDataAt cfg k s with hHdef
  have hclust : ClusterOracle H.a H.d (cfg.N k ^ η) (cfg.N k ^ (-(ε₁ / 2))) :=
    clusterOracle_of hN1 (hCS (cfg.N k) hNk)
  have hZσ : 1 < cfg.N k ^ ε₁ * cfg.N k ^ (-(ε₁ / 2)) := by
    rw [← Real.rpow_add hN0]
    exact Real.one_lt_rpow hN1 (by linarith)
  have hθ : 0 < cfg.N k ^ (-(η / 2)) := Real.rpow_pos_of_pos hN0 _
  have hlm := light_mass_le H hH (goodSet H.b H.K H.χ) (measurableSet_goodSet hH.hb _ _)
    subset_rfl (hsupp H hH) hclust hc1 hc2 hZσ hθ (Real.rpow_pos_of_pos hN0 _)
  refine hlm.trans (ENNReal.ofReal_le_ofReal ?_)
  -- numerics
  show 16 * cfg.K k ^ 2 / (cfg.N k ^ η * cfg.N k ^ (-(η / 2))) +
      cfg.K k * cfg.N k ^ (-(η / 2)) ≤ cfg.N k ^ (-(η / 4))
  have e1 : cfg.N k ^ η * cfg.N k ^ (-(η / 2)) = cfg.N k ^ (η / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have e2 : cfg.N k ^ (-(η / 2)) = (cfg.N k ^ (η / 2))⁻¹ := Real.rpow_neg hN0.le _
  have e3 : cfg.N k ^ (-(η / 4)) = cfg.N k ^ (η / 4) / cfg.N k ^ (η / 2) := by
    rw [← Real.rpow_sub hN0]; ring_nf
  have hpos : 0 < cfg.N k ^ (η / 2) := Real.rpow_pos_of_pos hN0 _
  rw [e1, e2, e3]
  have hKK : cfg.K k ≤ cfg.K k ^ 2 := by nlinarith
  rw [div_eq_mul_inv, div_eq_mul_inv, ← add_mul]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hpos.le)
  nlinarith

/-- The good labels carry all the current mass at every large index. -/
theorem eventually_goodSet_conull (cfg : Data α) (hK : ∀ k, 1 ≤ cfg.K k) (hbasic : cfg.Basic) (hatlas : cfg.Atlas)
    {s : ℝ} (hs0 : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, cfg.ρ k (Prod.fst ⁻¹' goodSet (cfg.b k) (cfg.K k) (cfg.N k ^ (-cfg.e₀)))ᶜ = 0 := by
  have hR1 : 1 < s + s⁻¹ + 2 := by have := inv_pos.mpr hs0; linarith
  have hsR := range_of_inv (R := s + s⁻¹ + 2) hs0 (by have := inv_pos.mpr hs0; linarith)
    (by linarith)
  filter_upwards [hatlas _ hR1] with k hatl
  obtain ⟨hb, hν, hπ, hμν, hρμ, hμsupp, hρmass, -, hbase, hpoly⟩ := hbasic k
  obtain ⟨-, -, -, -, A5, A6, -⟩ := hatl s hsR.1 hsU
  have hKk := hK k
  -- the index set is not empty
  have hn : 0 < cfg.n k s := by
    by_contra h0
    push_neg at h0
    have hn0 : cfg.n k s = 0 := by omega
    have hμ0 : cfg.μ k univ = 0 := by
      rw [ae_iff] at A6
      have : {p : α × ℝ | ¬∃ i, p.1 ∈ cfg.B k s i ∧
          p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i)} = univ := by
        ext p
        simp only [mem_setOf_eq, mem_univ, iff_true, not_exists, not_and]
        intro i
        exact absurd i.isLt (by omega)
      rw [this] at A6
      exact A6
    have h1 := hρmass.trans (hρμ univ)
    rw [hμ0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
    have : 0 < (cfg.K k)⁻¹ := inv_pos.mpr (by linarith)
    linarith
  set i₀ : Fin (cfg.n k s) := ⟨0, hn⟩
  have hhor := (A5 i₀).2.2.2.2.2.2.2.2 rfl
  have hP : cfg.P k = MvPolynomial.X 3 := hhor.1
  -- the base bound transfers from the prior to the current law
  have hbaseμ : ∀ᵐ p ∂cfg.μ k,
      |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k := by
    have hm : MeasurableSet {p : α × ℝ |
        |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k} :=
      measurableSet_le (f := fun p : α × ℝ =>
        |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4|)
        (by fun_prop) measurable_const
    have hprod : ∀ᵐ (p : α × ℝ) ∂(cfg.ν k).prod volume,
        |cfg.b k p.1 0| + |cfg.b k p.1 1| + |cfg.b k p.1 3| + |cfg.b k p.1 4| ≤ cfg.K k := by
      apply (Measure.ae_prod_iff_ae_ae hm).mpr
      filter_upwards [hbase] with l hl
      exact Filter.Eventually.of_forall (fun _ => hl)
    exact (Measure.absolutelyContinuous_of_le_smul hμν).ae_le hprod
  have hgoodμ : ∀ᵐ p ∂cfg.μ k, p.1 ∈ goodSet (cfg.b k) (cfg.K k) (cfg.N k ^ (-cfg.e₀)) := by
    filter_upwards [hbaseμ, hhor.2.1, hpoly] with p h1 h2 h3
    have h0 := (h3.1 0 (by simp)).1
    have h1' := (h3.1 1 (by simp)).1
    rw [hP, MvPolynomial.eval_X, x_three] at h0 h1'
    simp only [X3, zero_mul, add_zero, one_mul] at h0 h1'
    exact ⟨h1, h2, h0, h1'⟩
  rw [ae_iff] at hgoodμ
  apply le_antisymm _ bot_le
  calc cfg.ρ k (Prod.fst ⁻¹' goodSet (cfg.b k) (cfg.K k) (cfg.N k ^ (-cfg.e₀)))ᶜ
      ≤ cfg.μ k (Prod.fst ⁻¹' goodSet (cfg.b k) (cfg.K k) (cfg.N k ^ (-cfg.e₀)))ᶜ := hρμ _
    _ = 0 := by
        have : (Prod.fst ⁻¹' goodSet (cfg.b k) (cfg.K k) (cfg.N k ^ (-cfg.e₀)))ᶜ =
            {p : α × ℝ | ¬p.1 ∈ goodSet (cfg.b k) (cfg.K k) (cfg.N k ^ (-cfg.e₀))} := by
          ext p; simp
        rw [this]
        exact hgoodμ

end

end Submission.Obl.k4_horizontal_coefficient_count
