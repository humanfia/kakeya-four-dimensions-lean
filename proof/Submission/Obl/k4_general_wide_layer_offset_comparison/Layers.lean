import Submission.Obl.k4_general_wide_layer_offset_comparison.ExponentChoice
import Submission.Obl.k4_general_parent_projected_layers.Layers
import Submission.Obl.k4_general_parent_projected_layers.Raw
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.StripCoeff

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Filter Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

/-- A projected layer retains its original floors and total reference budget. -/
def LayerValid {α : Type} [MeasurableSpace α] (p : Parameters) (M : PreparedModel α)
    (k : ℕ) (s m H : ℝ) (L : ProjLayer α) : Prop :=
  L.Good (p.N k) H p.d p.ell 0 s (p.N k ^ (-m)) (M.b k) (M.P k) (M.pi k) (M.rho k) ∧
    (∑ i, L.weight (p.N k) p.d s (p.N k ^ (-m)) (M.pi k) i) ≤ ENNReal.ofReal H

/-- The depth of the coarse layer and the two fine colors. -/
def depth (r u v : ℝ) : Fin 3 → ℝ := ![r, r + u, r + v]

/-- Before the loss is chosen, a single cofinal sequence carries all three actual
wide layers. Enlarging its intrinsic loss by two also supplies the bound `2 ≤ H`. -/
theorem exists_three_layers {α : Type} [MeasurableSpace α]
    (p : Parameters) (M : PreparedModel α) (hp : p.Valid)
    (hwide : RawLayer p.N p.K p.d p.ell p.U M.rho M.pi M.b M.P M.x true)
    {Ucap : ℝ} (hcap : 0 < Ucap) :
    ∃ (τ : ℕ → ℕ), StrictMono τ ∧ ∃ r u v m : ℝ,
      ComparisonExponents p.d p.kappa p.ell p.U r u v m ∧ m ≤ Ucap ∧
      ∃ (H : ℕ → ℝ) (σ : ℕ → Measure (α × ℝ)) (L : ℕ → Fin 3 → ProjLayer α),
        (∀ k, 2 ≤ H k ∧ p.K (τ k) ≤ H k) ∧
        (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N (τ k) ^ ε) ∧
        (∀ k, σ k ≤ M.rho (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ σ k univ) ∧
        (∀ k a, LayerValid p M (τ k) (depth r u v a) m (H k) (L k a)) ∧
        (∀ k a, ∀ᵐ ω ∂σ k, ω ∈ (L k a).covered) := by
  classical
  obtain ⟨hN, hNt, hK, hd, hd1, hκ, hκ1, hℓ, hS, hS1, hU, he⟩ := hp
  obtain ⟨C, hC, hwide⟩ := hwide
  obtain ⟨r, u, v, m, hexp, hmcap, hrU, hrm⟩ :=
    exists_comparison_exponents hd hd1 hκ hℓ hU hC hcap
  have hdepth : ∀ a, r ≤ depth r u v a ∧ depth r u v a ≤ 2 * r := by
    intro a
    fin_cases a <;> constructor <;> dsimp [depth] <;> linarith [hexp.1.1, hexp.1.2.1,
      hexp.1.2.2.1, hexp.2.1, hexp.2.2.1]
  let D : Finset ℝ := Finset.univ.image (depth r u v)
  have hD : ∀ s ∈ D, r ≤ s ∧ s ≤ 2 * r := by
    intro s hs
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hs
    exact hdepth a
  obtain ⟨τ, hτ, H, hH, hHsub, σ, β, n, C', tag, u', v', G, hσ, hlayers⟩ :=
    hwide r hexp.1.1 (by simpa using hrU) D hD m hrm
  let HH : ℕ → ℝ := fun k => 2 * H k
  have hHH : ∀ k, H k ≤ HH k := fun k => by dsimp [HH]; linarith [(hH k).1]
  have hHpos : ∀ k, 0 < H k := fun k => by linarith [(hH k).1]
  let LL : ℕ → Fin 3 → ProjLayer α := fun k a =>
    ⟨n k (depth r u v a), β k (depth r u v a), C' k (depth r u v a),
      tag k (depth r u v a), u' k (depth r u v a), v' k (depth r u v a),
      G k (depth r u v a)⟩
  refine ⟨τ, hτ, r, u, v, m, hexp, hmcap, HH, σ, LL, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ⟨by dsimp [HH]; linarith [(hH k).1], (hH k).2.trans (hHH k)⟩
  · intro ε hε
    have hbig := Submission.Obl.k4_profile_density_bounds.eventually_const_mul_rpow_lt
      (hNt.comp hτ.tendsto_atTop) (a := 0) (b := ε / 2) (by linarith) 2
    filter_upwards [hHsub (ε / 2) (by positivity), hbig] with k hk hb
    simp only [Real.rpow_zero, mul_one] at hb
    calc HH k = 2 * H k := rfl
      _ ≤ p.N (τ k) ^ (ε / 2) * p.N (τ k) ^ (ε / 2) := by
        exact mul_le_mul hb.le hk (hHpos k).le
          (Real.rpow_nonneg (by linarith [hN (τ k)]) _)
      _ = p.N (τ k) ^ ε := by
        rw [← Real.rpow_add (by linarith [hN (τ k)] : 0 < p.N (τ k))]
        congr 1
        ring
  · intro k
    exact ⟨(hσ k).1, (ENNReal.ofReal_le_ofReal (inv_anti₀ (hHpos k) (hHH k))).trans
      (hσ k).2⟩
  · intro k a
    have hsD : depth r u v a ∈ D := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    obtain ⟨hβ, hβlo, hβhi, hmeas, hdisj, hi, hbudget, hcover⟩ := hlayers k _ hsD
    have hg : (LL k a).Good (p.N (τ k)) (H k) p.d p.ell 0 (depth r u v a)
        (p.N (τ k) ^ (-m)) (M.b (τ k)) (M.P (τ k)) (M.pi (τ k)) (M.rho (τ k)) := by
      simpa [ProjLayer.Good, LL] using
        And.intro hβ (And.intro hβlo (And.intro hβhi
          (And.intro hmeas (And.intro hdisj hi))))
    refine ⟨hg.mono (by linarith [hN (τ k)]) (hHpos k) (hHH k)
      (Real.rpow_nonneg (by linarith [hN (τ k)]) _), ?_⟩
    exact hbudget.trans (ENNReal.ofReal_le_ofReal (hHH k))
  · intro k a
    exact (hlayers k _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)).2.2.2.2.2.2.2

end

end Submission.Obl.k4_general_wide_layer_offset_comparison
