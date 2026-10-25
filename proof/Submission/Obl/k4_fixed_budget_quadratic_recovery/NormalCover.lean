import Submission.Obl.k4_fixed_budget_quadratic_recovery.Cover
import Submission.Obl.k4_fixed_budget_quadratic_recovery.Numerics
import Submission.Obl.k4_finite_width_output_exclusion.ChartTransport

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Set Filter

/-- The geometric cover with its final coefficient and fixed Boolean-format budgets.
The positive fit exponent and an upper bound on all internal losses are supplied first. -/
theorem finite_scalar_fit_cover_normalized
    (hmesh : ScalarMeshProjection)
    {d s m S U c κ ε : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hs : 0 < s) (hs1 : s < 1) (hsm : s < m) (hS : 0 < S)
    (hU : 0 < U) (hUm : U < m) (hcs : c < s)
    (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ κ ∧ δ ≤ ε / 100 ∧
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ δ ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ η : ℝ, η ≤ η₀ →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (μ : Measure (α × ℝ))
        (b : α → Fin 5 → ℝ),
        ScalarAdmissible N η d s m 1 S U 1 ν b μ →
        ∃ (n : ℕ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
          (A : Fin n → Set (Fin 5 → ℝ)),
          (n : ℝ) ≤ N ^ (d * s + ε) ∧
          (∀ i, (P i).totalDegree ≤ 2 ∧
            (∀ e, |(P i).coeff e| ≤ N ^ ε) ∧
            MeasurableSet (A i) ∧ fmt 5 (N ^ (7 : ℕ)) 4 (A i) ∧
            A i ⊆ scalarFit (P i) (N ^ δ * N ^ (-s))) ∧
          Pairwise (fun i j => Disjoint (A i) (A j)) ∧
          μ.real {p | ¬ ∃ i, b p.1 ∈ A i} < N ^ (-η₀) ∧
          2 * (N ^ δ * N ^ (-s)) ≤ N ^ (-c) := by
  let δ := min κ (min (ε / 100) ((s - c) / 100))
  have hδ : 0 < δ := lt_min hκ (lt_min (by positivity) (by linarith))
  have hδκ : δ ≤ κ := min_le_left _ _
  have hδε : δ ≤ ε / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ ≤ (s - c) / 100 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨η₁, hη₁, R, hR, hcover⟩ :=
    finite_scalar_fit_cover_residual hmesh hd hd1 hs hsm hS hU hUm hδ
  let η₀ := min η₁ δ
  have hη₀ : 0 < η₀ := lt_min hη₁ hδ
  have hcoef : ∀ᶠ N : ℝ in atTop, 240 * N ^ (5 * δ) ≤ N ^ ε :=
    eventually_const_mul_rpow_le 240 (by linarith)
  have hfit : ∀ᶠ N : ℝ in atTop, 2 * N ^ (δ - s) ≤ N ^ (-c) :=
    eventually_const_mul_rpow_le 2 (by linarith)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((hcoef.and hfit).and (eventually_ge_atTop R))
  refine ⟨δ, hδ, hδκ, hδε, η₀, hη₀, min_le_right _ _, max 2 N₀,
    le_max_left _ _, ?_⟩
  intro N hN η hη α _ ν μ b hadm
  have hNN₀ : N₀ ≤ N := (le_max_right _ _).trans hN
  obtain ⟨⟨hcoefN, hfitN⟩, hNR⟩ := hN₀ N hNN₀
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hηδ : η ≤ δ := hη.trans (min_le_right _ _)
  obtain ⟨n, P, A, hn, hP, hdisj, hres⟩ :=
    hcover N hNR η (hη.trans (min_le_left _ _)) α ν μ b hadm
  have hn' : (n : ℝ) ≤ N ^ (d * s + ε) := hn.trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hfcount : (n : ℝ) * 24 ≤ N ^ (7 : ℕ) :=
    scalar_format_count hN2 hd hd1 hs hs1 hε1 hn'
  have hpow : (N ^ δ) ^ (5 : ℕ) = N ^ (5 * δ) := by
    rw [← Real.rpow_mul_natCast hN0.le]
    congr 1
    ring
  refine ⟨n, P, A, hn', ?_, hdisj, ?_, ?_⟩
  · intro i
    obtain ⟨hdeg, hcoeff, hmeas, hformat, hfit⟩ := hP i
    refine ⟨hdeg, fun e => (hcoeff e).trans ?_, hmeas, ?_, hfit⟩
    · rwa [hpow]
    · exact Submission.Obl.k4_finite_width_output_exclusion.fmt_mono hfcount hformat
  · exact hres.trans_le (Real.rpow_le_rpow_of_exponent_le hN1
      (neg_le_neg (min_le_left _ _)))
  · simpa only [sub_eq_add_neg, Real.rpow_add hN0] using hfitN

end Submission.Obl.k4_fixed_budget_quadratic_recovery
