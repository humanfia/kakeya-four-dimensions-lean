import Submission.Obl.k4_scalar_normalized_exact_refinement.ChartWorld

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Filter
open k4_scalar_linear_critical_extremizers.Split

noncomputable section

structure ChosenCharts (p : Code) (r b h : ℝ) where
  B : ℕ
  B_pos : 1 ≤ B
  φ : ℕ → ℕ
  φ_mono : StrictMono φ
  ε : ℕ → ℝ
  ε_pos : ∀ k, 0 < ε k
  ε_lim : Tendsto ε atTop (nhds 0)
  ε_le_one : ∀ k, ε k ≤ 1
  T : ℕ → ℕ
  n : ℕ → ℕ
  γ : (k : ℕ) → Fin (n k) → Fin (W p (φ k))
  j : (k : ℕ) → Fin (n k) → Fin (2 ^ T k)
  A : (k : ℕ) → Fin (n k) → Set Line
  C : (k : ℕ) → Fin (n k) → Set (Line × ℝ)
  u : (k : ℕ) → Fin (n k) → ℝ
  v : (k : ℕ) → Fin (n k) → ℝ
  J : (k : ℕ) → Fin (n k) → ℝ
  P : (k : ℕ) → Fin (n k) → MvPolynomial (Fin 2) ℝ
  Λ : (k : ℕ) → Fin (W p (φ k)) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin (n k))
  data : ∀ k, ChartData p B r b (h + ε k) (ε k) false (φ k) (T k) (n k)
    (γ k) (j k) (A k) (C k) (u k) (v k) (J k) (P k) (Λ k)
  prior_lower : ∀ k i, N p (φ k) ^ (-((B : ℝ) + 2)) ≤
    (ν p (φ k) (γ k i) (A k i)).toReal

namespace ChosenCharts

theorem nonempty {p : Code} {r b h : ℝ} (hp : Spec.RawScalar p) (hk : Known p r b h) :
    Nonempty (ChosenCharts p r b h) := by
  classical
  obtain ⟨φ, ε, B, hφ, hε0, hεlim, hε1, hB, hcharts⟩ := known_pruned_sequence
    hp.1.1 hp.1.2.1 (fun k g => ((hp.2 k).2.2.2.1 g).1)
    (fun k => (hp.2 k).2.1) (fun k => (hp.2 k).2.2.1) hk
  choose T n γ j A C u v J P Λ hd hprior using hcharts
  exact ⟨⟨B, hB, φ, hφ, ε, hε0, hεlim, hε1, T, n, γ, j, A, C, u, v, J, P, Λ, hd, hprior⟩⟩

variable {p : Code} {r b h : ℝ} (a : ChosenCharts p r b h)

def dt (k : ℕ) : ℝ := ((2 : ℝ) ^ a.T k)⁻¹
def t₀ (k : ℕ) (i : Fin (a.n k)) : ℝ := ((a.j k i : ℕ) : ℝ) * a.dt k
def δ (k : ℕ) : ℝ := N p (a.φ k) ^ (-r)
def θ (k : ℕ) (i : Fin (a.n k)) : Line → Line :=
  normalizeLine (a.P k i) (a.t₀ k i) (a.dt k) (a.u k i) (a.v k i) (a.J k i) (a.δ k)
def Φ (k : ℕ) (i : Fin (a.n k)) : Line × ℝ → Line × ℝ :=
  fun z => (a.θ k i z.1, (z.2 - a.t₀ k i) / a.dt k)
def prior (k : ℕ) (i : Fin (a.n k)) : Measure Line :=
  chartPrior (ν p (a.φ k) (a.γ k i)) (a.A k i) (a.P k i)
    (a.t₀ k i) (a.dt k) (a.u k i) (a.v k i) (a.J k i) (a.δ k)
def event (k : ℕ) (i : Fin (a.n k)) : Set (Line × ℝ) :=
  a.Φ k i '' a.C k i
def budget (k : ℕ) (i : Fin (a.n k)) : ℝ :=
  ω p (a.φ k) (a.γ k i) * a.dt k * (ν p (a.φ k) (a.γ k i) (a.A k i)).toReal
def Z (k : ℕ) : ℝ := ∑ i, a.budget k i
def weight (k : ℕ) (i : Fin (a.n k)) : ℝ := a.budget k i / a.Z k

def code (M' D' : ℕ) (d' : ℝ) : Code :=
  ⟨a.n, (fun k => N p (a.φ k)), (fun k => 8 * N p (a.φ k) ^ a.ε k), M', D',
    L p - r, d', S p, U p * (L p - r) / L p, a.weight, a.prior, a.event,
    (fun _ _ _ _ => 0), (fun _ _ _ _ => 0), (fun _ => 0)⟩

lemma dt_pos (k : ℕ) : 0 < a.dt k := by unfold dt; positivity
lemma δ_pos (hp : Spec.RawScalar p) (k : ℕ) : 0 < a.δ k :=
  Real.rpow_pos_of_pos (by have hN : 2 ≤ N p (a.φ k) := hp.1.1 _; linarith) _
lemma dt_le_one (k : ℕ) : a.dt k ≤ 1 := by
  unfold dt
  simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ a.T k)

lemma selected_subset (k : ℕ) (i : Fin (a.n k)) :
    a.C k i ⊆ a.A k i ×ˢ Set.Icc (a.t₀ k i) (a.t₀ k i + a.dt k) := by
  intro z hz
  simpa only [t₀, dt, I, div_eq_mul_inv, add_mul, one_mul] using ((a.data k).2.2.2.2.1 i hz).2

lemma selected_budget (k : ℕ) (i : Fin (a.n k)) :
    mu p (a.φ k) (a.γ k i) (a.C k i) ≤
      ENNReal.ofReal (a.dt k) * ν p (a.φ k) (a.γ k i) (a.A k i) :=
  selected_mass_le_assignment _ _ Measure.restrict_le_self _ _ _ _ (a.selected_subset k i)

lemma Z_pos (hp : Spec.RawScalar p) (k : ℕ) : 0 < a.Z k := by
  exact assignment_normalizer_positive (ν p (a.φ k)) (mu p (a.φ k)) (ω p (a.φ k))
    (a.γ k) (a.A k) (a.C k) (a.dt k)
    (fun g => ((hp.2 (a.φ k)).2.2.2.1 g).1) (hp.2 (a.φ k)).2.1
    (a.dt_pos k).le (a.selected_budget k)
    (Real.rpow_pos_of_pos (by have hN : 2 ≤ N p (a.φ k) := hp.1.1 _; linarith) _) (a.data k).2.2.2.2.2.2.2.2.2

lemma Z_le_one (hp : Spec.RawScalar p) (k : ℕ) : a.Z k ≤ 1 := by
  apply assignment_normalizer_le_one (ν p (a.φ k)) (ω p (a.φ k)) (a.γ k) (a.j k) (a.A k)
    (a.dt k) (a.dt_pos k).le
  · simp only [dt, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    exact inv_mul_cancel₀ (by positivity)
  · exact fun g => ((hp.2 (a.φ k)).2.2.2.1 g).1
  · exact (hp.2 (a.φ k)).2.1
  · exact (hp.2 (a.φ k)).2.2.1
  · exact fun i => ((a.data k).2.2.1 i).1
  · exact (a.data k).2.2.2.1

lemma weights_probability (hp : Spec.RawScalar p) (k : ℕ) :
    (∀ i, 0 ≤ a.weight k i) ∧ ∑ i, a.weight k i = 1 := by
  apply normalized_assignment_weights (a.budget k)
  · intro i
    exact mul_nonneg (mul_nonneg ((hp.2 (a.φ k)).2.1 _) (a.dt_pos k).le) ENNReal.toReal_nonneg
  · exact a.Z_pos hp k

end ChosenCharts

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
