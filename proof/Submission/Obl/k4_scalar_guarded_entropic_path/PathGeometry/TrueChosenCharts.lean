/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/TrueChosenCharts.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_normalized_exact_refinement.ChosenCharts
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.TrueSaturation

/-! Select a supplied true atlas without losing its true floors.
The diagonal selection follows the accepted o166 ChartSelection proof,
using its Bool-polymorphic prior-pruning lemma with the flag true.
Adapted from: here:o166, ChartSelection.lean, accepted lib336f0b704ef5. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Filter
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split
open Submission.Obl.k4_scalar_normalized_exact_refinement

noncomputable section

private theorem chartData_forgetTrue {p : Code} {B k T n : ℕ} {r b h ε : ℝ}
    {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Line} {C : Fin n → Set (Line × ℝ)} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hc : ChartData p B r b h ε true k T n γ j A C u v J P Λ) :
    ChartData p B r b h ε false k T n γ j A C u v J P Λ := by
  rcases hc with ⟨hT, hn, hm, hd, hs, hp, hcard, hmeas, hlist, hmass⟩
  refine ⟨hT, hn, hm, hd, hs, ?_, hcard, hmeas, hlist, hmass⟩
  intro i
  rcases hp i with ⟨a, b, c, d, e, f, g, h, j, k, l, _⟩
  exact ⟨a, b, c, d, e, f, g, h, j, k, l, by simp⟩

def TrueKnown (p : Code) (r b h : ℝ) : Prop :=
  0 ≤ h ∧ ∃ B : ℕ, 1 ≤ B ∧ ∀ ε : ℝ, 0 < ε →
    ∃ᶠ k in atTop, Chart p B r b (h + ε) ε true k

structure TrueChosenCharts (p : Code) (r b h : ℝ) extends ChosenCharts p r b h where
  true_data : ∀ k, ChartData p B r b (h + ε k) (ε k) true (φ k) (T k) (n k)
    (γ k) (j k) (A k) (C k) (u k) (v k) (J k) (P k) (Λ k)

private def PrunedTrueChart (p : Code) (B : ℕ) (r b h ε : ℝ) (k : ℕ) : Prop :=
  ∃ (T n : ℕ) (γ : Fin n → Fin (W p k)) (j : Fin n → Fin (2 ^ T))
    (A : Fin n → Set Line) (C : Fin n → Set (Line × ℝ))
    (u v J : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ)
    (Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)),
    ChartData p B r b h ε true k T n γ j A C u v J P Λ ∧
      ∀ i, N p k ^ (-((B : ℝ) + 2)) ≤ (ν p k (γ i) (A i)).toReal

/-- One strict subsequence of the given true charts retains true floors
and the polynomial lower cutoff on every full assigned prior. -/
theorem nonempty_true_chosen_charts {p : Code} {r b h : ℝ}
    (hp : Exact p) (hk : TrueKnown p r b h) : Nonempty (TrueChosenCharts p r b h) := by
  classical
  obtain ⟨_, B, hB, hknown⟩ := hk
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε0 n : 0 < ε n := by dsimp [ε]; positivity
  have hε1 n : ε n ≤ 1 := by
    dsimp [ε]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hf n : ∃ᶠ k in atTop, PrunedTrueChart p B r b (h + ε n) (ε n) k := by
    have hη : 0 < ε n / 2 := by positivity
    have hg : ∀ᶠ k in atTop, 2 ≤ N p k ^ (ε n / 2) :=
      ((tendsto_rpow_atTop hη).comp hp.1.2.1).eventually (eventually_ge_atTop 2)
    apply ((hknown (ε n / 2) hη).and_eventually hg).mono
    intro k hk
    obtain ⟨T, m, γ, j, A, C, u, v, J, P, Λ, hd⟩ := hk.1
    obtain ⟨m', e, he, hd'⟩ := chartData_prune_prior (hp.1.1 k) hη.le
      (by linarith [hε1 n]) hk.2 (fun g => ((hp.2.1 k).2.2.2.1 g).1)
      (hp.2.1 k).2.1 (hp.2.1 k).2.2.1 hd
    refine ⟨T, m', γ ∘ e, j ∘ e, A ∘ e, C ∘ e, u ∘ e, v ∘ e, J ∘ e, P ∘ e,
      restrictedChartList e Λ, ?_, he⟩
    convert hd' using 1 <;> ring
  obtain ⟨φ, hφ, hcharts⟩ := extraction_forall_of_frequently hf
  choose T n γ j A C u v J P Λ hd hprior using hcharts
  let a : ChosenCharts p r b h :=
      { B := B
        B_pos := hB
        φ := φ
        φ_mono := hφ
        ε := ε
        ε_pos := hε0
        ε_lim := tendsto_one_div_add_atTop_nhds_zero_nat
        ε_le_one := hε1
        T := T
        n := n
        γ := γ
        j := j
        A := A
        C := C
        u := u
        v := v
        J := J
        P := P
        Λ := Λ
        data := fun k => chartData_forgetTrue (hd k)
        prior_lower := hprior }
  exact ⟨{ toChosenCharts := a, true_data := hd }⟩

end

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
