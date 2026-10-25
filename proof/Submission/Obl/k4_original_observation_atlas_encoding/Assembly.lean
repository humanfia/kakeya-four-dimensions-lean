import Submission.Obl.k4_original_observation_atlas_encoding.Analytic
import Submission.Obl.k4_original_observation_atlas_encoding.Format
import Submission.Obl.k4_original_observation_atlas_encoding.Numerics

namespace Submission.Obl.k4_original_observation_atlas_encoding

open MeasureTheory Set Finset
open scoped ENNReal
open Submission.Lib.K4XInterface
open Submission.Lib.K4ModelReduction (densityL1Distance)
open Submission.Obl.k4_native_base_flattening (uniform_native_flattening baseCoordinates)
open Submission.Obl.k4_horizon_light_cell_mass

theorem encoding :
    ∀ L : ℝ, 0 < L → ∀ Mν Dν M D : ℕ,
    ∃ M' D' : ℕ, M ≤ M' ∧ D ≤ D' ∧ ∀ τ : ℝ, 0 < τ →
    ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    ∀ (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
      (B : Fin W → ℝ) (E : Fin W → Set State),
    temperedLaw N Mν Dν W ω ν B →
    ∀ (ε r : ℝ) (T C : ℕ) (γ : Fin C → Fin W) (j : Fin C → Fin (2 ^ T))
      (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
      (R : Fin C → MvPolynomial (Fin 4) ℝ) (A : Fin C → Set (ℕ × (Fin 6 → ℝ)))
      (F : Fin C → Set State) (lst : Fin W → Observation → Finset (Fin C)),
    0 < ε → ε ≤ τ / 4 → ε ≤ 1 / 8 → (C : ℝ) ≤ N ^ M →
    (∀ w o, ((lst w o).card : ℝ) ≤ N ^ ε) →
    (∀ w b, MeasurableSet {o | b ∈ lst w o}) →
    (∀ b, gchart N M D (N ^ ε) T (j b : ℝ) r (B (γ b)) (E (γ b))
      (c b) (u b) (Q b) (R b) (A b) (F b) True) →
    ENNReal.ofReal (N ^ (-ε)) ≤ ∑ b, ENNReal.ofReal (ω (γ b)) *
      ((ν (γ b)).prod volume) {p | p ∈ F b ∧ b ∈ lst (γ b) (gobs (B (γ b)) (gδ N L) p)} →
    ∃ (F' : Fin C → Set State) (lst' : Fin W → Observation → Finset (Fin C)),
      (∀ b, F' b ⊆ F b) ∧
      (∀ w o, ((lst' w o).card : ℝ) ≤ N ^ τ) ∧
      (∀ b, gchart N M' D' (N ^ τ) T (j b : ℝ) r (B (γ b)) (E (γ b))
        (c b) (u b) (Q b) (R b) (A b) (F' b)
          (∀ p ∈ F' b, b ∈ lst' (γ b) (gobs (B (γ b)) (gδ N L) p))) ∧
      ENNReal.ofReal (N ^ (-τ)) ≤ ∑ b, ENNReal.ofReal (ω (γ b)) *
        ((ν (γ b)).prod volume) (F' b) := by
  classical
  intro L hL Mν Dν M D
  obtain ⟨H, hH⟩ := uniform_native_flattening (max Mν M) (max Dν D) (M + 2)
  let Z := H + Mν + M + ⌈|L|⌉₊ + 2
  let M' := M + 4 * Z + 20
  refine ⟨M', max D 2, (by dsimp [M']; omega), le_max_left _ _, ?_⟩
  intro τ hτ
  obtain ⟨N₀, hN₀, hretain⟩ := mass_retention_cutoff τ hτ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hNN W ω ν B E hlaw ε r T C γ j c u Q R A F lst hε hετ hε1 hC hlst hlstm hchart hsuccess
  have hN : 2 ≤ N := hN₀.trans hNN
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  obtain ⟨hW, hω, hωsum, hprior⟩ := hlaw
  have hsource (b : Fin C) := source_of_chart hN (ν (γ b)) (hprior (γ b)).2.2.2.2
    (j b) (hchart b)
  choose f hf hfm hf0 hfb hraw using hsource
  choose g hgm hgb hgc hgs hge using fun b => hH N hN (f b) (hf b)
  let ρ : ℝ := (N ^ H)⁻¹
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hcell (b : Fin C) : ∀ x y, (∀ i ∉ baseCoordinates, x i = y i) →
      (∀ i ∈ baseCoordinates, ⌊x i / ρ⌋ = ⌊y i / ρ⌋) → g b x = g b y := by
    intro x y ho hb
    apply hgc b x y ho
    intro i hi
    simpa only [ρ, div_inv_eq_mul, mul_comm] using hb i hi
  have hLK (w : Fin W) (o : Observation) : (lst w o).card ≤ ⌊N ^ ε⌋₊ := Nat.le_floor (hlst w o)
  obtain ⟨table, ht, hs⟩ := recover_original_family ω hω hωsum γ B (gδ N L) ρ hρ
    (fun b => (ν (γ b)).prod volume) F f g hfm hgm hf0 (fun b x => (hgb b x).1)
    hraw hcell ⌊N ^ ε⌋₊ lst hlstm hLK
  let lst' : Fin W → Observation → Finset (Fin C) :=
    fun w o => table w (meshCode ![ρ, ρ, ρ] o)
  let F' : Fin C → Set State :=
    fun b => {p | p ∈ F b ∧ b ∈ lst' (γ b) (pureMap (B (γ b)) (gδ N L) p)}
  have hlst'm (w : Fin W) (b : Fin C) : MeasurableSet {o | b ∈ lst' w o} :=
    (meshCode_measurable _) ((Set.to_countable {c | b ∈ table w c}).measurableSet)
  have hκ : N ^ ε ≤ N ^ τ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine ⟨F', lst', (fun b p hp => hp.1), ?_, ?_, ?_⟩
  · intro w o
    exact (show ((lst' w o).card : ℝ) ≤ (⌊N ^ ε⌋₊ : ℝ) by exact_mod_cast ht w _).trans
      ((Nat.floor_le (Real.rpow_nonneg hN0.le _)).trans hκ)
  · intro b
    have htime : ∀ p ∈ F b, p.2 ∈ Icc (0 : ℝ) 1 := fun p hp => (chart_time_subset (j b) (hchart b) hp).2
    have hbd := chart_coeff_bound (hchart b)
    have hfmt' (i : ℕ) : gfmt 7 (N ^ M') (max D 2)
        {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ F' b} := by
      obtain ⟨_, _, _, _, _, _, _, _, hfmt, _⟩ := hchart b
      exact selected_fiber_format hN M Mν H ⌈|L|⌉₊ D (hprior (γ b)).2.1.le
        (hprior (γ b)).2.2.1 (gδ_pos N L) (inv_delta_le hN L) i (hfmt i).2
        htime hbd (table (γ b)) b
    have hwide := gchart_mono (hchart b) hN1 (show M ≤ M' by dsimp [M']; omega)
      (le_max_left D 2) (Real.rpow_pos_of_pos hN0 ε) hκ (hprior (γ b)).2.1.le (fun _ => True.intro)
    obtain ⟨hQ, hcu, hQQ, hQs, hdeg, hcoef, hmA, hmF, hfmt, hAl, hFp, _⟩ := hwide
    have hmF' : MeasurableSet (F' b) :=
      hmF.inter ((hlst'm (γ b) b).preimage (pureMap_measurable (B (γ b)) (gδ N L)))
    exact ⟨hQ, hcu, hQQ, hQs, hdeg, hcoef, hmA, hmF',
      fun i => ⟨(hfmt i).1, hfmt' i⟩, hAl, fun p hp => hFp p hp.1, fun p hp => hp.2⟩
  · apply hretain N hNN ε hετ hε1
    have herr := sum_error_bound hN0 M C hC
      (fun b => densityL1Distance volume (g b) (f b)) hge
    exact hsuccess.trans (hs.trans (add_le_add le_rfl (mul_le_mul_right herr 2)))

end Submission.Obl.k4_original_observation_atlas_encoding
