import Mathlib
import ChallengeDeps

open Filter Set
open scoped Topology

/-- Compactness of the finite exponent profile, from the proof developed for o055. -/
theorem Submission.k4_matching_profile_compactness :
  ∀ (q : ℕ) (s : ℝ), 0 ≤ s → ∀ P : (ℕ → ℝ) → ℝ → ℝ → Prop, (∀ (u v : ℕ → ℝ) (ε δ N : ℝ), 0 < ε → 0 < δ → 2 ≤ N → (∀ k : ℕ, k ≤ q → |u k - v k| ≤ δ) → P u ε N → P v (ε + 2 * δ) N) → (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ ∃ u : ℕ → ℝ, ((∀ k : ℕ, k ≤ q → 0 ≤ u k) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b) ∧ u q ≤ s + ε) ∧ P u ε N) → ∃ u : ℕ → ℝ, ((∀ k : ℕ, k ≤ q → 0 ≤ u k) ∧ (∀ a b : ℕ, a ≤ b → b ≤ q → u a ≤ u b) ∧ u q ≤ s) ∧ (∀ ε : ℝ, 0 < ε → ∀ R : ℝ, 2 ≤ R → ∃ N : ℝ, R ≤ N ∧ P u ε N) := by
  classical
  intro q s hs P hstable happ
  let τ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hτpos (n : ℕ) : 0 < τ n := by dsimp [τ]; positivity
  have hτone (n : ℕ) : τ n ≤ 1 := by
    dsimp [τ]
    apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).2
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hτlim : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose N hN v hv hPv using
    (fun n : ℕ => happ (τ n) (hτpos n) ((n : ℝ) + 2) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  let z : ℕ → Fin (q + 1) → ℝ := fun n i => v n i.val
  have hz (n : ℕ) : z n ∈ Icc (0 : Fin (q + 1) → ℝ) (fun _ => s + 1) := by
    constructor
    · intro i
      exact (hv n).1 i (by omega)
    · intro i
      have hh := (hv n).2.1 i q (by omega) le_rfl
      have he := (hv n).2.2
      dsimp [z]
      linarith [hτone n]
  obtain ⟨u₀, hu₀, φ, hφ, hlim⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : Fin (q + 1) → ℝ) (fun _ => s + 1))).tendsto_subseq hz
  let u : ℕ → ℝ := fun k => if hk : k ≤ q then u₀ ⟨k, by omega⟩ else 0
  have hτφ : Tendsto (fun n => τ (φ n)) atTop (𝓝 0) := hτlim.comp hφ.tendsto_atTop
  have hlimq : Tendsto (fun n => v (φ n) q) atTop (𝓝 (u₀ ⟨q, by omega⟩)) :=
    (tendsto_pi_nhds.1 hlim) ⟨q, by omega⟩
  have hend : u q ≤ s := by
    have h := le_of_tendsto_of_tendsto hlimq
      (tendsto_const_nhds.add hτφ) (Eventually.of_forall fun n => (hv (φ n)).2.2)
    simpa [u] using h
  refine ⟨u, ⟨?_, ?_, hend⟩, ?_⟩
  · intro k hk
    simpa [u, hk] using hu₀.1 (⟨k, by omega⟩ : Fin (q + 1))
  · intro a b hab hb
    have ha : a ≤ q := hab.trans hb
    have h := le_of_tendsto_of_tendsto
      ((tendsto_pi_nhds.1 hlim) (⟨a, by omega⟩ : Fin (q + 1)))
      ((tendsto_pi_nhds.1 hlim) (⟨b, by omega⟩ : Fin (q + 1)))
      (Eventually.of_forall fun n => (hv (φ n)).2.1 a b hab hb)
    simpa [u, ha, hb] using h
  · intro ε hε R hR
    have hlarge : ∀ᶠ n : ℕ in atTop, R ≤ N (φ n) := by
      have hnat : Tendsto (fun n => (φ n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
      filter_upwards [hnat.eventually (eventually_ge_atTop R)] with n hn
      linarith [hN (φ n)]
    have hsmall : ∀ᶠ n : ℕ in atTop, τ (φ n) < ε / 2 :=
      hτφ.eventually (Iio_mem_nhds (by linarith))
    have hclose : ∀ᶠ n : ℕ in atTop, dist (z (φ n)) u₀ < ε / 4 :=
      (Metric.tendsto_nhds.1 hlim) (ε / 4) (by positivity)
    obtain ⟨n, hnR, hnτ, hnclose⟩ := (hlarge.and (hsmall.and hclose)).exists
    let δ := (ε - τ (φ n)) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hdiff : ∀ k : ℕ, k ≤ q → |v (φ n) k - u k| ≤ δ := by
      intro k hk
      have hcomp := norm_le_pi_norm (z (φ n) - u₀) (⟨k, by omega⟩ : Fin (q + 1))
      have hc : |v (φ n) k - u k| ≤ dist (z (φ n)) u₀ := by
        simpa [z, u, hk, dist_eq_norm, Real.norm_eq_abs] using hcomp
      dsimp [δ]
      linarith
    have hNtwo : 2 ≤ N (φ n) := by linarith [hN (φ n), (Nat.cast_nonneg (φ n) : (0 : ℝ) ≤ φ n)]
    have hP := hstable (v (φ n)) u (τ (φ n)) δ (N (φ n))
      (hτpos (φ n)) hδ hNtwo hdiff (hPv (φ n))
    have he : τ (φ n) + 2 * δ = ε := by dsimp [δ]; ring
    exact ⟨N (φ n), hnR, by simpa only [he] using hP⟩

