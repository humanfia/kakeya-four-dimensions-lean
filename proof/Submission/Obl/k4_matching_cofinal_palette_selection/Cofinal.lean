import Submission.Obl.k4_matching_cofinal_palette_selection.Monotonicity
import Submission.Obl.k4_matching_cofinal_palette_selection.Data

namespace Submission.Obl.k4_matching_cofinal_palette_selection

open Filter
open scoped Topology

theorem cofinal_finite_choice {ι : Type*} (B : Finset ι) (P : ι → ℝ → ℝ → Prop)
    (hmono : ∀ i ε ε' N, 2 ≤ N → ε ≤ ε' → P i ε N → P i ε' N)
    (h : Cofinal (fun ε N => ∃ i ∈ B, P i ε N)) :
    ∃ i ∈ B, Cofinal (P i) := by
  classical
  let τ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hτpos (n : ℕ) : 0 < τ n := by dsimp [τ]; positivity
  have hτlim : Tendsto τ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hh : ∃ᶠ n : ℕ in atTop, ∃ i ∈ B, ∃ N : ℝ,
      (n : ℝ) + 2 ≤ N ∧ P i (τ n) N := by
    apply Frequently.of_forall
    intro n
    obtain ⟨N, hN, i, hi, hP⟩ := h (τ n) (hτpos n) ((n : ℝ) + 2)
      (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    exact ⟨i, hi, N, hN, hP⟩
  obtain ⟨i, hi, hfreq⟩ := B.frequently_exists.mp hh
  refine ⟨i, hi, ?_⟩
  intro ε hε R hR
  have hsmall : ∀ᶠ n : ℕ in atTop, τ n ≤ ε :=
    (hτlim.eventually (Iio_mem_nhds hε)).mono fun _ hn => hn.le
  have hlarge : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) + 2 := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)] with n hn
    linarith
  obtain ⟨n, ⟨N, hN, hP⟩, hnε, hnR⟩ := (hfreq.and_eventually (hsmall.and hlarge)).exists
  exact ⟨N, hnR.trans hN, hmono i (τ n) ε N (hR.trans (hnR.trans hN)) hnε hP⟩

/-- Among finitely many admissible subsets, one supports records cofinally in
both the loss and the scale. -/
theorem cofinal_good_subset {J q : ℕ} {d δ θ : ℝ} {β : ℕ → ℝ} {r : ℝ → ℝ}
    {l : ℕ → ℝ → ℝ} {u : ℕ → ℝ} {m z : ℕ → ℕ} (A : Finset ℕ)
    (h : Cofinal (fun ε N => ∃ G : Finset ℕ, G ⊆ A ∧
      ((A \ G).card : ℝ) / (q : ℝ) ≤ δ ∧ GoodRecordData J d β r l q u ε N m z G θ)) :
    ∃ G : Finset ℕ, G ⊆ A ∧ ((A \ G).card : ℝ) / (q : ℝ) ≤ δ ∧
      Cofinal (fun ε N => GoodRecordData J d β r l q u ε N m z G θ) := by
  classical
  let B := A.powerset.filter (fun G => ((A \ G).card : ℝ) / (q : ℝ) ≤ δ)
  have hchoice : Cofinal (fun ε N => ∃ G ∈ B, GoodRecordData J d β r l q u ε N m z G θ) := by
    intro ε hε R hR
    obtain ⟨N, hN, G, hGA, hcard, hgood⟩ := h ε hε R hR
    exact ⟨N, hN, G, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hGA, hcard⟩, hgood⟩
  obtain ⟨G, hGB, hco⟩ := cofinal_finite_choice B
    (fun G ε N => GoodRecordData J d β r l q u ε N m z G θ)
    (fun _ _ _ _ hN hε hr => hr.mono (by linarith) hε) hchoice
  obtain ⟨hGA, hcard⟩ := Finset.mem_filter.mp hGB
  exact ⟨G, Finset.mem_powerset.mp hGA, hcard, hco⟩

/-- A uniform selection for all sufficiently large records gives one fixed
cofinal good subset. -/
theorem cofinal_good_subset_of_large_records {J q : ℕ} {d δ θ : ℝ} {β : ℕ → ℝ}
    {r : ℝ → ℝ} {l : ℕ → ℝ → ℝ} {u : ℕ → ℝ} {m z : ℕ → ℕ}
    (A : Finset ℕ) (hco : Cofinal (RecordData J d β r l q u))
    (N₀ : ℝ) (hN₀ : 2 ≤ N₀)
    (hselect : ∀ ε N : ℝ, N₀ ≤ N → RecordData J d β r l q u ε N →
      ∃ G : Finset ℕ, G ⊆ A ∧ ((A \ G).card : ℝ) / (q : ℝ) ≤ δ ∧
        GoodRecordData J d β r l q u ε N m z G θ) :
    ∃ G : Finset ℕ, G ⊆ A ∧ ((A \ G).card : ℝ) / (q : ℝ) ≤ δ ∧
      Cofinal (fun ε N => GoodRecordData J d β r l q u ε N m z G θ) := by
  apply cofinal_good_subset A
  intro ε hε R hR
  obtain ⟨N, hN, hr⟩ := hco ε hε (max R N₀) (hR.trans (le_max_left _ _))
  obtain ⟨G, hGA, hcard, hg⟩ := hselect ε N ((le_max_right _ _).trans hN) hr
  exact ⟨N, (le_max_left _ _).trans hN, G, hGA, hcard, hg⟩

end Submission.Obl.k4_matching_cofinal_palette_selection
