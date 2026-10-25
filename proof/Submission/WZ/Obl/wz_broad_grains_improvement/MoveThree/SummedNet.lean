-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.SummedNet.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/SummedNet.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641 commit 7652d3d, SummedNet.lean. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NetEstimate

noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement
open WangZahlLot.Obl.wz_transverse_cell_weighted_cover

abbrev lowQCoeff (A δ ε b ω σ w M Λ : ℝ) (d : ℕ) : ℝ :=
  A * netConst * δ ^ ε * (4 * b) ^ (ω + σ) * w / ((d : ℝ) * Λ * M)

/-- One label, keeping the concentration factor: for every threshold `K ≥ 1`, a fibre size
`q * w ≤ M (4b)^2 / K` forces shading mass `lowQCoeff * K^(σ/2) * #I`. -/
theorem label_net_low_q_conc {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω)
    (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (n d : ℕ) (I : Finset (Fin n))
        (U Y : Fin n → Set V) (Γ : Set V) (c : Fin n → V) (u : Fin n → Fin 3 → V)
        (a b Λ w M D : ℝ),
      I.Nonempty → (n : ℝ) ≤ δ ^ (-100 : ℝ) → 0 < d → 1 < Λ → (n : ℝ) < Λ ^ d →
      0 ≤ a → a ≤ b → 4 * δ ≤ b → b ≤ 1 / 1000000 →
      0 < w → 0 < M → 6144 * δ ^ η ≤ D → MeasurableSet Γ →
      (∀ i ∈ I, Orthonormal ℝ (u i)) → (∀ i ∈ I, ‖c i‖ < 1 / 100) →
      (∀ i ∈ I, U i ⊆ prism a b (c i) (u i)) →
      (∀ i ∈ I, Y i ⊆ Γ ∩ prism a b (c i) (u i)) →
      (∀ i ∈ I, O (D * b ^ 2) ≤ μ (Y i)) →
      BodyConvexCount U w M →
      ∃ (N q : ℕ) (k : Fin N → Fin n) (F : Fin N → Finset (Fin n)),
        0 < N ∧ 0 < q ∧ (∀ j, k j ∈ I) ∧ (∀ j, F j ⊆ I) ∧
        (∀ j, (F j).card = q) ∧ (∀ j j', j ≠ j' → Disjoint (F j) (F j')) ∧
        netConst * (I.card : ℝ) ≤ (d : ℝ) * Λ * N * q ∧
        (∀ j, ∀ i ∈ F j, U i ⊆ cTube b (c (k j)) (u (k j))) ∧
        (∀ j j', j ≠ j' → μ (cTube b (c (k j)) (u (k j)) ∩
          cTube b (c (k j')) (u (k j'))) ≤
          (1 / 2 : ℝ≥0∞) * μ (cTube b (c (k j)) (u (k j)))) ∧
        ∀ K : ℝ, 1 ≤ K → (q : ℝ) * w ≤ M * (4 * b) ^ 2 / K →
          O (lowQCoeff A δ ε b ω σ w M Λ d * K ^ (σ / 2) * I.card) ≤ μ Γ := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, HE⟩ :=
    balanced_net_density_estimate_with_separation hσ hσhalf hω hE ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd n d I U Y Γ c u a b Λ w M D hI hn hd hΛ hnΛ ha hab hδb hbsmall hw hM hD hΓ
    hu hc hU hY hden hK
  have hcard : (0 : ℝ) < I.card := by exact_mod_cast hI.card_pos
  have hτ : 0 < (I.card : ℝ) * w / M := by positivity
  have hsat : (I.card : ℝ) * w / M * M ≤ (I.card : ℝ) * w := by
    rw [div_mul_cancel₀ _ hM.ne']
  obtain ⟨N, q, k, F, hN, hq, hk, hFI, hFc, hdisj, hret, hwhole, hX, hlow⟩ :=
    HE δ hδ hδd n d I U Y Γ c u a b Λ w M D ((I.card : ℝ) * w / M) hI hn hd hΛ hnΛ ha hab
      hδb hbsmall hw hM hτ hD hΓ hu hc hU hY hden hK hsat
  refine ⟨N, q, k, F, hN, hq, hk, hFI, hFc, hdisj, hret, hwhole, hX, ?_⟩
  intro Kc hKc hqw
  have hb : 0 < b := (by positivity : 0 < 4 * δ).trans_le hδb
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hΛ0 : 0 < Λ := lt_trans zero_lt_one hΛ
  have hKc0 : 0 < Kc := lt_of_lt_of_le zero_lt_one hKc
  have hqw' : (q : ℝ) * w ≤ M * (4 * b) ^ 2 := by
    refine hqw.trans ?_
    exact div_le_self (by positivity) hKc
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hlow hqw')
  have hXK : Kc ≤ M * (4 * b) ^ 2 / ((q : ℝ) * w) := by
    rw [le_div_iff₀ (by positivity)]
    have := (le_div_iff₀ hKc0).mp hqw
    nlinarith
  have hXpow : Kc ^ (σ / 2) ≤ (M * (4 * b) ^ 2 / ((q : ℝ) * w)) ^ (σ / 2) :=
    Real.rpow_le_rpow hKc0.le hXK (by positivity)
  have hpos : 0 ≤ A * (netConst * ((I.card : ℝ) * w / M) / ((d : ℝ) * Λ)) * δ ^ ε *
      (4 * b) ^ (ω + σ) := by
    have := netConst_pos
    positivity
  calc
    lowQCoeff A δ ε b ω σ w M Λ d * Kc ^ (σ / 2) * I.card =
        A * (netConst * ((I.card : ℝ) * w / M) / ((d : ℝ) * Λ)) * δ ^ ε *
          (4 * b) ^ (ω + σ) * Kc ^ (σ / 2) := by
      dsimp only [lowQCoeff]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hXpow hpos

/-- All labels at once, keeping the concentration factor for a common threshold `K ≥ 1`. -/
theorem summed_low_q_net_conc {σ ω : ℝ} (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) (hω : 0 < ω)
    (hE : E σ ω) :
    ∀ ε : ℝ, 0 < ε → ∃ A η d₀ : ℝ, 0 < A ∧ 0 < η ∧ 0 < d₀ ∧ d₀ ≤ 1 / 100 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ d₀ → ∀ (Kc : ℝ), 1 ≤ Kc → ∀ {ι : Type} (Lab : Finset ι) (n d : ℕ)
        (I : ι → Finset (Fin n)) (U Y : ι → Fin n → Set V) (Γ : ι → Set V)
        (c : ι → Fin n → V) (u : ι → Fin n → Fin 3 → V) (a b Λ w M D : ℝ),
      (n : ℝ) ≤ δ ^ (-100 : ℝ) → 0 < d → 1 < Λ → (n : ℝ) < Λ ^ d →
      0 ≤ a → a ≤ b → 4 * δ ≤ b → b ≤ 1 / 1000000 →
      0 < w → 0 < M → 6144 * δ ^ η ≤ D →
      (∀ l ∈ Lab, (I l).Nonempty ∧ MeasurableSet (Γ l) ∧
        (∀ i ∈ I l, Orthonormal ℝ (u l i)) ∧ (∀ i ∈ I l, ‖c l i‖ < 1 / 100) ∧
        (∀ i ∈ I l, U l i ⊆ prism a b (c l i) (u l i)) ∧
        (∀ i ∈ I l, Y l i ⊆ Γ l ∩ prism a b (c l i) (u l i)) ∧
        (∀ i ∈ I l, O (D * b ^ 2) ≤ μ (Y l i)) ∧
        BodyConvexCount (U l) w M) →
      ∃ (N q : ι → ℕ) (k : ∀ l, Fin (N l) → Fin n) (F : ∀ l, Fin (N l) → Finset (Fin n)),
        (∀ l ∈ Lab, 0 < N l ∧ 0 < q l ∧ (∀ j, k l j ∈ I l) ∧ (∀ j, F l j ⊆ I l) ∧
          (∀ j, (F l j).card = q l) ∧ (∀ j j', j ≠ j' → Disjoint (F l j) (F l j')) ∧
          netConst * ((I l).card : ℝ) ≤ (d : ℝ) * Λ * N l * q l ∧
          (∀ j, ∀ i ∈ F l j, U l i ⊆ cTube b (c l (k l j)) (u l (k l j))) ∧
          (∀ j j', j ≠ j' → μ (cTube b (c l (k l j)) (u l (k l j)) ∩
            cTube b (c l (k l j')) (u l (k l j'))) ≤
            (1 / 2 : ℝ≥0∞) * μ (cTube b (c l (k l j)) (u l (k l j))))) ∧
        ∑ l ∈ Lab.filter (fun l => (q l : ℝ) * w ≤ M * (4 * b) ^ 2 / Kc),
            O (lowQCoeff A δ ε b ω σ w M Λ d * Kc ^ (σ / 2) * (I l).card) ≤
          ∑ l ∈ Lab.filter (fun l => (q l : ℝ) * w ≤ M * (4 * b) ^ 2 / Kc), μ (Γ l) := by
  intro ε hε
  obtain ⟨A, η, d₀, hA, hη, hd₀, hd₀small, H⟩ := label_net_low_q_conc hσ hσhalf hω hE ε hε
  refine ⟨A, η, d₀, hA, hη, hd₀, hd₀small, ?_⟩
  intro δ hδ hδd Kc hKc ι Lab n d I U Y Γ c u a b Λ w M D hn hd hΛ hnΛ ha hab hδb hbsmall hw hM
    hD hlab
  classical
  have hex : ∀ l : ι, ∃ (N q : ℕ) (k : Fin N → Fin n) (F : Fin N → Finset (Fin n)),
      l ∈ Lab → (0 < N ∧ 0 < q ∧ (∀ j, k j ∈ I l) ∧ (∀ j, F j ⊆ I l) ∧
        (∀ j, (F j).card = q) ∧ (∀ j j', j ≠ j' → Disjoint (F j) (F j')) ∧
        netConst * ((I l).card : ℝ) ≤ (d : ℝ) * Λ * N * q ∧
        (∀ j, ∀ i ∈ F j, U l i ⊆ cTube b (c l (k j)) (u l (k j))) ∧
        (∀ j j', j ≠ j' → μ (cTube b (c l (k j)) (u l (k j)) ∩
          cTube b (c l (k j')) (u l (k j'))) ≤
          (1 / 2 : ℝ≥0∞) * μ (cTube b (c l (k j)) (u l (k j)))) ∧
        ((q : ℝ) * w ≤ M * (4 * b) ^ 2 / Kc →
          O (lowQCoeff A δ ε b ω σ w M Λ d * Kc ^ (σ / 2) * (I l).card) ≤ μ (Γ l))) := by
    intro l
    by_cases hl : l ∈ Lab
    · obtain ⟨hI, hΓ, hu, hc, hU, hY, hden, hK⟩ := hlab l hl
      obtain ⟨N, q, k, F, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
        H δ hδ hδd n d (I l) (U l) (Y l) (Γ l) (c l) (u l)
          a b Λ w M D hI hn hd hΛ hnΛ ha hab hδb hbsmall hw hM hD hΓ hu hc hU hY hden hK
      exact ⟨N, q, k, F, fun _ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10 Kc hKc⟩⟩
    · exact ⟨0, 0, Fin.elim0, Fin.elim0, fun h => (hl h).elim⟩
  choose N q k F hprop using hex
  refine ⟨N, q, k, F, fun l hl => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := hprop l hl
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · apply Finset.sum_le_sum
    intro l hl
    have hl' := Finset.mem_filter.mp hl
    exact (hprop l hl'.1).2.2.2.2.2.2.2.2.2 hl'.2

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
