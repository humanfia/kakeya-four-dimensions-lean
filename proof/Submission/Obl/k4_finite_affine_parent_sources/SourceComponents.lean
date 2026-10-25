-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceSet
import Submission.Obl.k4_finite_affine_parent_sources.PathFullness

/-!
# The source preparation from its two components

`SourcePartsSpec` splits into two independent per-sample components with the same quantifier
prefix:

* `SourceSelectionSpec` (probability preparation): a mixed candidate, or a parent `a` with
  `s(lev a) ∈ [1/8, 1/4]`, a measurable set `G` inside the residual of its world with
  `m τ packet(a) < mass(G ∩ counted a)` (e.g. `room_of_counted_density` from a density
  `c₀ > m τ κ²` in the counted set), such that no label of the parent's world at a level
  between `lev a` and depth `L/2` met by `G` is axis-deficient (`sourceAxisMask`), a palette `π`
  and a floor `τ`, such that every model on `a` and `π` over a subset of `G` has its per-label
  velocity caps and `EH2`.
* `SourceTrackingSpec` (geometry): a mixed candidate, or tracking coefficients for every model
  over a subset of the residual in the open block of any parent in the band, whose parent and
  model labels are not axis-deficient.

The unpruned set is `exists_prepared_set` of `G`, which keeps all of `G ∩ counted a`.
Mixed candidates of the two components are merged with `mixedCandidate_mono`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Filter

noncomputable section

/-- The axis-deficiency threshold of the source stage: `Nk^(-uLβ/2)` with
`β = min(θ/1000, ℓ/1000)`, `θ = ρ/(10⁶(n+1))` (agreed with x0923, x0807, x0812). -/
def sourceAxisMask (n : ℕ) (ℓ ρ u Nk L : ℝ) : ℝ :=
  Nk ^ (-(u * L * min (ρ / (1000000 * ((n : ℝ) + 1)) / 1000) (ℓ / 1000) / 2))

/-- The per-sample package of the selection component: a parent `a` in the band, a measurable
set `Gm` in the residual of its world with room for the floor, fullness of the labels it meets, a
floor `τ`, a palette `π`, and velocity caps and `EH2` for every model on `a` over a subset of
`Gm`. -/
def SelectionOutput {W : ℕ} (p : PathData W) (n m : ℕ) (s : ℕ → ℝ) (d₁ ℓ S ρ u δ₀ ε Nk L : ℝ)
    (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ) (H : Fin W → Set Incidence) : Prop :=
    ∃ (a : Fin p.C) (Gm : Set Incidence) (π : Measure ℝ) (τ : ℝ),
      MeasurableSet Gm ∧ Gm ⊆ H (p.world a) ∧
      (m : ℝ) * τ * (((ν (p.world a)).prod volume) (p.packet a)).toReal <
        (((ν (p.world a)).prod volume) (Gm ∩ p.counted a)).toReal ∧
      1 / 8 ≤ s (p.lev a) ∧ s (p.lev a) ≤ 1 / 4 ∧
      (∀ b : Fin p.C, p.world b = p.world a → p.lev a ≤ p.lev b → s (p.lev b) ≤ 1 / 2 →
        (Gm ∩ p.counted b).Nonempty →
        ¬p.axisDeficient (sourceAxisMask n ℓ ρ u Nk L) b) ∧
      s (p.lev a) + u + δ₀ ≤ 1 / 2 ∧ 0 < τ ∧
      τ⁻¹ ≤ Nk ^ (ε / 4000000) ∧
      τ⁻¹ ≤ Nk ^ (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 4) ∧
      τ⁻¹ ≤ Nk ^ (1 / 2 : ℝ) ∧
      IsProbabilityMeasure π ∧
      ∀ D : SourceData p, D.parent = a → D.π = π → D.S ⊆ Gm → MeasurableSet D.S →
        D.S.Nonempty → D.D₀ = MajorFrame.frame (p.frame a) →
        D.K = (Nk ^ (u * L)) ^ (ρ / (1000000 * ((n : ℝ) + 1))) →
        D.depth = sourceDepth m s (p.lev a) u →
        D.S ⊆ p.assigned a ×ˢ Ioo ((p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
          (((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a)) →
        (∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
          z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) →
        ¬p.axisDeficient (sourceAxisMask n ℓ ρ u Nk L) a →
        (∀ x : ℝ, (n : ℝ)⁻¹ ≤ x → x ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth x)),
          ¬p.axisDeficient (sourceAxisMask n ℓ ρ u Nk L) (D.old x i)) →
        ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet D.parent) ≤
          ((ν D.w₀).prod volume) (D.S ∩ p.counted D.parent) →
        (∀ x : ℝ, (n : ℝ)⁻¹ ≤ x → x ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth x)),
          ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old x i)) ≤
            ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old x i))) →
        D.VelCaps n u Nk L ν B ∧ EH2 d₁ S (D.stage Nk L u ν B) n

/-- **Selection component** of the source preparation. -/
def SourceSelectionSpec : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ n : ℕ, 2 ≤ n →
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ gain : ℝ, 0 < gain → gain ≤ g₀ →
    ∀ (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ), FineGrid m s gain ρ → 0 < δ₀ → δ₀ ≤ ρ * gain →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
      (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
      ∀ Mp Dp : ℕ, ∃ Mprep : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ σp : ℝ, 0 < σp ∧ ∃ kp : ℕ, ∀ σ : ℝ, 0 < σ → σ ≤ σp → ∀ k, kp ≤ k →
      ∀ p : PathData (W k), p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (W k) → Set Incidence,
        (∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc (W k) p.C m p.lev p.world p.counted w) →
        (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
          ((ν k w).prod volume) (TerminalInc (W k) p.C m p.lev p.world p.counted w)) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H w) →
        MixedCandidate (N k) L (W k) (ν k) (B k) Mprep d₁ ρ gain ε
          p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned H ∨
        SelectionOutput p n m s d₁ ℓ S ρ u δ₀ ε (N k) L (ν k) (B k) H

/-- **Tracking component** of the source preparation. -/
def SourceTrackingSpec : Prop :=
  ∀ d₁ κ₁ ℓ S η ρ : ℝ, 0 ≤ d₁ → d₁ < 1 → 0 < κ₁ → κ₁ ≤ 1 →
    0 < ℓ → 0 < S → S ≤ 1 → 0 < η → 0 < ρ → ρ ≤ 1 / 4 →
    ∀ n : ℕ, 2 ≤ n →
    ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
    ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ gain : ℝ, 0 < gain → gain ≤ g₀ →
    ∀ (m : ℕ) (s : ℕ → ℝ) (δ₀ : ℝ), FineGrid m s gain ρ → 0 < δ₀ → δ₀ ≤ ρ * gain →
    ∀ N K L d W ω ν E P B f g G, prob N K L d S η W ω ν E P B f g G →
      (∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) →
      ∀ Mp Dp : ℕ, ∃ Mprep : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ σp : ℝ, 0 < σp ∧ ∃ kp : ℕ, ∀ σ : ℝ, 0 < σ → σ ≤ σp → ∀ k, kp ≤ k →
      ∀ p : PathData (W k), p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (W k) → Set Incidence,
        (∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc (W k) p.C m p.lev p.world p.counted w) →
        (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
          ((ν k w).prod volume) (TerminalInc (W k) p.C m p.lev p.world p.counted w)) ≤
        ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H w) →
        MixedCandidate (N k) L (W k) (ν k) (B k) Mprep d₁ ρ gain ε
          p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned H ∨
        ∀ (a : Fin p.C) (τ : ℝ) (D : SourceData p), D.parent = a →
          1 / 8 ≤ s (p.lev a) → s (p.lev a) ≤ 1 / 4 →
          s (p.lev a) + u + δ₀ ≤ 1 / 2 → 0 < τ →
          τ⁻¹ ≤ N k ^ (ε / 4000000) →
          τ⁻¹ ≤ N k ^ (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 4) →
          τ⁻¹ ≤ N k ^ (1 / 2 : ℝ) →
          D.S ⊆ H (p.world a) → MeasurableSet D.S → D.S.Nonempty →
          D.D₀ = MajorFrame.frame (p.frame a) →
          D.K = (N k ^ (u * L)) ^ (ρ / (1000000 * ((n : ℝ) + 1))) →
          D.depth = sourceDepth m s (p.lev a) u →
          D.S ⊆ p.assigned a ×ˢ Ioo ((p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
            (((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a)) →
          (∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
            z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) →
          ¬p.axisDeficient (sourceAxisMask n ℓ ρ u (N k) L) a →
          (∀ x : ℝ, (n : ℝ)⁻¹ ≤ x → x ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth x)),
            ¬p.axisDeficient (sourceAxisMask n ℓ ρ u (N k) L) (D.old x i)) →
          ENNReal.ofReal τ * ((ν k D.w₀).prod volume) (p.packet D.parent) ≤
            ((ν k D.w₀).prod volume) (D.S ∩ p.counted D.parent) →
          (∀ x : ℝ, (n : ℝ)⁻¹ ≤ x → x ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth x)),
            ENNReal.ofReal τ * ((ν k D.w₀).prod volume) (p.packet (D.old x i)) ≤
              ((ν k D.w₀).prod volume) (D.S ∩ p.counted (D.old x i))) →
          ∃ c, D.Tracks n ℓ u (N k) L (ν k) (B k) c

/-- **`SourcePartsSpec` from its two components.** -/
theorem sourcePartsSpec_of_components (hA : SourceSelectionSpec) (hB : SourceTrackingSpec) :
    SourcePartsSpec := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  obtain ⟨uA, huA, hUA⟩ := hA d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  obtain ⟨uB, huB, hUB⟩ := hB d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  refine ⟨min (min uA uB) (1 / 4), lt_min (lt_min huA huB) (by norm_num), fun u hu hu' => ?_⟩
  have hu4 : u ≤ 1 / 4 := hu'.trans (min_le_right _ _)
  obtain ⟨gA, hgA, hGA⟩ := hUA u hu (hu'.trans ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨gB, hgB, hGB⟩ := hUB u hu (hu'.trans ((min_le_left _ _).trans (min_le_right _ _)))
  refine ⟨min gA gB, lt_min hgA hgB, fun gain hg hg' m s δ₀ hgrid hδ₀ hδ₀' => ?_⟩
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨MA, hPA⟩ := hGA gain hg (hg'.trans (min_le_left _ _)) m s δ₀ hgrid hδ₀ hδ₀'
    N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨MB, hPB⟩ := hGB gain hg (hg'.trans (min_le_right _ _)) m s δ₀ hgrid hδ₀ hδ₀'
    N K L d W ω ν E P B f g G hprob hprof Mp Dp
  refine ⟨max MA MB, fun ε hε => ?_⟩
  obtain ⟨σA, hσA, kA, hKA⟩ := hPA ε hε
  obtain ⟨σB, hσB, kB, hKB⟩ := hPB ε hε
  refine ⟨min σA σB, lt_min hσA hσB, max kA kB, fun σ hσ hσ' k hk p hp H hH hmass => ?_⟩
  obtain ⟨hNge, -, -, -, -, hνp, -, -⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic N K L d S η W ω ν E P B f g G
      hprob
  have hN1 : (1 : ℝ) ≤ N k := by linarith [hNge k]
  rcases hKA σ hσ (hσ'.trans (min_le_left _ _)) k ((le_max_left _ _).trans hk) p hp H hH
      hmass with hcA | ⟨a, Gm, π, τ, hGm, hGH, hdens, hband1, hband2, hfull, hroom, hτ, hτε, hτu,
        hτh, hπ, hmodels⟩
  · exact Or.inl (mixedCandidate_mono hN1 (le_max_left _ _) hcA)
  rcases hKB σ hσ (hσ'.trans (min_le_right _ _)) k ((le_max_right _ _).trans hk) p hp H hH
      hmass with hcB | htrack
  · exact Or.inl (mixedCandidate_mono hN1 (le_max_right _ _) hcB)
  right
  have : IsProbabilityMeasure (ν k (p.world a)) := hνp k _
  obtain ⟨S₁, hS₁G, hS₁m, hS₁o, hS₁e, hS₁mass⟩ := exists_prepared_set hp a hGm
  have hS₁a : S₁ ⊆ p.packet a := fun z hz =>
    ⟨(hS₁o hz).1, Set.Ioo_subset_Icc_self (hS₁o hz).2⟩
  -- fullness of the parent and of the model labels
  have hi₀ : p.lev a < m := hp.label_level a
  have hGne : (Gm ∩ p.counted a).Nonempty := by
    have hpos : 0 < (((ν k (p.world a)).prod volume) (Gm ∩ p.counted a)).toReal := by
      have : 0 ≤ (m : ℝ) * τ * (((ν k (p.world a)).prod volume) (p.packet a)).toReal := by
        have := hτ.le; positivity
      linarith
    apply nonempty_of_measure_ne_zero (μ := (ν k (p.world a)).prod volume)
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hfa : ¬p.axisDeficient (sourceAxisMask n ℓ ρ u (N k) L) a :=
    hfull a rfl le_rfl (by linarith) hGne
  have hroom' : s (p.lev a) + u ≤ s (m - 1) := by
    rw [hgrid.1.2.2.2]; linarith
  have hfl : ∀ D : SourceData p, D.parent = a → D.S ⊆ Gm →
      D.depth = sourceDepth m s (p.lev a) u →
      ∀ x : ℝ, (n : ℝ)⁻¹ ≤ x → x ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth x)),
        ¬p.axisDeficient (sourceAxisMask n ℓ ρ u (N k) L) (D.old x i) := by
    intro D hDa hDG hDd x hx1 hx2 i
    have hx0 : 0 ≤ x := le_trans (inv_nonneg.mpr (Nat.cast_nonneg n)) hx1
    obtain ⟨hw, hne⟩ := D.old_world x i
    have hlev := D.old_level x i
    rw [hDd] at hlev
    have hw' : p.world (D.old x i) = p.world a := by rw [hw, SourceData.w₀, hDa]
    have hge : p.lev a ≤ p.lev (D.old x i) := by
      rw [hlev]; exact sourceDepth_ge s hi₀ hu.le x
    have hnom := (sourceDepth_nominal hgrid.1.1 hi₀ hu.le (by positivity) (fineGrid_mesh hgrid)
      hroom' hx0 hx2).1
    have hsle : s (p.lev (D.old x i)) ≤ 1 / 2 := by
      rw [hlev]
      have : u * x ≤ u := by nlinarith
      linarith
    exact hfull (D.old x i) hw' hge hsle
      (hne.mono (Set.inter_subset_inter_left _ hDG))
  refine ⟨a, S₁, π, τ,
    { room := hroom
      τ_pos := hτ
      τ_ε := hτε
      τ_u := hτu
      τ_half := hτh
      π_prob := hπ
      S_meas := hS₁m
      S_res := hS₁G.trans hGH
      S_open := hS₁o
      S_term := (hS₁G.trans hGH).trans (hH (p.world a)).2
      S_end := hS₁e
      mass := hdens.trans_le (ENNReal.toReal_mono
        (ne_top_of_le_ne_top (packet_ne_top _ a) (measure_mono hS₁a)) hS₁mass)
      models := ?_ }⟩
  intro D hDa hDπ hDS hDm hDne hD₀ hDK hDd hpf hlf
  have hDo : D.S ⊆ p.assigned a ×ˢ Ioo ((p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
      (((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a)) := hDS.trans hS₁o
  have hDfl := hfl D hDa (hDS.trans hS₁G) hDd
  obtain ⟨hvel, heh2⟩ := hmodels D hDa hDπ (hDS.trans hS₁G) hDm hDne hD₀ hDK hDd hDo
    (fun z hz => hS₁e z (hDS hz)) hfa hDfl hpf hlf
  exact ⟨htrack a τ D hDa hband1 hband2 hroom hτ hτε hτu hτh ((hDS.trans hS₁G).trans hGH) hDm
    hDne hD₀ hDK hDd hDo (fun z hz => hS₁e z (hDS hz)) hfa hDfl hpf hlf, hvel, heh2⟩

/-- **The source preparation from its two components.** -/
theorem sourcePreparation_of_components (hA : SourceSelectionSpec) (hB : SourceTrackingSpec) :
    SourcePreparation :=
  sourcePreparation_of_parts (sourcePartsSpec_of_components hA hB)

end

end Submission.Obl.k4_finite_affine_parent_sources
