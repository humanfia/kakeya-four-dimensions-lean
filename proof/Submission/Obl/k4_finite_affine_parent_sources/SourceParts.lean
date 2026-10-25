-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourcePrep
import Submission.Obl.k4_finite_affine_parent_sources.SourceFloors
import Submission.Obl.k4_finite_affine_parent_sources.SourceDet

/-!
# The source preparation from its parts

`SourcePartsSpec` is a smaller per-sample interface than `SourceInputsSpec`: a late sample has
an original mixed candidate, or a parent `a` with an UNPRUNED prepared set `S₁` (with room for
the floor `τ`: `m τ packet(a) < mass(S₁)`), a palette `π`, and, for every model built on `a`,
`π` and a measurable nonempty subset of `S₁` with the floors, tracking coefficients, per-label
velocity caps and `EH2`. The floors are produced by pruning (`exists_local_floors`) and the
determinant floors are proved (`SourceData.det_field`), so neither is an input any more.
Velocity caps and `EH2` are upper bounds on `muE S`, monotone in `S` (`muE_mono`), so they
may be proved for `S₁`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Filter
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

namespace SourceData

variable {W : ℕ} {p : PathData W}

/-- Tracking coefficients `c` of the model labels (the field `Inputs.track` for `c`). -/
def Tracks (D : SourceData p) (n : ℕ) (ℓ unit Nk L : ℝ) (ν : Fin W → Measure Trajectory)
    (B : Fin W → ℝ) (c : (s : ℝ) → Fin (p.activeCount D.Hm (D.depth s)) → Fin 5 → ℝ) :
    Prop :=
  ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
    (∀ e, |c s i e| ≤ D.K) ∧
    (∀ l ∈ p.assigned (D.old s i), ∀ t ∈ IS (D.relT s) (D.relBin s i),
      |(exS (D.stage Nk L unit ν B).b l t) 1 - c s i 0 - t * c s i 1| ≤
        D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) ∧
      |(exS (D.stage Nk L unit ν B).b l t) 2 - c s i 2 - t * c s i 3 -
          c s i 4 * (exS (D.stage Nk L unit ν B).b l t) 1| ≤
        D.K * (2 : ℝ) ^ (-(D.relT s : ℤ)) * (Nk ^ (unit * L)) ^ (-ℓ * s) ∧
      |(D.stage Nk L unit ν B).b l 4 - c s i 3 - c s i 4 * (D.stage Nk L unit ν B).b l 3| ≤
        D.K * (Nk ^ (unit * L)) ^ (-ℓ * s))

/-- The per-label velocity caps (the field `Inputs.vel`). -/
def VelCaps (D : SourceData p) (n : ℕ) (unit Nk L : ℝ) (ν : Fin W → Measure Trajectory)
    (B : Fin W → ℝ) : Prop :=
  ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ (i : Fin (p.activeCount D.Hm (D.depth s)))
      (v : ℝ) (v₀ : ℤ), (n : ℝ)⁻¹ ≤ v → v ≤ n →
    (D.stage Nk L unit ν B).μ {z | z.1 ∈ p.assigned (D.old s i) ∧
        z.2 ∈ IS (D.relT s) (D.relBin s i) ∧
        ⌊(D.stage Nk L unit ν B).b z.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} ≤
      ENNReal.ofReal (D.K * (2 : ℝ) ^ (-(D.relT s : ℤ))) *
        (D.stage Nk L unit ν B).ν (p.assigned (D.old s i)) *
        D.π {w : ℝ | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}

end SourceData

/-- The parts of a source stage on the parent `a`, before pruning. -/
structure SourceParts {W : ℕ} (p : PathData W) (n m : ℕ) (sg : ℕ → ℝ)
    (d₁ ℓ S ρ u δ₀ ε Nk L : ℝ) (ν : Fin W → Measure Trajectory) (B : Fin W → ℝ)
    (H : Fin W → Set Incidence) (a : Fin p.C) (S₁ : Set Incidence) (π : Measure ℝ) (τ : ℝ) :
    Prop where
  room : sg (p.lev a) + u + δ₀ ≤ 1 / 2
  τ_pos : 0 < τ
  τ_ε : τ⁻¹ ≤ Nk ^ (ε / 4000000)
  τ_u : τ⁻¹ ≤ Nk ^ (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 4)
  τ_half : τ⁻¹ ≤ Nk ^ (1 / 2 : ℝ)
  π_prob : IsProbabilityMeasure π
  S_meas : MeasurableSet S₁
  S_res : S₁ ⊆ H (p.world a)
  S_open : S₁ ⊆ p.assigned a ×ˢ Ioo ((p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
    (((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a))
  S_term : S₁ ⊆ TerminalInc W p.C m p.lev p.world p.counted (p.world a)
  S_end : ∀ z ∈ S₁, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
    z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)
  mass : (m : ℝ) * τ * (((ν (p.world a)).prod volume) (p.packet a)).toReal <
    (((ν (p.world a)).prod volume) S₁).toReal
  models : ∀ D : SourceData p, D.parent = a → D.π = π → D.S ⊆ S₁ → MeasurableSet D.S →
    D.S.Nonempty → D.D₀ = MajorFrame.frame (p.frame a) →
    D.K = (Nk ^ (u * L)) ^ (ρ / (1000000 * ((n : ℝ) + 1))) →
    D.depth = sourceDepth m sg (p.lev a) u →
    ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet D.parent) ≤
      ((ν D.w₀).prod volume) (D.S ∩ p.counted D.parent) →
    (∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → ∀ i : Fin (p.activeCount D.Hm (D.depth s)),
      ENNReal.ofReal τ * ((ν D.w₀).prod volume) (p.packet (D.old s i)) ≤
        ((ν D.w₀).prod volume) (D.S ∩ p.counted (D.old s i))) →
    (∃ c, D.Tracks n ℓ u Nk L ν B c) ∧ D.VelCaps n u Nk L ν B ∧
      EH2 d₁ S (D.stage Nk L u ν B) n

/-- **The per-sample parts interface of the source preparation.** -/
def SourcePartsSpec : Prop :=
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
        ∃ (a : Fin p.C) (S₁ : Set Incidence) (π : Measure ℝ) (τ : ℝ),
          SourceParts p n m s d₁ ℓ S ρ u δ₀ ε (N k) L (ν k) (B k) H a S₁ π τ

/-- **`SourceInputsSpec` from the parts.** -/
theorem sourceInputsSpec_of_parts (h : SourcePartsSpec) : SourceInputsSpec := by
  intro d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  obtain ⟨u₀, hu₀, hU⟩ := h d₁ κ₁ ℓ S η ρ hd hd' hκ hκ' hℓ hS hS' hη hρ hρ' n hn
  refine ⟨u₀, hu₀, fun u hu hu' => ?_⟩
  obtain ⟨g₀, hg₀, hG⟩ := hU u hu hu'
  set θ := ρ / (1000000 * ((n : ℝ) + 1)) with hθ
  have hθ0 : 0 < θ := by positivity
  refine ⟨min g₀ (u * θ), lt_min hg₀ (by positivity),
    fun gain hg hg' m s δ₀ hgrid hδ₀ hδ₀' => ?_⟩
  have hgain : gain ≤ g₀ := le_trans hg' (min_le_left _ _)
  have hguθ : gain ≤ u * θ := le_trans hg' (min_le_right _ _)
  intro N K L d W ω ν E P B f g G hprob hprof Mp Dp
  obtain ⟨Mprep, hP⟩ := hG gain hg hgain m s δ₀ hgrid hδ₀ hδ₀' N K L d W ω ν E P B f g G
    hprob hprof Mp Dp
  refine ⟨Mprep, fun ε hε => ?_⟩
  obtain ⟨σp, hσp, kp, hPk⟩ := hP ε hε
  refine ⟨σp, hσp, kp, fun σ hσ hσ' k hk p hp H hH hmass => ?_⟩
  rcases hPk σ hσ hσ' k hk p hp H hH hmass with hc | ⟨a, S₁, π, τ, hpt⟩
  · exact Or.inl hc
  right
  obtain ⟨hNge, -, hL, -, -, hνp, -, -⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic N K L d S η W ω ν E P B f g G
      hprob
  have hN1 : (1 : ℝ) ≤ N k := by linarith [hNge k]
  have hN0 : (0 : ℝ) < N k := by linarith
  have : IsProbabilityMeasure (ν k (p.world a)) := hνp k _
  -- prune `S₁`
  have hS₁a : S₁ ⊆ p.packet a := fun z hz =>
    ⟨(hpt.S_open hz).1, Set.Ioo_subset_Icc_self (hpt.S_open hz).2⟩
  obtain ⟨S₂, hS₂₁, hS₂m, hS₂mass, hS₂fl⟩ :=
    exists_local_floors hp a hpt.S_meas hS₁a hpt.τ_pos.le
  have hS₂ne : S₂.Nonempty := by
    have hpos : 0 < (((ν k (p.world a)).prod volume) S₂).toReal := by
      linarith [hpt.mass]
    apply nonempty_of_measure_ne_zero (μ := (ν k (p.world a)).prod volume)
    intro h0
    rw [h0] at hpos
    simp at hpos
  -- the models
  let D₁ : SourceData p := ⟨a, MajorFrame.frame (p.frame a), (N k ^ (u * L)) ^ θ, π, S₂,
    sourceDepth m s (p.lev a) u, fun _ _ _ => 0⟩
  have hi₀ : p.lev a < m := hp.label_level a
  have hge : ∀ D : SourceData p, D.parent = a → D.depth = sourceDepth m s (p.lev a) u →
      ∀ x, D.i₀ ≤ D.depth x := by
    intro D hDa hDd x
    rw [hDd, SourceData.i₀, hDa]
    exact sourceDepth_ge s hi₀ hu.le x
  have hopen : ∀ D : SourceData p, D.parent = a → D.S = S₂ →
      D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀) := by
    intro D hDa hDS
    rw [D.t₀_add_q₀, hDS]
    intro z hz
    have h := hpt.S_open (hS₂₁ hz)
    rw [SourceData.t₀, SourceData.i₀, hDa]
    exact h
  have hterm : ∀ D : SourceData p, D.parent = a → D.S = S₂ →
      D.S ⊆ TerminalInc (W k) p.C m p.lev p.world p.counted D.w₀ := by
    intro D hDa hDS
    rw [hDS, SourceData.w₀, hDa]
    exact hS₂₁.trans hpt.S_term
  have hfloors : ∀ D : SourceData p, D.parent = a → D.S = S₂ →
      D.depth = sourceDepth m s (p.lev a) u →
      (ENNReal.ofReal τ * ((ν k D.w₀).prod volume) (p.packet D.parent) ≤
        ((ν k D.w₀).prod volume) (D.S ∩ p.counted D.parent)) ∧
      (∀ x : ℝ, ∀ i : Fin (p.activeCount D.Hm (D.depth x)),
        ENNReal.ofReal τ * ((ν k D.w₀).prod volume) (p.packet (D.old x i)) ≤
          ((ν k D.w₀).prod volume) (D.S ∩ p.counted (D.old x i))) := by
    intro D hDa hDS hDd
    apply D.floors_of_desc hp (hge D hDa hDd) (hopen D hDa hDS) (hterm D hDa hDS)
      (by rw [hDS]; exact hS₂ne)
    intro b hb hanc hne
    rw [hDS] at hne ⊢
    rw [SourceData.w₀, hDa]
    rw [hDa] at hb hanc
    exact hS₂fl b hb hanc hne
  obtain ⟨hpf₁, hlf₁⟩ := hfloors D₁ rfl rfl rfl
  obtain ⟨⟨c, hc⟩, -, -⟩ := hpt.models D₁ rfl rfl hS₂₁ hS₂m hS₂ne rfl rfl rfl hpf₁
    (fun x _ _ i => hlf₁ x i)
  let D : SourceData p := ⟨a, MajorFrame.frame (p.frame a), (N k ^ (u * L)) ^ θ, π, S₂,
    sourceDepth m s (p.lev a) u, c⟩
  obtain ⟨hpf, hlf⟩ := hfloors D rfl rfl rfl
  obtain ⟨-, hvel, heh2⟩ := hpt.models D rfl rfl hS₂₁ hS₂m hS₂ne rfl rfl rfl hpf
    (fun x _ _ i => hlf x i)
  -- the determinant floors
  have hroom' : s D.i₀ + u ≤ s (m - 1) := by
    rw [hgrid.1.2.2.2]
    have := hpt.room
    have : s D.i₀ + u + δ₀ ≤ 1 / 2 := this
    linarith
  have hKdet : N k ^ (4 * δ₀ * L) ≤ D.K := by
    show N k ^ (4 * δ₀ * L) ≤ (N k ^ (u * L)) ^ θ
    rw [← Real.rpow_mul hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have h1 : δ₀ ≤ ρ * (u * θ) := hδ₀'.trans (mul_le_mul_of_nonneg_left hguθ hρ.le)
    have h2 : ρ * (u * θ) ≤ u * θ / 4 := by
      have : 0 ≤ u * θ := by positivity
      nlinarith
    have h3 : 4 * δ₀ ≤ u * θ := by linarith
    nlinarith [hL]
  have hdet := D.det_field hp n (u := u) (mesh := ρ * gain) rfl rfl (hopen D rfl rfl) hN1
    hL.le hℓ.le hu.le hgrid.1.1 (by positivity) (fineGrid_mesh hgrid) hroom' hKdet
  refine ⟨D, τ, rfl, rfl, rfl, hpt.room, hpt.τ_pos, hpt.τ_ε, hpt.τ_u, hpt.τ_half, ?_⟩
  exact
    { π_prob := hpt.π_prob
      S_meas := hS₂m
      S_res := hS₂₁.trans hpt.S_res
      S_open := hopen D rfl rfl
      S_term := hterm D rfl rfl
      S_end := fun z hz => hpt.S_end z (hS₂₁ hz)
      parent_floor := hpf
      label_floor := fun x _ _ i => hlf x i
      det := hdet
      track := hc
      vel := hvel
      eh2 := heh2 }

/-- **The source preparation from its parts.** -/
theorem sourcePreparation_of_parts (h : SourcePartsSpec) : SourcePreparation :=
  sourcePreparation_of_spec (sourceInputsSpec_of_parts h)

end

end Submission.Obl.k4_finite_affine_parent_sources
