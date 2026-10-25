-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionSample
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionSchedule
import Submission.Obl.k4_finite_affine_parent_sources.SourceResidual
import Submission.Obl.k4_finite_affine_parent_sources.OriginalAxisCharge
import Submission.Obl.k4_finite_affine_parent_sources.PaletteDepthMenu
import Submission.Obl.k4_finite_affine_parent_sources.SourceSelectionNumbers

/-!
# The selection component from the per-sample selection

`sourceSelectionSpec_of_sample : SelectionSample → SourceSelectionSpec` (x0812 proves
`SelectionSample`). The outer schedule chooses the raw-upgrade window `T, N₀`
(`exists_rawUpgrade`), the unit `u₀`, the gain `g₀`, `Mprep = 1`, the depth grid `Qd` (round up,
mesh `hd`), the angular menu `Qa` (x0807's `exists_positive_angular_depth_menu` plus the axis
width `uLβ/2`), the tolerances, the floor `τ = Nk^(-a_τ)`, the slack bound and the cutoff; at the
sample it masks the residual (densities at `Qd`, terminal lower density, angular densities at
`Qa`), prunes the axis-deficient labels (x0923's `prune_original_full_axes` with
`deficient_level_power_charge`), and checks the remaining mass `≥ (4κ)⁻¹ ≥ 1/(4κ²)`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set Filter

noncomputable section

/-- Mixed candidates survive enlarging the residual. -/
theorem mixedCandidate_mono_set {Nk L : ℝ} {W : ℕ} {ν : Fin W → Measure Trajectory}
    {B : Fin W → ℝ} {Mc : ℕ} {d₁ ρ gain ε : ℝ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {A : Fin C → Set Trajectory} {H H' : Fin W → Set Incidence} (hHH : ∀ w, H w ⊆ H' w)
    (h : MixedCandidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j u Q A H) :
    MixedCandidate Nk L W ν B Mc d₁ ρ gain ε r T C lev γ j u Q A H' := by
  obtain ⟨b, h, hg, hu, hr, hpos, hcase⟩ := h
  refine ⟨b, h, hg, hu, hr, hpos, ?_⟩
  rcases hcase with ⟨R, hR, hc, hm⟩ | ⟨a, z, ha, hz, hm⟩
  · exact Or.inl ⟨R, hR, hc, hm.trans (measure_mono fun q hq => ⟨hHH _ hq.1, hq.2⟩)⟩
  · exact Or.inr ⟨a, z, ha, hz, hm.trans (measure_mono fun q hq => ⟨hHH _ hq.1, hq.2⟩)⟩

/-- A finite depth grid of `[0, L]` containing `L` that rounds every depth up by at most `hd`. -/
theorem exists_roundup_grid {L hd : ℝ} (hL : 0 ≤ L) (hd0 : 0 < hd) :
    ∃ Q : Finset ℝ, L ∈ Q ∧ (∀ r ∈ Q, 0 ≤ r ∧ r ≤ L) ∧
      ∀ t, 0 ≤ t → t ≤ L → ∃ r ∈ Q, t ≤ r ∧ r ≤ t + hd := by
  classical
  set M := ⌈L / hd⌉₊ with hM
  refine ⟨(Finset.range (M + 1)).image (fun j : ℕ => min L ((j : ℝ) * hd)), ?_, ?_, ?_⟩
  · rw [Finset.mem_image]
    refine ⟨M, Finset.mem_range.mpr (Nat.lt_succ_self M), ?_⟩
    apply min_eq_left
    have := Nat.le_ceil (L / hd)
    rw [div_le_iff₀ hd0] at this
    exact this
  · intro r hr
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨le_min hL (by positivity), min_le_left _ _⟩
  · intro t ht0 htL
    set j := ⌈t / hd⌉₊ with hj
    have hjM : j ≤ M := Nat.ceil_mono (div_le_div_of_nonneg_right htL hd0.le)
    refine ⟨min L ((j : ℝ) * hd),
      Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩, ?_, ?_⟩
    · have h1 := Nat.le_ceil (t / hd)
      rw [div_le_iff₀ hd0] at h1
      exact le_min htL h1
    · have h2 := Nat.ceil_lt_add_one (div_nonneg ht0 hd0.le)
      have h3 : (j : ℝ) * hd < (t / hd + 1) * hd := mul_lt_mul_of_pos_right h2 hd0
      have h4 : (t / hd + 1) * hd = t + hd := by field_simp
      calc min L ((j : ℝ) * hd) ≤ (j : ℝ) * hd := min_le_right _ _
        _ ≤ t + hd := by linarith

/-- x0812's package with a floor `τ` and the floor facts is the output of the selection
component. -/
theorem selectionOutput_of_package {W : ℕ} {p : PathData W} {ν : Fin W → Measure Trajectory}
    {B : Fin W → ℝ} {Nk L : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {n : ℕ} {ℓ ρ u d₁ S ε : ℝ}
    {H : Fin W → Set Incidence} {τ : ℝ}
    (h : SelectionPackage p ν B Nk L m s δ₀ n ℓ ρ u d₁ S H τ) (hτ : 0 < τ)
    (h1 : τ⁻¹ ≤ Nk ^ (ε / 4000000))
    (h2 : τ⁻¹ ≤ Nk ^ (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 4))
    (h3 : τ⁻¹ ≤ Nk ^ (1 / 2 : ℝ)) :
    SelectionOutput p n m s d₁ ℓ S ρ u δ₀ ε Nk L ν B H := by
  obtain ⟨a, Gm, π, hGm, hGH, hroom, hb1, hb2, hfull, hroom2, hπ, hmodels⟩ := h
  refine ⟨a, Gm, π, τ, hGm, hGH, hroom, hb1, hb2, hfull, hroom2, hτ, h1, h2, h3, hπ, ?_⟩
  intro D hDa hDπ hDS hDm hDne hD₀ hDK hDd hDo hDend hfa hfl hpf hlf
  exact hmodels D hDa hDπ hDS hDm hDne hD₀ hDK hDd hDo hDend hfa hfl hpf hlf

/-- The angular observation map is measurable. -/
theorem measurable_angularObs (Bw a c : ℝ) :
    Measurable (fun z : Incidence => (obs Bw a z, fun j : Fin 2 => ⌊(v z.1) j / c⌋)) := by
  refine (Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.measurable_obs
    _ _).prodMk ?_
  refine measurable_pi_iff.mpr fun j => Int.measurable_floor.comp (Measurable.div_const ?_ c)
  fin_cases j
  · exact (measurable_pi_apply 3).comp (measurable_snd.comp measurable_fst)
  · exact (measurable_pi_apply 4).comp (measurable_snd.comp measurable_fst)

/-- The selection mask set of one world. -/
def selectionMaskSet (Nk L S τd τa : ℝ) (f : ℝ → ℝ) (Bw : ℝ)
    (gw : ℝ → Observation → ENNReal) (Gw : ℝ → Observation × (Fin 2 → ℤ) → ENNReal)
    (Qd Qa : Finset ℝ) : Set Incidence :=
  {z | SelectionMask Nk L S τd τa f Bw gw Gw Qd Qa z}

theorem selectionMaskSet_eq (Nk L S τd τa : ℝ) (f : ℝ → ℝ) (Bw : ℝ)
    (gw : ℝ → Observation → ENNReal) (Gw : ℝ → Observation × (Fin 2 → ℤ) → ENNReal)
    (Qd Qa : Finset ℝ) :
    selectionMaskSet Nk L S τd τa f Bw gw Gw Qd Qa =
      (⋂ r ∈ Qd, {z | gw r (obs Bw (δ Nk r) z) ≤ ENNReal.ofReal (Nk ^ (-f r + τd))}) ∩
        {z | ENNReal.ofReal (Nk ^ (-f L - τd)) ≤ gw L (obs Bw (δ Nk L) z)} ∩
        ⋂ r ∈ Qa, {z | Gw r (obs Bw (δ Nk L) z, fun j : Fin 2 => ⌊(v z.1) j / δ Nk r⌋) ≤
          ENNReal.ofReal (Nk ^ (-f L - S * r + τa))} := by
  ext z
  simp only [selectionMaskSet, SelectionMask, mem_ofPred_eq, mem_inter_iff, mem_iInter, and_assoc]

theorem measurableSet_selectionMaskSet {Nk L S τd τa : ℝ} {f : ℝ → ℝ} {Bw : ℝ}
    {gw : ℝ → Observation → ENNReal} {Gw : ℝ → Observation × (Fin 2 → ℤ) → ENNReal}
    {Qd Qa : Finset ℝ} (hgm : ∀ r ∈ Qd, Measurable (gw r)) (hgL : Measurable (gw L))
    (hGm : ∀ r ∈ Qa, Measurable (Gw r)) :
    MeasurableSet (selectionMaskSet Nk L S τd τa f Bw gw Gw Qd Qa) := by
  have hobs := Submission.Obl.k4_remainder_pure_profile_normalization.Normalization.measurable_obs
  rw [selectionMaskSet_eq]
  refine ((Finset.measurableSet_biInter Qd fun r hr => ?_).inter ?_).inter
    (Finset.measurableSet_biInter Qa fun r hr => ?_)
  · exact measurableSet_le ((hgm r hr).comp (hobs _ _)) measurable_const
  · exact measurableSet_le measurable_const (hgL.comp (hobs _ _))
  · exact measurableSet_le ((hGm r hr).comp (measurable_angularObs _ _ _)) measurable_const

/-- **The mass outside the selection masks** is at most the upper pure-density tails on the
depth grid, the terminal lower tail and the angular tails on the menu. -/
theorem selectionMask_loss {W : ℕ} (Nk L S τ : ℝ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (E : Fin W → Set Incidence) (B : Fin W → ℝ)
    (f : ℝ → ℝ) (g : Fin W → ℝ → Observation → ENNReal)
    (G : Fin W → ℝ → Observation × (Fin 2 → ℤ) → ENNReal) (Qd Qa : Finset ℝ) :
    (∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w))
      (selectionMaskSet Nk L S τ τ f (B w) (g w) (G w) Qd Qa)ᶜ) ≤
      (∑ r ∈ Qd, k4_fixed_menu_density_pruning.upperTail Nk W ω ν E B f g τ r) +
        lowerTail Nk L W ω ν E B f g τ +
        ∑ r ∈ Qa, angularTail Nk L S W ω ν E B f G τ r := by
  unfold k4_fixed_menu_density_pruning.upperTail lowerTail angularTail
  rw [Finset.sum_comm (s := Qd), Finset.sum_comm (s := Qa), ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, ← mul_add]
  refine mul_le_mul' le_rfl ?_
  set μ := ((ν w).prod volume).restrict (E w)
  have hsub : (selectionMaskSet Nk L S τ τ f (B w) (g w) (G w) Qd Qa)ᶜ ⊆
      ((⋃ r ∈ Qd, {p | ENNReal.ofReal (Nk ^ (-f r + τ)) < g w r (obs (B w) (δ Nk r) p)}) ∪
        {p | g w L (obs (B w) (δ Nk L) p) < ENNReal.ofReal (Nk ^ (-f L - τ))}) ∪
        ⋃ r ∈ Qa, {p | ENNReal.ofReal (Nk ^ (-f L - S * r + τ)) <
          G w r (obs (B w) (δ Nk L) p, fun j : Fin 2 => ⌊(v p.1) j / δ Nk r⌋)} := by
    intro z hz
    simp only [selectionMaskSet, SelectionMask, mem_compl_iff, mem_ofPred_eq, not_and_or,
      not_forall, not_le, exists_prop] at hz
    simp only [mem_union, mem_iUnion, mem_ofPred_eq, exists_prop]
    rcases hz with ⟨r, hr, h⟩ | h | ⟨r, hr, h⟩
    · exact Or.inl (Or.inl ⟨r, hr, h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨r, hr, h⟩
  calc μ (selectionMaskSet Nk L S τ τ f (B w) (g w) (G w) Qd Qa)ᶜ
      ≤ μ (((⋃ r ∈ Qd, {p | ENNReal.ofReal (Nk ^ (-f r + τ)) <
            g w r (obs (B w) (δ Nk r) p)}) ∪
          {p | g w L (obs (B w) (δ Nk L) p) < ENNReal.ofReal (Nk ^ (-f L - τ))}) ∪
          ⋃ r ∈ Qa, {p | ENNReal.ofReal (Nk ^ (-f L - S * r + τ)) <
            G w r (obs (B w) (δ Nk L) p, fun j : Fin 2 => ⌊(v p.1) j / δ Nk r⌋)}) :=
        measure_mono hsub
    _ ≤ μ ((⋃ r ∈ Qd, {p | ENNReal.ofReal (Nk ^ (-f r + τ)) <
            g w r (obs (B w) (δ Nk r) p)}) ∪
          {p | g w L (obs (B w) (δ Nk L) p) < ENNReal.ofReal (Nk ^ (-f L - τ))}) +
        μ (⋃ r ∈ Qa, {p | ENNReal.ofReal (Nk ^ (-f L - S * r + τ)) <
            G w r (obs (B w) (δ Nk L) p, fun j : Fin 2 => ⌊(v p.1) j / δ Nk r⌋)}) :=
        measure_union_le _ _
    _ ≤ (∑ r ∈ Qd, μ {p | ENNReal.ofReal (Nk ^ (-f r + τ)) <
            g w r (obs (B w) (δ Nk r) p)} +
          μ {p | g w L (obs (B w) (δ Nk L) p) < ENNReal.ofReal (Nk ^ (-f L - τ))}) +
        ∑ r ∈ Qa, μ {p | ENNReal.ofReal (Nk ^ (-f L - S * r + τ)) <
            G w r (obs (B w) (δ Nk L) p, fun j : Fin 2 => ⌊(v p.1) j / δ Nk r⌋)} := by
        gcongr
        · exact (measure_union_le _ _).trans (add_le_add (measure_biUnion_finset_le _ _) le_rfl)
        · exact measure_biUnion_finset_le _ _

/-- Arithmetic of the tail count. -/
theorem card_tail_sum (a b : ℕ) (x : ENNReal) :
    (a : ENNReal) * x + x + (b : ENNReal) * x = ((a + b + 1 : ℕ) : ENNReal) * x := by
  push_cast
  ring

section Masks

open scoped Classical
open Submission.Lib.K4XInterface

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **The masked and axis-pruned residual of one sample.** -/
theorem masked_residual [hν : ∀ w, IsProbabilityMeasure (ν w)]
    (hω0 : ∀ w, 0 ≤ ω w) (hω1 : ∑ w, ω w = 1)
    (hE : ∀ w, E w ⊆ univ ×ˢ Icc (0 : ℝ) 1) (hm : 0 < m) (hNk : 1 ≤ Nk) (hL : 0 ≤ L)
    (hδ : δ₀ ≤ 1 / 2) (S η : ℝ)
    (g : Fin W → ℝ → Observation → ENNReal)
    (G : Fin W → ℝ → Observation × (Fin 2 → ℤ) → ENNReal)
    (hg : ∀ w r, 0 ≤ r → r ≤ L → Measurable (g w r) ∧
      Measure.map (obs (B w) (δ Nk r)) (((ν w).prod volume).restrict (E w)) =
        (volume.prod Measure.count).withDensity (g w r))
    (hG : ∀ w u, 0 < u → u ≤ η * L → Measurable (G w u) ∧
      Measure.map (fun z : Incidence =>
          (obs (B w) (δ Nk L) z, fun j : Fin 2 => ⌊(v z.1) j / δ Nk u⌋))
        (((ν w).prod volume).restrict (E w)) =
        ((volume.prod Measure.count).prod Measure.count).withDensity (G w u))
    (Qd Qa : Finset ℝ) (hQd : ∀ r ∈ Qd, 0 ≤ r ∧ r ≤ L)
    (hQa : ∀ r ∈ Qa, 0 < r ∧ r ≤ η * L) {a : ℝ} (ha : a ∈ Qa) (τt : ℝ)
    {Hf : ℝ} (hHf : 0 < Hf) (hfull : 4 / Hf ≤ Nk ^ (-a) * p.κ)
    (H : Fin W → Set Incidence)
    (hH : ∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc W p.C m p.lev p.world p.counted w)
    (hmass : (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω w) *
        (ν w).prod volume (TerminalInc W p.C m p.lev p.world p.counted w)) ≤
      ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w))
    {c : ℝ}
    (hup : ∀ r ∈ Qd, k4_fixed_menu_density_pruning.upperTail Nk W ω ν E B f g τt r ≤
      ENNReal.ofReal (Nk ^ (-c)))
    (hlow : lowerTail Nk L W ω ν E B f g τt ≤ ENNReal.ofReal (Nk ^ (-c)))
    (hang : ∀ r ∈ Qa, angularTail Nk L S W ω ν E B f G τt r ≤ ENNReal.ofReal (Nk ^ (-c)))
    (hbudget : ((Qd.card + Qa.card + 1 : ℕ) : ℝ) * Nk ^ (-c) +
      (m : ℝ) * (130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τt) + 2 * p.κ * (2 * Nk ^ (-c))) ≤
        (4 * p.κ)⁻¹) :
    ∃ H' : Fin W → Set Incidence, (∀ w, MeasurableSet (H' w) ∧ H' w ⊆ H w) ∧
      (∀ w, ∀ z ∈ H' w, SelectionMask Nk L S τt τt f (B w) (g w) (G w) Qd Qa z) ∧
      (∀ b : Fin p.C, sg (p.lev b) ≤ 1 / 2 → (H' (p.world b) ∩ p.counted b).Nonempty →
        ¬p.axisDeficient (Nk ^ (-a)) b ∧
          ((2 : ℝ) ^ p.T (p.lev b))⁻¹ / Hf ≤
            Submission.Obl.k4_compatible_pair_frame_preparation.Construction.r₁ (p.frame b)) ∧
      ENNReal.ofReal ((4 * p.κ)⁻¹) ≤
        ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H' w) := by
  have hκ := hp.one_le_slack
  have hκ0 : 0 < p.κ := by linarith
  -- the masks
  set M : Fin W → Set Incidence :=
    fun w => selectionMaskSet Nk L S τt τt f (B w) (g w) (G w) Qd Qa with hM
  have hMm : ∀ w, MeasurableSet (M w) := fun w =>
    measurableSet_selectionMaskSet (fun r hr => (hg w r (hQd r hr).1 (hQd r hr).2).1)
      (hg w L hL le_rfl).1 (fun r hr => (hG w r (hQa r hr).1 (hQa r hr).2).1)
  set H₁ : Fin W → Set Incidence := fun w => H w ∩ M w with hH₁
  have hH₁m : ∀ w, MeasurableSet (H₁ w) := fun w => (hH w).1.inter (hMm w)
  -- the axis prune
  set loss : ENNReal := ENNReal.ofReal (130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τt)) *
      (∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) univ) +
    ENNReal.ofReal (2 * p.κ) *
      ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w))
        {z | ENNReal.ofReal (Nk ^ (-f L - S * a + τt)) <
            G w a (gobs (B w) (gδ Nk L) z, fun e : Fin 2 => ⌊gv z.1 e / gδ Nk a⌋) ∨
          g w L (gobs (B w) (gδ Nk L) z) < ENNReal.ofReal (Nk ^ (-f L - τt))} with hloss
  have hbad : ∀ i : ℕ, i < m → sg i ≤ 1 / 2 →
      (∑ b, if p.lev b = i ∧ p.axisDeficient (Nk ^ (-a)) b then
        ENNReal.ofReal (ω (p.world b)) * (ν (p.world b)).prod volume (p.counted b) else 0) ≤
        loss := by
    intro i hi hsi
    obtain ⟨hr0, hrL⟩ := hp.nominal_half_depth_bounds hL hδ i hi hsi
    exact hp.deficient_level_power_charge hE hNk i hr0.le hrL a S τt (fun w => g w L)
      (fun w => (hg w L hL le_rfl).1) (fun w => (hg w L hL le_rfl).2)
      (fun w => G w a) (fun w => (hG w a (hQa a ha).1 (hQa a ha).2).1)
      (fun w => (hG w a (hQa a ha).1 (hQa a ha).2).2)
  obtain ⟨H₂, hH₂, hmass₂, hfull₂⟩ := prune_original_full_axes hp H₁ hH₁m
    (fun i => sg i ≤ 1 / 2) (Nk ^ (-a)) Hf hHf hfull loss hbad
  refine ⟨H₂, fun w => ⟨(hH₂ w).1, (hH₂ w).2.trans inter_subset_left⟩,
    fun w z hz => ((hH₂ w).2 hz).2, fun b hb hne => hfull₂ b hb hne, ?_⟩
  -- mass accounting
  have hNc : 0 ≤ Nk ^ (-c) := Real.rpow_nonneg (by linarith) _
  have hNa : 0 ≤ Nk ^ (-S * a + 2 * τt) := Real.rpow_nonneg (by linarith) _
  have hκ5 : 0 ≤ 130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τt) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hκ0.le 5)) hNa
  have h2κ : 0 ≤ 2 * p.κ := by linarith
  have h2N : 0 ≤ 2 * Nk ^ (-c) := mul_nonneg (by norm_num) hNc
  have h2κN : 0 ≤ 2 * p.κ * (2 * Nk ^ (-c)) := mul_nonneg h2κ h2N
  have hX : 0 ≤ 130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τt) + 2 * p.κ * (2 * Nk ^ (-c)) :=
    add_nonneg hκ5 h2κN
  have hY : 0 ≤ ((Qd.card + Qa.card + 1 : ℕ) : ℝ) * Nk ^ (-c) :=
    mul_nonneg (Nat.cast_nonneg _) hNc
  have hmX : 0 ≤ (m : ℝ) * (130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τt) +
      2 * p.κ * (2 * Nk ^ (-c))) := mul_nonneg (Nat.cast_nonneg _) hX
  have h4κ : 0 ≤ (4 * p.κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hHE : ∀ w, H w ⊆ E w := by
    intro w z hz
    obtain ⟨b, -, hbw, hzb⟩ := (hH w).2 hz
    have := (hp.counted_support b z hzb).1
    rwa [hbw] at this
  have hres := hp.residual_mass_lower hm H hmass
  have hsplit : (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w)) ≤
      (∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H₁ w)) +
        ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) (M w)ᶜ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [← mul_add]
    refine mul_le_mul' le_rfl ?_
    rw [Measure.restrict_apply (hMm w).compl]
    calc (ν w).prod volume (H w) ≤ (ν w).prod volume (H₁ w ∪ ((M w)ᶜ ∩ E w)) := by
          apply measure_mono
          intro z hz
          by_cases hzM : z ∈ M w
          · exact Or.inl ⟨hz, hzM⟩
          · exact Or.inr ⟨hzM, hHE w hz⟩
      _ ≤ _ := measure_union_le _ _
  have hmaskloss : (∑ w, ENNReal.ofReal (ω w) *
      (((ν w).prod volume).restrict (E w)) (M w)ᶜ) ≤
      ENNReal.ofReal (((Qd.card + Qa.card + 1 : ℕ) : ℝ) * Nk ^ (-c)) := by
    refine (selectionMask_loss Nk L S τt ω ν E B f g G Qd Qa).trans ?_
    have h1 : (∑ r ∈ Qd, k4_fixed_menu_density_pruning.upperTail Nk W ω ν E B f g τt r) ≤
        Qd.card * ENNReal.ofReal (Nk ^ (-c)) := by
      calc _ ≤ ∑ _r ∈ Qd, ENNReal.ofReal (Nk ^ (-c)) := Finset.sum_le_sum hup
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : (∑ r ∈ Qa, angularTail Nk L S W ω ν E B f G τt r) ≤
        Qa.card * ENNReal.ofReal (Nk ^ (-c)) := by
      calc _ ≤ ∑ _r ∈ Qa, ENNReal.ofReal (Nk ^ (-c)) := Finset.sum_le_sum hang
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    calc _ ≤ Qd.card * ENNReal.ofReal (Nk ^ (-c)) + ENNReal.ofReal (Nk ^ (-c)) +
          Qa.card * ENNReal.ofReal (Nk ^ (-c)) := add_le_add (add_le_add h1 hlow) h2
      _ = ENNReal.ofReal (((Qd.card + Qa.card + 1 : ℕ) : ℝ) * Nk ^ (-c)) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          exact card_tail_sum _ _ _
  have hunit : (∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) univ) ≤ 1 := by
    calc _ ≤ ∑ w, ENNReal.ofReal (ω w) * 1 := by
          refine Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl ?_
          rw [Measure.restrict_apply_univ]
          calc (ν w).prod volume (E w) ≤ (ν w).prod volume (univ ×ˢ Icc (0 : ℝ) 1) :=
                measure_mono (hE w)
            _ = 1 := by rw [Measure.prod_prod, measure_univ, Real.volume_Icc]; simp
      _ = 1 := by
          simp only [mul_one]
          rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => hω0 w), hω1, ENNReal.ofReal_one]
  have hunion : (∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w))
        {z | ENNReal.ofReal (Nk ^ (-f L - S * a + τt)) <
            G w a (gobs (B w) (gδ Nk L) z, fun e : Fin 2 => ⌊gv z.1 e / gδ Nk a⌋) ∨
          g w L (gobs (B w) (gδ Nk L) z) < ENNReal.ofReal (Nk ^ (-f L - τt))}) ≤
      ENNReal.ofReal (2 * Nk ^ (-c)) := by
    calc _ ≤ angularTail Nk L S W ω ν E B f G τt a + lowerTail Nk L W ω ν E B f g τt := by
          unfold angularTail lowerTail
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun w _ => ?_
          rw [← mul_add]
          exact mul_le_mul' le_rfl ((measure_mono fun z hz => hz).trans (measure_union_le _ _))
      _ ≤ ENNReal.ofReal (Nk ^ (-c)) + ENNReal.ofReal (Nk ^ (-c)) :=
          add_le_add (hang a ha) hlow
      _ = ENNReal.ofReal (2 * Nk ^ (-c)) := by
          rw [← ENNReal.ofReal_add hNc hNc]
          ring_nf
  have hlossb : loss ≤ ENNReal.ofReal (130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τt) +
      2 * p.κ * (2 * Nk ^ (-c))) := by
    calc loss ≤ ENNReal.ofReal (130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τt)) * 1 +
          ENNReal.ofReal (2 * p.κ) * ENNReal.ofReal (2 * Nk ^ (-c)) :=
        add_le_add (mul_le_mul' le_rfl hunit) (mul_le_mul' le_rfl hunion)
      _ = _ := by
        rw [mul_one, ← ENNReal.ofReal_mul h2κ, ← ENNReal.ofReal_add hκ5 h2κN]
  have h2 : ENNReal.ofReal ((4 * p.κ)⁻¹) + ENNReal.ofReal ((4 * p.κ)⁻¹) =
      ENNReal.ofReal ((2 * p.κ)⁻¹) := by
    rw [← ENNReal.ofReal_add h4κ h4κ]
    congr 1
    field_simp
    ring
  have hfinal : ENNReal.ofReal ((4 * p.κ)⁻¹) + ENNReal.ofReal ((4 * p.κ)⁻¹) ≤
      (∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H₂ w)) +
        ENNReal.ofReal ((4 * p.κ)⁻¹) := by
    rw [h2]
    calc ENNReal.ofReal ((2 * p.κ)⁻¹)
        ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (H w) := hres
      _ ≤ _ := hsplit
      _ ≤ ((∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H₂ w)) + (m : ENNReal) * loss) +
          ∑ w, ENNReal.ofReal (ω w) * (((ν w).prod volume).restrict (E w)) (M w)ᶜ :=
          add_le_add hmass₂ le_rfl
      _ ≤ ((∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H₂ w)) +
            ENNReal.ofReal (m : ℝ) * ENNReal.ofReal (130 * p.κ ^ 5 *
              Nk ^ (-S * a + 2 * τt) + 2 * p.κ * (2 * Nk ^ (-c)))) +
          ENNReal.ofReal (((Qd.card + Qa.card + 1 : ℕ) : ℝ) * Nk ^ (-c)) := by
          rw [ENNReal.ofReal_natCast]
          exact add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hlossb)) hmaskloss
      _ = (∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (H₂ w)) +
          ENNReal.ofReal (((Qd.card + Qa.card + 1 : ℕ) : ℝ) * Nk ^ (-c) +
            (m : ℝ) * (130 * p.κ ^ 5 * Nk ^ (-S * a + 2 * τt) + 2 * p.κ * (2 * Nk ^ (-c)))) := by
          rw [← ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_add hY hmX]
          ring
      _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal hbudget)
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hfinal

end Masks

/-- The output of the selection component is monotone in the residual. -/
theorem selectionOutput_mono {W : ℕ} {p : PathData W} {n m : ℕ} {s : ℕ → ℝ}
    {d₁ ℓ S ρ u δ₀ ε Nk L : ℝ} {ν : Fin W → Measure Trajectory} {B : Fin W → ℝ}
    {H H' : Fin W → Set Incidence} (hHH : ∀ w, H w ⊆ H' w)
    (h : SelectionOutput p n m s d₁ ℓ S ρ u δ₀ ε Nk L ν B H) :
    SelectionOutput p n m s d₁ ℓ S ρ u δ₀ ε Nk L ν B H' := by
  obtain ⟨a, Gm, π, τ, hGm, hGH, rest⟩ := h
  exact ⟨a, Gm, π, τ, hGm, hGH.trans (hHH _), rest⟩

/-- **The selection at one sample**, from x0812's per-sample selection and the masked residual. -/
theorem selection_at_sample (hS : SelectionSample)
    {d₁ κ₁ ℓ S η ρ : ℝ} {n : ℕ} {u gain : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {N K : ℕ → ℝ} {L d : ℝ} {W : ℕ → ℕ} {ω : (k : ℕ) → Fin (W k) → ℝ}
    {ν : (k : ℕ) → Fin (W k) → Measure Trajectory}
    {E : (k : ℕ) → Fin (W k) → Set Incidence}
    {P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ} {B : (k : ℕ) → Fin (W k) → ℝ}
    {f : ℝ → ℝ} {g : (k : ℕ) → Fin (W k) → ℝ → Observation → ENNReal}
    {G : (k : ℕ) → Fin (W k) → ℝ → Observation × (Fin 2 → ℤ) → ENNReal}
    {Mp Dp : ℕ} {ε σ : ℝ} {k : ℕ} {p : PathData (W k)} {T N₀ τt hd ma aτ c : ℝ}
    {Qd Qa : Finset ℝ}
    (hd₁ : 0 ≤ d₁) (hd₁' : d₁ < 1) (hκ₁ : 0 < κ₁) (hκ₁' : κ₁ ≤ 1) (hℓ : 0 < ℓ) (hS₀ : 0 < S)
    (hS' : S ≤ 1) (hη : 0 < η) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 4) (hn : 2 ≤ n) (hu : 0 < u)
    (hg : 0 < gain) (hgrid : FineGrid m s gain ρ) (hδ₀ : 0 < δ₀) (hδ₀' : δ₀ ≤ ρ * gain)
    (hδ : δ₀ ≤ 1 / 2) (hprob : prob N K L d S η W ω ν E P B f g G)
    (hprof : ∀ q : ℝ, 0 ≤ q → q ≤ L → |f q - f 0 - d₁ * q| ≤ δ₀ * L) (hε : 0 < ε) (hσ : 0 < σ)
    (hp : p.Valid ℓ (N k) L (ω k) (ν k) (E k) (B k) f κ₁ m s δ₀ Mp Dp σ)
    (hnT : (n : ℝ) < T) (hup : RawUpgrade n T N₀)
    (hu1 : u * T * (((n : ℝ) + 2) ^ 2 * ((groupsC : ℝ) + 2)) * 10 ^ 15 ≤ κ₁ * ρ)
    (hu2 : u * ((n : ℝ) + 2) ≤ η) (hu3 : u * ((n : ℝ) + 2) ≤ ℓ / 8)
    (hg1 : gain * (10 ^ 12 * ((n : ℝ) + 1) * ((groupsC : ℝ) + 2)) ≤ u)
    (hLQd : L ∈ Qd) (hQd : ∀ r ∈ Qd, 0 ≤ r ∧ r ≤ L) (hhd : 0 < hd)
    (hQdc : ∀ t, 0 ≤ t → t ≤ L → ∃ r ∈ Qd, t ≤ r ∧ r ≤ t + hd)
    (hQa : ∀ r ∈ Qa, 0 < r ∧ r ≤ η * L) (hma : 0 < ma)
    (hQac : ∀ t, u * L / n ≤ t → t ≤ u * L * n → ∃ r ∈ Qa, t - ma ≤ r ∧ r ≤ t)
    (hτt : 0 ≤ τt) (hτtb : τt ≤ selectionBudget n ρ u L) (hhdb : hd ≤ selectionBudget n ρ u L)
    (hmab : ma ≤ selectionBudget n ρ u L)
    (hax : u * L * min (stagePower n ρ / 1000) (ℓ / 1000) / 2 ∈ Qa)
    (hN₀ : N₀ ≤ N k ^ (u * L))
    (hconst : p.κ ^ 20 * K k ^ 4 * selectionConst m n T κ₁ ρ u L ≤
      N k ^ selectionBudget n ρ u L)
    (h2κ : 2 * p.κ ≤ N k ^ (1 : ℝ))
    (hfloor : N k ^ (-aτ) * (10 ^ 6 * ((m : ℝ) + 1) ^ 2 * p.κ ^ 12) ≤ 1)
    (hτ1 : (N k ^ (-aτ))⁻¹ ≤ N k ^ (ε / 4000000))
    (hτ2 : (N k ^ (-aτ))⁻¹ ≤ N k ^ (u * (ρ / (1000000 * ((n : ℝ) + 1))) * L / 4))
    (hτ3 : (N k ^ (-aτ))⁻¹ ≤ N k ^ (1 / 2 : ℝ))
    (hupT : ∀ r ∈ Qd, k4_fixed_menu_density_pruning.upperTail (N k) (W k) (ω k) (ν k) (E k)
      (B k) f (g k) τt r ≤ ENNReal.ofReal (N k ^ (-c)))
    (hlowT : lowerTail (N k) L (W k) (ω k) (ν k) (E k) (B k) f (g k) τt ≤
      ENNReal.ofReal (N k ^ (-c)))
    (hangT : ∀ r ∈ Qa, angularTail (N k) L S (W k) (ω k) (ν k) (E k) (B k) f (G k) τt r ≤
      ENNReal.ofReal (N k ^ (-c)))
    (hbudget : ((Qd.card + Qa.card + 1 : ℕ) : ℝ) * N k ^ (-c) +
      (m : ℝ) * (130 * p.κ ^ 5 * N k ^ (-S * (u * L * min (stagePower n ρ / 1000) (ℓ / 1000) / 2)
        + 2 * τt) + 2 * p.κ * (2 * N k ^ (-c))) ≤ (4 * p.κ)⁻¹)
    (hfull : 4 / N k ^ (u * L * min (stagePower n ρ / 1000) (ℓ / 1000)) ≤
      N k ^ (-(u * L * min (stagePower n ρ / 1000) (ℓ / 1000) / 2)) * p.κ)
    (H : Fin (W k) → Set Incidence)
    (hH : ∀ w, MeasurableSet (H w) ∧ H w ⊆ TerminalInc (W k) p.C m p.lev p.world p.counted w)
    (hmass : (1 / 2 : ENNReal) * (∑ w, ENNReal.ofReal (ω k w) *
        ((ν k w).prod volume) (TerminalInc (W k) p.C m p.lev p.world p.counted w)) ≤
      ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H w)) :
    MixedCandidate (N k) L (W k) (ν k) (B k) 1 d₁ ρ gain ε
        p.r p.T p.C p.lev p.world p.bin p.velocity p.frame p.assigned H ∨
      SelectionOutput p n m s d₁ ℓ S ρ u δ₀ ε (N k) L (ν k) (B k) H := by
  obtain ⟨hNge, -, hL0, hω0, hω1, hνp, -, hE⟩ :=
    Submission.Obl.k4_quadratic_finite_greedy_cover.prob_basic N K L d S η W ω ν E P B f g G
      hprob
  have hprob' := hprob
  obtain ⟨_, _, _, _, _, _, _, _, _, hgm, hGm, _⟩ := hprob'
  have : ∀ w, IsProbabilityMeasure (ν k w) := hνp k
  have hN1 : (1 : ℝ) ≤ N k := le_trans (by norm_num) (hNge k)
  have hm : 0 < m := hgrid.1.1
  have hκ := hp.one_le_slack
  -- the masked residual
  have hN0 : (0 : ℝ) < N k := lt_of_lt_of_le one_pos hN1
  have hHf0 : 0 < N k ^ (u * L * min (stagePower n ρ / 1000) (ℓ / 1000)) :=
    Real.rpow_pos_of_pos hN0 _
  obtain ⟨H', hH'm, hH'mask, hH'axis, hH'mass⟩ :=
    masked_residual hp (ω := ω k) (ν := ν k) (E := E k) (B := B k) (hω0 k) (hω1 k) (hE k) hm
      hN1 hL0.le hδ S η (g k) (G k) (fun w r h0 h1 => hgm k w r h0 h1)
      (fun w u' h0 h1 => hGm k w u' h0 h1) Qd Qa hQd hQa hax τt hHf0 hfull H hH hmass hupT
      hlowT hangT hbudget
  have hmass' : ENNReal.ofReal (1 / (4 * p.κ ^ 2)) ≤
      ∑ w, ENNReal.ofReal (ω k w) * ((ν k w).prod volume) (H' w) := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hH'mass
    rw [one_div]
    apply inv_anti₀ (by positivity)
    nlinarith
  have hτpos : 0 < N k ^ (-aτ) := Real.rpow_pos_of_pos hN0 _
  rcases hS d₁ κ₁ ℓ S η ρ n u gain m s δ₀ N K L d W ω ν E P B f g G Mp Dp 1 ε σ k p H' T N₀
      (N k ^ (-aτ)) τt τt hd ma Qd Qa hd₁ hd₁' hκ₁ hκ₁' hℓ hS₀ hS' hη hρ hρ' hn hu hg hgrid
      hδ₀ hδ₀' hprob hprof hε hσ hp hnT hup hu1 hu2 hu3 hg1 hLQd hQd hhd hQdc hQa hma hQac
      hτt hτt hτtb hτtb hhdb hmab hN₀ hconst (by rw [Nat.cast_one]; exact h2κ) hτpos hfloor
      (fun w => ⟨(hH'm w).1, (hH'm w).2.trans (hH w).2⟩) hH'mask hH'axis hmass' with hc | hpkg
  · exact Or.inl (mixedCandidate_mono_set (fun w => (hH'm w).2) hc)
  · exact Or.inr (selectionOutput_mono (fun w => (hH'm w).2)
      (selectionOutput_of_package hpkg hτpos hτ1 hτ2 hτ3))

end

end Submission.Obl.k4_finite_affine_parent_sources
