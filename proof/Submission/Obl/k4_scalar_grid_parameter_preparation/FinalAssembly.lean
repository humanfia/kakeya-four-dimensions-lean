import Submission.Obl.k4_scalar_grid_parameter_preparation.EntryInterface
import Submission.Obl.k4_scalar_grid_parameter_preparation.AssemblyHelpers
import Submission.Obl.k4_scalar_grid_parameter_preparation.ScalarRegularizedPreparation
import Submission.Obl.k4_scalar_grid_parameter_preparation.SequenceCoefficientCaps
import Submission.Obl.k4_scalar_grid_parameter_preparation.PhysicalGridCertificate
import Submission.Obl.k4_scalar_grid_parameter_preparation.SequencePaletteFloors
import Submission.Obl.k4_scalar_grid_parameter_preparation.SlowCoefficientFloors
import Submission.Obl.k4_scalar_grid_parameter_preparation.CommonScaleMasks

/-!
# The preparation of o228, assembled

`prep_core_of_claim` derives `PrepConclusion` from the frozen hypotheses and the entry-stage
interface `EntryStageClaim`, through six deletions of one common mask:

1. regularized prior `θ ≤ ν`, trace core `Z` and density band `E₁` (x0317);
2. mixed coefficient upper caps on `θ` (x0317);
3. physical support counts on the stage grid `Γ k = positiveScaleGrid (M k) (J k)` (x0317, x0796);
4. palette floors of physical cells and velocity bins on `Γ k` (x0317);
5. coefficient-bin floors on a slowly growing part `Ξ k` of `Γ k` (x0796);
6. coefficient lists on `Ξ k` (the entry stage).

The losses are `5, 2, 1, 1, 1` hundredths of `1 / K` in every world, so the weighted mass stays
above `1 / (2 K)`.
-/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

theorem smul_le_smul_measure {α : Type*} [MeasurableSpace α] {a b : ℝ≥0∞} (hab : a ≤ b)
    {μ ν : Measure α} (h : μ ≤ ν) : a • μ ≤ b • ν := by
  rw [Measure.le_iff']
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' hab (h s)

theorem prep_core_of_claim (hclaim : EntryStageClaim)
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : (∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (d κ S : ℝ) (hd : 0 ≤ d) (hd1 : d < 1) (_hκ : 0 < κ) (hκ1 : κ ≤ 1) (hS : 0 < S)
    (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 5 → ℝ)))
    (ρ : (k : ℕ) → Fin (W k) → Measure ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (π : (k : ℕ) → Fin (W k) → Measure ℝ)
    (T n : ℕ → ℝ → ℕ) (γ : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (W k))
    (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
    (A : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set (ℕ × (Fin 5 → ℝ)))
    (u v : (k : ℕ) → (s : ℝ) → Fin (n k s) → ℝ)
    (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 2) ℝ)
    (hbase : FrozenBase K W ω ν ρ π) (hcaps : FrozenCaps N K d S W ρ π)
    (hpackets : FrozenPackets N K d κ W ν ρ T n γ j A u v F) :
    PrepConclusion N d W ω ν ρ π := by
  classical
  have hNpos : ∀ k, 0 < N k := fun k => by linarith [hN k]
  have hK1 : ∀ k, 1 ≤ K k := hK.1
  have hKpos : ∀ k, 0 < K k := fun k => by linarith [hK1 k]
  have hKsub : Subpower N K := hK
  have hfin : ∀ k g, IsFiniteMeasure (ρ k g) := frozen_finite hbase
  have hν : ∀ k g, IsProbabilityMeasure (ν k g) := fun k g => ((hbase k).2.2.1 g).1
  have hπ : ∀ k g, IsProbabilityMeasure (π k g) := fun k g => ((hbase k).2.2.1 g).2.1
  -- Stage 1: regularized prior, trace core and density band.
  obtain ⟨H₁, θ, E₁, Z, hH₁, hH₁sub, -, hE₁, htrace⟩ :=
    exists_scalar_regularized_preparation N K hN hNt hK W ν ρ π d (frozen_base_regularized hbase)
      (frozen_joint_caps hcaps) ω (fun k => ⟨(hbase k).1, (hbase k).2.1⟩)
      (fun k => (hbase k).2.2.2)
  have hH₁s : Subpower N H₁ := ⟨fun k => (hH₁ k).1, hH₁sub⟩
  have hθν : ∀ k g, θ k g ≤ ν k g := fun k g => (hE₁ k g).1
  have hθ1 : ∀ k g, θ k g Set.univ ≤ 1 := fun k g => (hE₁ k g).2.1
  have hE₁m : ∀ k g, MeasurableSet (E₁ k g) := fun k g => (hE₁ k g).2.2.1
  have hE₁Z : ∀ k g, E₁ k g ⊆ Z k g := fun k g => (hE₁ k g).2.2.2.1
  have hZm : ∀ k g, MeasurableSet (Z k g) := fun k g => (hE₁ k g).2.2.2.2.1
  have hZ : ∀ k g, ∀ p ∈ Z k g, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ K k :=
    fun k g => (hE₁ k g).2.2.2.2.2.1
  have hθb : ∀ k g, ∀ᵐ l ∂θ k g, ∀ e, |l.2 e| ≤ H₁ k := fun k g => (hE₁ k g).2.2.2.2.2.2.1
  have hloss₁ : ∀ k g, ρ k g (E₁ k g)ᶜ ≤ ENNReal.ofReal (5 / (100 * K k)) :=
    fun k g => (hE₁ k g).2.2.2.2.2.2.2.1
  have hlow₁ : ∀ k g, ENNReal.ofReal ((H₁ k)⁻¹) • ((θ k g).prod volume).restrict (E₁ k g) ≤
      (ρ k g).restrict (E₁ k g) := fun k g => (hE₁ k g).2.2.2.2.2.2.2.2.1
  have hup₁ : ∀ k g, (ρ k g).restrict (E₁ k g) ≤
      ENNReal.ofReal (H₁ k) • ((θ k g).prod volume).restrict (E₁ k g) :=
    fun k g => (hE₁ k g).2.2.2.2.2.2.2.2.2.1
  have hdur : ∀ k g (C : Set (ℕ × (Fin 5 → ℝ))), MeasurableSet C →
      ENNReal.ofReal (1 / (100 * K k)) * θ k g C ≤ (ρ k g).restrict (Z k g) (C ×ˢ Set.univ) :=
    fun k g => (hE₁ k g).2.2.2.2.2.2.2.2.2.2
  have hKH₁ : ∀ k, K k ≤ H₁ k := fun k => by linarith [(hH₁ k).2, hK1 k]
  -- Stage 2: mixed coefficient upper caps.
  obtain ⟨L, hL, hLsub, hmixed⟩ := exists_subpower_mixed_coefficient_caps N K H₁ hN hNt hK hH₁s W
    ν θ ρ π Z d
    (fun k g => ⟨hν k g, hZm k g, fun p hp => ⟨Set.mem_univ _, (hZ k g p hp).1⟩,
      (frozen_base_regularized hbase k g).2.2.1⟩)
    hdur htrace
  have hLs : Subpower N L := ⟨fun k => (hL k).1, hLsub⟩
  -- Stage 3: physical support on the stage grid.
  obtain ⟨H₂, M, E₂, hH₂, hM, hE₂, hloss₂, hphys₂, J, hJM, hJt, hstage₂⟩ :=
    exists_scalar_physical_preparation_on_grid N K hN hNt hK W Prod.snd measurable_snd ν ρ π E₁
      d S hS (fun k g => ⟨hν k g, hE₁m k g, fun p hp => hZ k g p (hE₁Z k g hp)⟩) hfin
      (frozen_original_caps hcaps) (frozen_pure_physical hcaps)
      (frozen_packet_sequence hN hK1 hκ1 hpackets)
  have hH₂s : Subpower N H₂ := hH₂
  let Γ : ℕ → Finset ℝ := fun k => positiveScaleGrid (M k) (J k)
  let code : ℕ → ℝ → (ℕ × (Fin 5 → ℝ)) × ℝ → Fin 3 → ℤ :=
    fun k r p => physicalScalarGridTag (N k ^ (-r)) (scalarPacketPosition Prod.snd p)
  have hcodem : ∀ k r, Measurable (code k r) := by
    intro k r
    apply Measurable.of_eval
    intro i
    dsimp only [code, physicalScalarGridTag]
    have hm := measurable_scalarPacketPosition
      (a := (Prod.snd : ℕ × (Fin 5 → ℝ) → Fin 5 → ℝ)) measurable_snd
    fun_prop
  have hE₂E₁ : ∀ k g, E₂ k g ⊆ E₁ k g := fun k g => (hE₂ k g).2
  -- Stage 4: palette floors of physical cells and velocity bins.
  obtain ⟨P, E₃, hP, hE₃, hfloor₃⟩ := exists_sequence_palette_floors N K H₂ hN hNt hK hH₂ W ρ π hπ
    E₂ (fun k g => ⟨(hE₂ k g).1, measure_ne_top _ _⟩) Γ code
    (fun k r c => measurableSet_eq_fun (hcodem k r) measurable_const) (fun p => p.1.2 1)
    (by fun_prop)
    (fun k g p hp => (hZ k g p (hE₁Z k g (hE₂E₁ k g hp))).2 1) d
    (by
      filter_upwards [hstage₂] with k hk
      refine ⟨hk.1, fun g r hr => ?_⟩
      have h := hk.2 g r hr
      rw [Set.image_image] at h
      exact ⟨h.1, h.2.1⟩)
  have hE₃E₂ : ∀ k g, E₃ k g ⊆ E₂ k g := fun k g => (hE₃ k g).2
  have hE₃E₁ : ∀ k g, E₃ k g ⊆ E₁ k g := fun k g => (hE₃E₂ k g).trans (hE₂E₁ k g)
  -- Stage 5: coefficient-bin floors.
  let Kc : ℕ → ℝ := fun k => max (max (H₁ k) (L k)) (P k)
  have hKcs : Subpower N Kc :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max
      (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hH₁s hLs) hP
  have hH₁Kc : ∀ k, H₁ k ≤ Kc k := fun k => (le_max_left _ _).trans (le_max_left _ _)
  have hLKc : ∀ k, L k ≤ Kc k := fun k => (le_max_right _ _).trans (le_max_left _ _)
  have hPKc : ∀ k, P k ≤ Kc k := fun k => le_max_right _ _
  have hPpos : ∀ k, 0 < P k := fun k => lt_of_lt_of_le zero_lt_one (hP.1 k)
  have hH₁pos : ∀ k, 0 < H₁ k := fun k => lt_of_lt_of_le zero_lt_one (hH₁ k).1
  have hpower := original_coefficient_deficiency_power_bound N Kc hN hNt hKcs W Prod.snd
    measurable_snd θ ρ π E₃ Γ d hd hd1 hfin
    (fun k g => by
      have := isFiniteMeasure_of_le (ν k g) (hθν k g)
      infer_instance) hπ
    (fun k g => (hθb k g).mono fun l hl e => (hl e).trans (hH₁Kc k))
    (fun k g => ⟨(hE₃ k g).1, fun z hz => ⟨(hZ k g z (hE₁Z k g (hE₃E₁ k g hz))).1,
      fun e => ((hZ k g z (hE₁Z k g (hE₃E₁ k g hz))).2 e).trans ((hKH₁ k).trans (hH₁Kc k))⟩⟩)
    (fun k g => by
      constructor
      · refine (restrict_le_smul_of_subset (hE₃ k g).1 (hE₃E₁ k g) _ (hup₁ k g)).trans ?_
        exact smul_le_smul_measure (ENNReal.ofReal_le_ofReal (hH₁Kc k)) Measure.restrict_le_self
      · refine le_trans ?_ (smul_restrict_le_of_subset (hE₃ k g).1 (hE₃E₁ k g) _ (hlow₁ k g))
        exact smul_le_smul_measure (ENNReal.ofReal_le_ofReal
          (inv_anti₀ (hH₁pos k) (hH₁Kc k))) le_rfl)
    (by
      intro R hR
      filter_upwards [hfloor₃, hstage₂] with k hf hs
      intro g r hr1 hr2 hrΓ
      refine ⟨(hs.2 g r hrΓ).1.subset (Set.image_mono (Set.image_mono (hE₃E₂ k g))), ?_⟩
      intro z hz
      refine le_trans ?_ ((hf g).2 r hrΓ z hz)
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
        (Real.rpow_nonneg (hNpos k).le _) (hPpos k) (hPKc k))) _)
    (by
      intro R hR
      filter_upwards [hmixed R hR] with k hk
      intro g r s hr1 hr2 hs1 hs2 z
      refine (hk g r s hr1 hr2 hs1 hs2 z).trans ?_
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hLKc k)
        (Real.rpow_nonneg (hNpos k).le _))) _)
  obtain ⟨Hf, J', Ξ, E₄, hHf, -, -, hΞ, hE₄, hloss₄, hfloor₄, hΞmem⟩ :=
    exists_slow_coefficient_floors N K H₂ hN hNt hK hH₂ W Prod.snd measurable_snd θ ρ π E₃
      (fun k g => (hE₃ k g).1) Γ (hstage₂.mono fun k hk => hk.1) d hpower
  have hE₄E₃ : ∀ k g, E₄ k g ⊆ E₃ k g := fun k g => (hE₄ k g).2
  have hE₄E₁ : ∀ k g, E₄ k g ⊆ E₁ k g := fun k g => (hE₄E₃ k g).trans (hE₃E₁ k g)
  have hΞΓ : ∀ k, Ξ k ⊆ Γ k := fun k => by rw [hΞ k]; exact Finset.filter_subset _ _
  -- Stage 6: coefficient lists.
  let Hc : ℕ → ℝ := fun k => max (max (Kc k) (Hf k)) (H₂ k)
  have hHcs : Subpower N Hc :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max
      (Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hKcs hHf) hH₂s
  have hKcHc : ∀ k, Kc k ≤ Hc k := fun k => (le_max_left _ _).trans (le_max_left _ _)
  have hHfHc : ∀ k, Hf k ≤ Hc k := fun k => (le_max_right _ _).trans (le_max_left _ _)
  have hH₂Hc : ∀ k, H₂ k ≤ Hc k := fun k => le_max_right _ _
  have hHfpos : ∀ k, 0 < Hf k := fun k => lt_of_lt_of_le zero_lt_one (hHf.1 k)
  obtain ⟨Hl, E₅, hHl, hE₅, hloss₅, hlists⟩ := hclaim N K Hc W d θ ρ π Ξ E₄ hN hNt hKsub hHcs hd
    hd1 hfin hθ1 hπ
    (by
      filter_upwards [hstage₂] with k hk
      refine le_trans ?_ (hk.1.trans (hH₂Hc k))
      exact_mod_cast Finset.card_le_card (hΞΓ k))
    (fun k r hr => by
      have hb := positiveScaleGrid_mem_bounds (Nat.lt_of_lt_of_le Nat.zero_lt_one (hM k).1)
        (hΞΓ k hr)
      exact lt_of_lt_of_le (by
        have : (0 : ℝ) < M k := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (hM k).1)
        positivity) hb.1)
    (fun k g => ⟨(hE₄ k g).1, fun p hp => ⟨(hZ k g p (hE₁Z k g (hE₄E₁ k g hp))).1,
      fun e => ((hZ k g p (hE₁Z k g (hE₄E₁ k g hp))).2 e).trans
        ((hKH₁ k).trans ((hH₁Kc k).trans (hKcHc k)))⟩⟩)
    (fun k g => by
      refine (restrict_le_smul_of_subset (hE₄ k g).1 (hE₄E₁ k g) _ (hup₁ k g)).trans ?_
      exact smul_le_smul_measure (ENNReal.ofReal_le_ofReal ((hH₁Kc k).trans (hKcHc k)))
        Measure.restrict_le_self)
    (fun k g r hr z hz => by
      have h := hfloor₄ k g r hr z hz
      rw [scalarMixedCoefficientTag_self] at h
      simp only [scalarMixedCoefficientTag_self] at h
      refine le_trans ?_ h
      rw [velBin_eq]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
        (Real.rpow_nonneg (hNpos k).le _) (hHfpos k) (hHfHc k))) _)
    (by
      intro R hR
      filter_upwards [frozen_joint_physical hcaps R hR] with k hk
      intro g r hr1 hr2 q c
      refine (hk g r hr1 hr2 q c).trans ?_
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        ((hKH₁ k).trans ((hH₁Kc k).trans (hKcHc k))) (Real.rpow_nonneg (hNpos k).le _))) _)
  have hE₅E₄ : ∀ k g, E₅ k g ⊆ E₄ k g := fun k g => (hE₅ k g).2
  have hE₅E₂ : ∀ k g, E₅ k g ⊆ E₂ k g :=
    fun k g => (hE₅E₄ k g).trans ((hE₄E₃ k g).trans (hE₃E₂ k g))
  have hE₅E₁ : ∀ k g, E₅ k g ⊆ E₁ k g := fun k g => (hE₅E₂ k g).trans (hE₂E₁ k g)
  -- The certificate.
  let H₀ : ℕ → ℝ := fun k => max (Hc k) (Hl k)
  have hH₀s : Subpower N H₀ :=
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.subpower_max hHcs hHl
  have hHcH₀ : ∀ k, Hc k ≤ H₀ k := fun k => le_max_left _ _
  have hHlH₀ : ∀ k, Hl k ≤ H₀ k := fun k => le_max_right _ _
  have hH₁H₀ : ∀ k, H₁ k ≤ H₀ k := fun k => (hH₁Kc k).trans ((hKcHc k).trans (hHcH₀ k))
  have hLH₀ : ∀ k, L k ≤ H₀ k := fun k => (hLKc k).trans ((hKcHc k).trans (hHcH₀ k))
  have hH₂H₀ : ∀ k, H₂ k ≤ H₀ k := fun k => (hH₂Hc k).trans (hHcH₀ k)
  have hHfH₀ : ∀ k, Hf k ≤ H₀ k := fun k => (hHfHc k).trans (hHcH₀ k)
  have hKH₀ : ∀ k, K k ≤ H₀ k := fun k => (hKH₁ k).trans (hH₁H₀ k)
  have hH₀pos : ∀ k, 0 < H₀ k := fun k => lt_of_lt_of_le zero_lt_one (hH₀s.1 k)
  refine ⟨H₀, θ, E₅, hH₀s, M, fun k => ⟨(hM k).1, (hM k).2.trans (hH₂H₀ k)⟩, ?_⟩
  intro R hR
  have hRpos : 0 < R := by linarith
  filter_upwards [hloss₂, hfloor₃, hloss₄, hloss₅, hphys₂ R hR, hmixed R hR, htrace R hR,
    hΞmem R hR, hlists R hR, hJt.eventually_ge_atTop ⌈R⌉₊] with
    k hl₂ hf₃ hl₄ hl₅ hph hmx htr hΞm hli hJk
  refine ⟨?_, fun g => ?_⟩
  · -- The weighted mass.
    have h := retained_weighted_mass (ρ k) (ω k) (E₅ k) (hKpos k) (hbase k).1 (hbase k).2.1
      (hbase k).2.2.2 (fun g => compl_le_of_chain (ρ k g) (hKpos k) (hloss₁ k g) (hl₂ g)
        (hf₃ g).1 (hl₄ g) (hl₅ g))
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
    rw [one_div]
    exact inv_anti₀ (by linarith [hKpos k]) (by linarith [(hH₁ k).2, hH₁H₀ k, hKpos k])
  refine ⟨hθν k g, hθ1 k g, (hE₅ k g).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := hZ k g p (hE₁Z k g (hE₅E₁ k g hp))
    exact ⟨h1, fun e => (h2 e).trans (hKH₀ k)⟩
  · exact (hθb k g).mono fun l hl e => (hl e).trans (hH₁H₀ k)
  · refine le_trans ?_ (smul_restrict_le_of_subset (hE₅ k g).1 (hE₅E₁ k g) _ (hlow₁ k g))
    exact smul_le_smul_measure (ENNReal.ofReal_le_ofReal (inv_anti₀ (hH₁pos k) (hH₁H₀ k))) le_rfl
  · refine (restrict_le_smul_of_subset (hE₅ k g).1 (hE₅E₁ k g) _ (hup₁ k g)).trans ?_
    exact smul_le_smul_measure (ENNReal.ofReal_le_ofReal (hH₁H₀ k)) le_rfl
  · intro r hr1 hr2 hgrid
    have hrpos : 0 < r := lt_of_lt_of_le (inv_pos.mpr hRpos) hr1
    have hrΓ : r ∈ Γ k := mem_positiveScaleGrid_of_grid_scale
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (hM k).1) hrpos
      (hr2.trans ((Nat.le_ceil R).trans (by exact_mod_cast hJk))) hgrid
    have hrΞ : r ∈ Ξ k := hΞm r hr1 hr2 hrΓ
    obtain ⟨hfin₂, hcount₂, -, hher₂⟩ := hph g r hr1 hr2 hgrid
    have hsub : {q : Fin 3 → ℤ | (ρ k g).restrict (E₅ k g) {p | physTag (N k) r p = q} ≠ 0} ⊆
        physicalScalarGridTag (N k ^ (-r)) '' (scalarPacketPosition Prod.snd '' E₂ k g) := by
      intro q hq
      obtain ⟨p, hp, hpq⟩ := exists_mem_of_restrict_ne_zero (hE₅ k g).1 hq
      exact ⟨scalarPacketPosition Prod.snd p, ⟨p, hE₅E₂ k g hp, rfl⟩, hpq⟩
    refine ⟨hfin₂.subset hsub, ?_, ?_, ?_, ?_⟩
    · refine (Nat.cast_le.mpr (Set.ncard_le_ncard hsub hfin₂)).trans (hcount₂.trans ?_)
      exact mul_le_mul_of_nonneg_right (hH₂H₀ k) (Real.rpow_nonneg (hNpos k).le _)
    · intro r₀ hr₀1 hr₀2 hgrid₀ q₀
      have h := hher₂ r₀ hr₀1 hr₀2 hgrid₀ (E₅ k g) (hE₅E₂ k g) q₀
      exact h.2.trans (mul_le_mul_of_nonneg_right (hH₂H₀ k) (Real.rpow_nonneg (hNpos k).le _))
    · intro q hq
      obtain ⟨z, hz, hzq⟩ := exists_mem_of_restrict_ne_zero (hE₅ k g).1 hq
      have hzq' : coeffTag (N k) r z.1 = q := hzq
      constructor
      · have h := hfloor₄ k g r hrΞ z (hE₅E₄ k g hz)
        simp only [scalarMixedCoefficientTag_self] at h
        rw [hzq'] at h
        have hq1 : ⌊z.1.2 1 / N k ^ (-r)⌋ = q 1 := by rw [← hzq']; rfl
        rw [hq1] at h
        refine le_trans ?_ h
        rw [velBin_eq, show -(1 + d) * r = -((1 + d) * r) by ring]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left
          (Real.rpow_nonneg (hNpos k).le _) (hHfpos k) (hHfH₀ k))) _
      · have h := hmx g r r hr1 hr2 hr1 hr2 q
        simp only [scalarMixedCoefficientTag_self] at h
        refine h.trans ?_
        rw [velBin_eq, show -(1 + d) * r = -r - d * r by ring]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hLH₀ k)
          (Real.rpow_nonneg (hNpos k).le _))) _
    · intro q c
      exact (hli g r hrΞ hr1 hr2 q c).trans (hHlH₀ k)
  · intro r s b t hr1 hr2 hs1 hs2 hb1 hb2 _ q a c
    calc
      θ k g {l | (l, t) ∈ E₅ k g ∧ (⌊trajY l t / (N k ^ (-r))⌋ : ℤ) = q ∧
          (⌊trajX l t / (N k ^ (-s))⌋ : ℤ) = a ∧ l.2 1 ∈ velBin (N k) b c}
          ≤ ν k g {l | (l, t) ∈ Z k g ∧ l.2 0 + t * l.2 1 ∈ scalarVelocityBin (N k ^ (-r)) q ∧
            l.2 2 + t * l.2 3 + t ^ 2 * l.2 4 ∈ scalarVelocityBin (N k ^ (-s)) a ∧
            l.2 1 ∈ scalarVelocityBin (N k ^ (-b)) c} := by
        refine (hθν k g _).trans (measure_mono ?_)
        rintro l ⟨h1, h2, h3, h4⟩
        exact ⟨hE₁Z k g (hE₅E₁ k g h1), h2, h3, h4⟩
      _ ≤ ENNReal.ofReal (H₁ k * N k ^ (-r - d * s)) *
            π k g (scalarVelocityBin (N k ^ (-b)) c) :=
        htr g r s b hr1 hr2 hs1 hs2 hb1 hb2 t q a c
      _ ≤ ENNReal.ofReal (H₀ k * N k ^ (-r - d * s)) * π k g (velBin (N k) b c) := by
        rw [velBin_eq]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hH₁H₀ k)
          (Real.rpow_nonneg (hNpos k).le _))) _

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
