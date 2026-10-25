/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Match/MatchGroupN.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
/- Adapted within this LOT tree (g-oai-074) from o227 `k4_horizontal_three_projection_wide_return`,
session x0788, branch x0788, commit d1137a70, file
Submission/Obl/k4_horizontal_three_projection_wide_return/MatchGroupN.lean (namespace renamed into o250's). -/
import Mathlib
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Match.MatchQuad
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Match.MatchCor
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Match.MatchGroup

/-!
# One jet group of the sliced matching lemma

Members carry full coefficient vectors `F : Fin n → ℝ` (binned at scale `M`) and the
frozen `Match` premise is applied to a linear one-variable slice `S F : Fin 3 → ℝ`.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGroupN

open MeasureTheory MatchQuad MatchCor MatchGroup

/-- `match_quadL` for fixed constants. -/
def MatchQL (d η : ℝ) (L N₀ : ℝ) : Prop :=
  ∀ N : ℝ, N₀ ≤ N →
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (a₁ : ι₁ → Fin 3 → ℝ) (a₂ : ι₂ → Fin 3 → ℝ) (π₁ : ι₁ → ℝ) (π₂ : ι₂ → ℝ)
      (μ : Measure ((ι₁ × ι₂) × ℝ)),
      (Fintype.card ι₁ : ℝ) ≤ N ^ (d + η) → (Fintype.card ι₂ : ℝ) ≤ N ^ (d + η) →
      (∀ i k, |a₁ i k| ≤ L) → (∀ j k, |a₂ j k| ≤ L) →
      (∀ i, 0 ≤ π₁ i) → (∀ j, 0 ≤ π₂ j) → (∑ i, π₁ i) = 1 → (∑ j, π₂ j) = 1 →
      IsProbabilityMeasure μ →
      (∀ i (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * volume E) →
      (∀ j (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ j) * volume E) →
      ¬ (∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0:ℝ) 1 ∧
          |quad (a₁ p.1.1) p.2 - quad (a₂ p.1.2) p.2| ≤ 2 / N ∧
          1 ≤ cnorm (a₁ p.1.1 - a₂ p.1.2))

theorem matchQL_of_hyp (hM : MatchHyp) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ L : ℝ, 1 ≤ L → ∃ N₀ : ℝ, 2 ≤ N₀ ∧ MatchQL d η L N₀ := by
  obtain ⟨η, hη, H⟩ := match_quadL hM hd0 hd1
  refine ⟨η, hη, fun L hL => ?_⟩
  obtain ⟨N₀, hN₀, H'⟩ := H L hL
  exact ⟨N₀, hN₀, fun N hN ι₁ ι₂ _ _ _ _ _ _ => H' N hN ι₁ ι₂⟩

/-- Bins of full coefficient vectors at scale `M`. -/
noncomputable def binN {n : ℕ} (M : ℝ) (F : Fin n → ℝ) : Fin n → ℤ := fun k => ⌊F k / M⌋

lemma binN_sub_bounds {n : ℕ} {M : ℝ} (hM : 0 < M) (F : Fin n → ℝ) (k : Fin n) :
    0 ≤ F k - M * binN M F k ∧ F k - M * binN M F k < M := by
  have h1 := Int.floor_le (F k / M)
  have h2 := Int.lt_floor_add_one (F k / M)
  have e1 : M * (⌊F k / M⌋ : ℝ) ≤ F k := by
    have := mul_le_mul_of_nonneg_left h1 (le_of_lt hM); rwa [mul_div_cancel₀ _ (ne_of_gt hM)] at this
  have e2 : F k < M * ((⌊F k / M⌋ : ℝ) + 1) := by
    have := mul_lt_mul_of_pos_left h2 hM; rwa [mul_div_cancel₀ _ (ne_of_gt hM)] at this
  unfold binN; constructor <;> nlinarith

section Group

variable {n : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
  [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]

/-- The slice-far pairs of one group. -/
def groupN (M Crec : ℝ) (S : (Fin n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) (F₁ : ι₁ → Fin n → ℝ)
    (F₂ : ι₂ → Fin n → ℝ) (β δb : Fin n → ℤ) : Set ((ι₁ × ι₂) × ℝ) :=
  {p | binN M (F₁ p.1.1) = β ∧ binN M (F₂ p.1.2) = β + δb ∧
    M / Crec ≤ cnorm (S (F₁ p.1.1) - S (F₂ p.1.2))}

theorem groupN_le {d η L N₀ : ℝ} (hQ : MatchQL d η L N₀) (hη : 0 < η)
    (S : (Fin n → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) {Lop Crec : ℝ} (hLop : 0 ≤ Lop) (hCrec : 0 < Crec)
    (hop : ∀ (F : Fin n → ℝ) (X : ℝ), (∀ k, |F k| ≤ X) → ∀ k, |S F k| ≤ Lop * X)
    (hL : 3 * Lop * Crec ≤ L)
    (F₁ : ι₁ → Fin n → ℝ) (F₂ : ι₂ → Fin n → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
    (Q : Measure ((ι₁ × ι₂) × ℝ)) [IsFiniteMeasure Q]
    {δ M A : ℝ} (hδ : 0 < δ) (hM : 0 < M) (hN : N₀ ≤ M / (Crec * δ)) (hA1 : 1 ≤ A)
    (hA : A ≤ (M / (Crec * δ)) ^ η) (hAc : A * (M / δ) ^ d ≤ (M / (Crec * δ)) ^ (d + η))
    (hT₁ : ∀ i, 0 ≤ T₁ i) (hT₂ : ∀ j, 0 ≤ T₂ j)
    (hm₁ : ∀ i (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₁ i) * volume E)
    (hm₂ : ∀ j (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₂ j) * volume E)
    (hc₁ : ∀ r : Fin n → ℝ,
      ((Finset.univ.filter (fun i => ∀ k, |F₁ i k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d)
    (hc₂ : ∀ r : Fin n → ℝ,
      ((Finset.univ.filter (fun j => ∀ k, |F₂ j k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d)
    (hae : ∀ᵐ p ∂Q, p.2 ∈ Set.Icc (0:ℝ) 1 ∧
      |quad (S (F₁ p.1.1)) p.2 - quad (S (F₂ p.1.2)) p.2| ≤ 2 * δ)
    (β δb : Fin n → ℤ) (hδb : ∀ k, |δb k| ≤ 2) :
    Q (groupN M Crec S F₁ F₂ β δb) ≤
      ENNReal.ofReal (A * (M / (Crec * δ)) ^ (-η) *
        ((∑ i ∈ Finset.univ.filter (fun i => binN M (F₁ i) = β), T₁ i) +
         (∑ j ∈ Finset.univ.filter (fun j => binN M (F₂ j) = β + δb), T₂ j))) := by
  classical
  set M' := M / Crec with hM'def
  have hM' : 0 < M' := div_pos hM hCrec
  set N := M / (Crec * δ) with hNdef
  have hNM' : N = M' / δ := by rw [hNdef, hM'def]; field_simp
  have hNpos : 0 < N := by rw [hNM']; exact div_pos hM' hδ
  set s₁ := Finset.univ.filter (fun i => binN M (F₁ i) = β) with hs₁def
  set s₂ := Finset.univ.filter (fun j => binN M (F₂ j) = β + δb) with hs₂def
  set W₁ := ∑ i ∈ s₁, T₁ i with hW₁def
  set W₂ := ∑ j ∈ s₂, T₂ j with hW₂def
  set θ := A * N ^ (-η) with hθdef
  have hθpos : 0 < θ := mul_pos (by linarith) (Real.rpow_pos_of_pos hNpos _)
  have hW₁nn : 0 ≤ W₁ := Finset.sum_nonneg (fun i _ => hT₁ i)
  have hW₂nn : 0 ≤ W₂ := Finset.sum_nonneg (fun j _ => hT₂ j)
  set G := groupN M Crec S F₁ F₂ β δb with hGdef
  have hGfst : G = {p : (ι₁ × ι₂) × ℝ | p.1 ∈ {x : ι₁ × ι₂ | binN M (F₁ x.1) = β ∧
      binN M (F₂ x.2) = β + δb ∧ M / Crec ≤ cnorm (S (F₁ x.1) - S (F₂ x.2))}} := by
    ext p; simp [hGdef, groupN]
  have hGm : MeasurableSet G := by rw [hGfst]; exact measurableSet_fst_preimage _
  by_contra hcon
  push Not at hcon
  set m := Q G with hmdef
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hcon; exact absurd hcon (not_lt.mpr zero_le)
  have hmtop : m ≠ ⊤ := measure_ne_top Q G
  have hGsub₁ : G ⊆ {p | p.1.1 ∈ s₁} := by
    intro p hp; simp only [hGfst, Set.mem_ofPred_eq] at hp; simp [hs₁def, hp.1]
  have hGsub₂ : G ⊆ {p | p.1.2 ∈ s₂} := by
    intro p hp; simp only [hGfst, Set.mem_ofPred_eq] at hp; simp [hs₂def, hp.2.1]
  have hW₁pos : 0 < W₁ := by
    rcases lt_or_eq_of_le hW₁nn with h | h
    · exact h
    exfalso; apply hm0
    apply le_antisymm _ zero_le
    refine le_trans (measure_mono hGsub₁) (le_of_eq (mass_fst_le Q T₁ hm₁ s₁ ?_))
    intro i hi
    have : T₁ i = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hT₁ i)).mp h.symm i hi
    rw [this, mul_zero]
  have hW₂pos : 0 < W₂ := by
    rcases lt_or_eq_of_le hW₂nn with h | h
    · exact h
    exfalso; apply hm0
    apply le_antisymm _ zero_le
    refine le_trans (measure_mono hGsub₂) (le_of_eq (mass_snd_le Q T₂ hm₂ s₂ ?_))
    intro j hj
    have : T₂ j = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hT₂ j)).mp h.symm j hj
    rw [this, mul_zero]
  let S₁ := {i : ι₁ // binN M (F₁ i) = β}
  let S₂ := {j : ι₂ // binN M (F₂ j) = β + δb}
  let base : Fin n → ℝ := fun k => M * β k
  let a₁ : S₁ → Fin 3 → ℝ := fun s k => S (F₁ s.1 - base) k / M'
  let a₂ : S₂ → Fin 3 → ℝ := fun s k => S (F₂ s.1 - base) k / M'
  let π₁ : S₁ → ℝ := fun s => T₁ s.1 / W₁
  let π₂ : S₂ → ℝ := fun s => T₂ s.1 / W₂
  let ψ : (S₁ × S₂) × ℝ → (ι₁ × ι₂) × ℝ := fun q => ((q.1.1.1, q.1.2.1), q.2)
  have hψ : MeasurableEmbedding ψ :=
    MeasurableEmbedding.prodMap
      (MeasurableEmbedding.prodMap (MeasurableEmbedding.subtype_coe MeasurableSet.of_discrete)
        (MeasurableEmbedding.subtype_coe MeasurableSet.of_discrete)) MeasurableEmbedding.id
  let μ : Measure ((S₁ × S₂) × ℝ) := m⁻¹ • (Q.restrict G).comap ψ
  have hμapp : ∀ X, μ X = m⁻¹ * Q (ψ '' X ∩ G) := by
    intro X
    simp only [μ, Measure.smul_apply, smul_eq_mul, hψ.comap_apply, Measure.restrict_apply' hGm]
  have hrange : G ⊆ ψ '' Set.univ := by
    intro p hp
    simp only [hGfst, Set.mem_ofPred_eq] at hp
    exact ⟨((⟨p.1.1, hp.1⟩, ⟨p.1.2, hp.2.1⟩), p.2), Set.mem_univ _, rfl⟩
  have hdiff : ∀ (s : S₁) (t : S₂), a₁ s - a₂ t = fun k => (S (F₁ s.1) - S (F₂ t.1)) k / M' := by
    intro s t; funext k; simp only [a₁, a₂, Pi.sub_apply, map_sub]; field_simp; ring
  have hcard₁ : (Fintype.card S₁ : ℝ) ≤ N ^ (d + η) := by
    have h1 : Fintype.card S₁ = s₁.card := by
      simp only [S₁, hs₁def]; rw [Fintype.card_subtype]
    have h2 : s₁ ⊆ Finset.univ.filter (fun i => ∀ k, |F₁ i k - base k| ≤ M) := by
      intro i hi
      simp only [hs₁def, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      intro k
      obtain ⟨h1, h2⟩ := binN_sub_bounds hM (F₁ i) k
      rw [hi] at h1 h2
      rw [abs_le]; constructor <;> linarith
    rw [h1]
    calc (s₁.card : ℝ) ≤ _ := by exact_mod_cast Finset.card_le_card h2
      _ ≤ A * (M / δ) ^ d := hc₁ _
      _ ≤ N ^ (d + η) := hAc
  have hcard₂ : (Fintype.card S₂ : ℝ) ≤ N ^ (d + η) := by
    have h1 : Fintype.card S₂ = s₂.card := by
      simp only [S₂, hs₂def]; rw [Fintype.card_subtype]
    have h2 : s₂ ⊆ Finset.univ.filter
        (fun j => ∀ k, |F₂ j k - (fun k => M * ((β + δb) k : ℝ)) k| ≤ M) := by
      intro j hj
      simp only [hs₂def, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro k
      obtain ⟨h1, h2⟩ := binN_sub_bounds hM (F₂ j) k
      rw [hj] at h1 h2
      rw [abs_le]; constructor <;> linarith
    rw [h1]
    calc (s₂.card : ℝ) ≤ _ := by exact_mod_cast Finset.card_le_card h2
      _ ≤ A * (M / δ) ^ d := hc₂ _
      _ ≤ N ^ (d + η) := hAc
  -- coefficient bounds
  have hcoef₁ : ∀ s k, |a₁ s k| ≤ L := by
    intro s k
    have hb : ∀ k', |(F₁ s.1 - base) k'| ≤ M := by
      intro k'
      obtain ⟨h1, h2⟩ := binN_sub_bounds hM (F₁ s.1) k'
      rw [s.2] at h1 h2
      simp only [Pi.sub_apply, base]; rw [abs_le]; constructor <;> linarith
    have := hop _ M hb k
    simp only [a₁]
    rw [abs_div, abs_of_pos hM', div_le_iff₀ hM']
    calc |S (F₁ s.1 - base) k| ≤ Lop * M := this
      _ = Lop * Crec * M' := by simp only [hM'def]; field_simp
      _ ≤ L * M' := by
          gcongr
          nlinarith
  have hcoef₂ : ∀ s k, |a₂ s k| ≤ L := by
    intro s k
    have hb : ∀ k', |(F₂ s.1 - base) k'| ≤ 3 * M := by
      intro k'
      obtain ⟨h1, h2⟩ := binN_sub_bounds hM (F₂ s.1) k'
      rw [s.2] at h1 h2
      have hk := hδb k'
      rw [abs_le] at hk
      have hk1 : (-2:ℝ) ≤ δb k' := by exact_mod_cast hk.1
      have hk2 : (δb k' : ℝ) ≤ 2 := by exact_mod_cast hk.2
      simp only [Pi.sub_apply, base, Pi.add_apply, Int.cast_add] at h1 h2 ⊢
      rw [abs_le]; constructor <;> nlinarith
    have := hop _ (3 * M) hb k
    simp only [a₂]
    rw [abs_div, abs_of_pos hM', div_le_iff₀ hM']
    calc |S (F₂ s.1 - base) k| ≤ Lop * (3 * M) := this
      _ = 3 * Lop * Crec * M' := by simp only [hM'def]; field_simp
      _ ≤ L * M' := by gcongr
  -- palette weights
  have hsum₁ : ∑ s : S₁, π₁ s = 1 := by
    simp only [π₁, ← Finset.sum_div]
    rw [← Finset.sum_subtype s₁ (fun i => by simp [hs₁def]) T₁]
    exact div_self (ne_of_gt hW₁pos)
  have hsum₂ : ∑ s : S₂, π₂ s = 1 := by
    simp only [π₂, ← Finset.sum_div]
    rw [← Finset.sum_subtype s₂ (fun j => by simp [hs₂def]) T₂]
    exact div_self (ne_of_gt hW₂pos)
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμapp, Set.inter_eq_right.mpr hrange]
    exact ENNReal.inv_mul_cancel hm0 hmtop
  have hmθ : ∀ W : ℝ, 0 < W → W ≤ W₁ + W₂ → m⁻¹ ≤ ENNReal.ofReal (θ * W)⁻¹ := by
    intro W hW hWle
    rw [ENNReal.ofReal_inv_of_pos (mul_pos hθpos hW), ENNReal.inv_le_inv]
    refine le_trans ?_ (le_of_lt hcon)
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hconv : ∀ T W : ℝ, 0 ≤ T → 0 < W →
      ENNReal.ofReal (θ * W)⁻¹ * ENNReal.ofReal (A * T) = ENNReal.ofReal (N ^ η * (T / W)) := by
    intro T W hT hW
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt (mul_pos hθpos hW)))]
    congr 1
    simp only [hθdef]
    rw [Real.rpow_neg (le_of_lt hNpos)]
    have hA0 : A ≠ 0 := by linarith
    have hNη : N ^ η ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hNpos η)
    field_simp
  have hmarg₁ : ∀ s (E : Set ℝ), MeasurableSet E →
      μ {q | q.1.1 = s ∧ q.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ s) * volume E := by
    intro s E hE
    rw [hμapp]
    have hsub : ψ '' {q : (S₁ × S₂) × ℝ | q.1.1 = s ∧ q.2 ∈ E} ∩ G ⊆
        {p | p.1.1 = s.1 ∧ p.2 ∈ E} := by
      rintro _ ⟨⟨q, ⟨hq1, hq2⟩, rfl⟩, _⟩
      exact ⟨by simp [ψ, hq1], hq2⟩
    calc m⁻¹ * Q (ψ '' {q | q.1.1 = s ∧ q.2 ∈ E} ∩ G)
        ≤ m⁻¹ * (ENNReal.ofReal (A * T₁ s.1) * volume E) := by
          gcongr; exact le_trans (measure_mono hsub) (hm₁ s.1 E hE)
      _ ≤ ENNReal.ofReal (θ * W₁)⁻¹ * (ENNReal.ofReal (A * T₁ s.1) * volume E) := by
          gcongr; exact hmθ W₁ hW₁pos (by linarith)
      _ = ENNReal.ofReal (N ^ η * π₁ s) * volume E := by
          rw [← mul_assoc, hconv _ _ (hT₁ _) hW₁pos]
  have hmarg₂ : ∀ s (E : Set ℝ), MeasurableSet E →
      μ {q | q.1.2 = s ∧ q.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ s) * volume E := by
    intro s E hE
    rw [hμapp]
    have hsub : ψ '' {q : (S₁ × S₂) × ℝ | q.1.2 = s ∧ q.2 ∈ E} ∩ G ⊆
        {p | p.1.2 = s.1 ∧ p.2 ∈ E} := by
      rintro _ ⟨⟨q, ⟨hq1, hq2⟩, rfl⟩, _⟩
      exact ⟨by simp [ψ, hq1], hq2⟩
    calc m⁻¹ * Q (ψ '' {q | q.1.2 = s ∧ q.2 ∈ E} ∩ G)
        ≤ m⁻¹ * (ENNReal.ofReal (A * T₂ s.1) * volume E) := by
          gcongr; exact le_trans (measure_mono hsub) (hm₂ s.1 E hE)
      _ ≤ ENNReal.ofReal (θ * W₂)⁻¹ * (ENNReal.ofReal (A * T₂ s.1) * volume E) := by
          gcongr; exact hmθ W₂ hW₂pos (by linarith)
      _ = ENNReal.ofReal (N ^ η * π₂ s) * volume E := by
          rw [← mul_assoc, hconv _ _ (hT₂ _) hW₂pos]
  have hprop : ∀ᵐ q ∂μ, q.2 ∈ Set.Icc (0:ℝ) 1 ∧
      |quad (a₁ q.1.1) q.2 - quad (a₂ q.1.2) q.2| ≤ 2 / N ∧
      1 ≤ cnorm (a₁ q.1.1 - a₂ q.1.2) := by
    rw [ae_iff, hμapp]
    have hnull := ae_iff.mp hae
    have hsub : ψ '' {q : (S₁ × S₂) × ℝ | ¬ (q.2 ∈ Set.Icc (0:ℝ) 1 ∧
        |quad (a₁ q.1.1) q.2 - quad (a₂ q.1.2) q.2| ≤ 2 / N ∧
        1 ≤ cnorm (a₁ q.1.1 - a₂ q.1.2))} ∩ G ⊆
        {p | ¬ (p.2 ∈ Set.Icc (0:ℝ) 1 ∧
          |quad (S (F₁ p.1.1)) p.2 - quad (S (F₂ p.1.2)) p.2| ≤ 2 * δ)} := by
      rintro _ ⟨⟨q, hq, rfl⟩, hG⟩
      simp only [Set.mem_ofPred_eq] at hq ⊢
      intro hgood
      apply hq
      have hfar : M / Crec ≤ cnorm (S (F₁ q.1.1.1) - S (F₂ q.1.2.1)) := by
        simp only [hGfst, Set.mem_ofPred_eq, ψ] at hG; exact hG.2.2
      refine ⟨hgood.1, ?_, ?_⟩
      · rw [quad_sub, hdiff, quad_div, abs_div, abs_of_pos hM', ← quad_sub]
        rw [div_le_div_iff₀ hM' hNpos]
        have := hgood.2
        calc |quad (S (F₁ q.1.1.1)) q.2 - quad (S (F₂ q.1.2.1)) q.2| * N ≤ 2 * δ * N := by gcongr
          _ = 2 * M' := by rw [hNM']; field_simp
      · rw [hdiff, cnorm_div hM', le_div_iff₀ hM', one_mul]
        exact hfar
    rw [measure_mono_null hsub hnull, mul_zero]
  exact hQ N hN S₁ S₂ a₁ a₂ π₁ π₂ μ hcard₁ hcard₂ hcoef₁ hcoef₂
    (fun s => div_nonneg (hT₁ _) (le_of_lt hW₁pos)) (fun s => div_nonneg (hT₂ _) (le_of_lt hW₂pos))
    hsum₁ hsum₂ hprob hmarg₁ hmarg₂ hprop

end Group

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGroupN
