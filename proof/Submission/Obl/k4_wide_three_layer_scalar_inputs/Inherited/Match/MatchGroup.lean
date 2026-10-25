/- Inlined from LOT tree g-oai-074, obligation o250, session x0879,
commit c77c1a90bc277c8885ed3af05e20668071ee3318, file Submission/Obl/k4_horizontal_wide_interval_return/Match/MatchGroup.lean.
Namespace and imports renamed for o274; earlier provenance retained below. -/
/- Adapted within this LOT tree (g-oai-074) from o227 `k4_horizontal_three_projection_wide_return`,
session x0788, branch x0788, commit d1137a70, file
Submission/Obl/k4_horizontal_three_projection_wide_return/MatchGroup.lean (namespace renamed into o250's). -/
import Mathlib
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Match.MatchQuad
import Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.Match.MatchCor

/-!
# One jet group of the matching lemma

Coefficient vectors are binned at scale `M`. For one pair of bins (`β` for the first
colour, `β + δb` for the second) the pairs whose coefficient vectors differ by at
least `M` carry at most `A (M/δ)^(-η)` times the reference weight of the two bins.
This is where the frozen `Match` premise is used.
-/

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGroup

open MeasureTheory MatchQuad MatchCor

/-- The conclusion of `match_quad` for fixed constants. -/
def MatchQ (d η N₀ : ℝ) : Prop :=
  ∀ N : ℝ, N₀ ≤ N →
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (a₁ : ι₁ → Fin 3 → ℝ) (a₂ : ι₂ → Fin 3 → ℝ) (π₁ : ι₁ → ℝ) (π₂ : ι₂ → ℝ)
      (μ : Measure ((ι₁ × ι₂) × ℝ)),
      (Fintype.card ι₁ : ℝ) ≤ N ^ (d + η) → (Fintype.card ι₂ : ℝ) ≤ N ^ (d + η) →
      (∀ i k, |a₁ i k| ≤ 3) → (∀ j k, |a₂ j k| ≤ 3) →
      (∀ i, 0 ≤ π₁ i) → (∀ j, 0 ≤ π₂ j) → (∑ i, π₁ i) = 1 → (∑ j, π₂ j) = 1 →
      IsProbabilityMeasure μ →
      (∀ i (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * volume E) →
      (∀ j (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ j) * volume E) →
      ¬ (∀ᵐ p ∂μ, p.2 ∈ Set.Icc (0:ℝ) 1 ∧
          |quad (a₁ p.1.1) p.2 - quad (a₂ p.1.2) p.2| ≤ 2 / N ∧
          1 ≤ cnorm (a₁ p.1.1 - a₂ p.1.2))

theorem matchQ_of_hyp (hM : MatchHyp) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ MatchQ d η N₀ := by
  obtain ⟨η, hη, N₀, hN₀, H⟩ := match_quad hM hd0 hd1
  exact ⟨η, hη, N₀, hN₀, fun N hN ι₁ ι₂ _ _ _ _ _ _ => H N hN ι₁ ι₂⟩

/-- The bin of a coefficient vector at scale `M`. -/
noncomputable def binOf (M : ℝ) (c : Fin 3 → ℝ) : Fin 3 → ℤ := fun k => ⌊c k / M⌋

lemma bin_sub_bounds {M : ℝ} (hM : 0 < M) (c : Fin 3 → ℝ) (k : Fin 3) :
    0 ≤ (c k - M * binOf M c k) / M ∧ (c k - M * binOf M c k) / M < 1 := by
  have h1 := Int.floor_le (c k / M)
  have h2 := Int.lt_floor_add_one (c k / M)
  have e : (c k - M * binOf M c k) / M = c k / M - ⌊c k / M⌋ := by
    unfold binOf; field_simp
  rw [e]; constructor <;> linarith

lemma abs_bin_sub_le {M : ℝ} (hM : 0 < M) (c : Fin 3 → ℝ) (k : Fin 3) :
    |c k - M * binOf M c k| ≤ M := by
  obtain ⟨h1, h2⟩ := bin_sub_bounds hM c k
  have h1' : 0 ≤ c k - M * binOf M c k := by
    have := mul_nonneg h1 (le_of_lt hM); rwa [div_mul_cancel₀ _ (ne_of_gt hM)] at this
  have h2' : c k - M * binOf M c k < M := by
    have := (div_lt_one hM).mp h2; exact this
  rw [abs_of_nonneg h1']; exact le_of_lt h2'

lemma quad_div (v : Fin 3 → ℝ) (M x : ℝ) :
    quad (fun k => v k / M) x = quad v x / M := by
  simp [quad]; ring

lemma cnorm_div {M : ℝ} (hM : 0 < M) (v : Fin 3 → ℝ) :
    cnorm (fun k => v k / M) = cnorm v / M := by
  unfold cnorm
  simp only [abs_div, abs_of_pos hM]
  rw [max_div_div_right (le_of_lt hM), max_div_div_right (le_of_lt hM)]

lemma quad_sub_fun (c c' : Fin 3 → ℝ) (x : ℝ) :
    quad (fun k => c k - c' k) x = quad c x - quad c' x := by
  simp [quad]; ring

/-- The group of pairs whose bins are `β` and `β + δb`. -/
def groupSet {ι₁ ι₂ : Type} (M : ℝ) (c₁ : ι₁ → Fin 3 → ℝ) (c₂ : ι₂ → Fin 3 → ℝ)
    (β δb : Fin 3 → ℤ) : Set ((ι₁ × ι₂) × ℝ) :=
  {p | binOf M (c₁ p.1.1) = β ∧ binOf M (c₂ p.1.2) = β + δb}

/-- Pairs whose coefficient vectors differ by at least `M`. -/
def farSet {ι₁ ι₂ : Type} (M : ℝ) (c₁ : ι₁ → Fin 3 → ℝ) (c₂ : ι₂ → Fin 3 → ℝ) :
    Set ((ι₁ × ι₂) × ℝ) :=
  {p | M ≤ cnorm (c₁ p.1.1 - c₂ p.1.2)}


section Group

variable {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
  [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]

lemma measurableSet_index (S : Set (ι₁ × ι₂)) : MeasurableSet S := by
  exact (Set.toFinite S).measurableSet

lemma measurableSet_fst_preimage (S : Set (ι₁ × ι₂)) :
    MeasurableSet {p : (ι₁ × ι₂) × ℝ | p.1 ∈ S} :=
  measurable_fst (measurableSet_index S)

/-- Mass of the pairs whose first index lies in a finite set, bounded by marginals. -/
lemma mass_fst_le (Q : Measure ((ι₁ × ι₂) × ℝ)) {A : ℝ} (T₁ : ι₁ → ℝ)
    (hm₁ : ∀ i (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₁ i) * volume E)
    (s : Finset ι₁) (hzero : ∀ i ∈ s, A * T₁ i ≤ 0) :
    Q {p | p.1.1 ∈ s} = 0 := by
  apply le_antisymm _ zero_le
  have : {p : (ι₁ × ι₂) × ℝ | p.1.1 ∈ s} ⊆ ⋃ i ∈ s, {p | p.1.1 = i ∧ p.2 ∈ Set.univ} := by
    intro p hp; simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    exact ⟨p.1.1, hp, rfl⟩
  refine le_trans (measure_mono this) (le_trans (measure_biUnion_finset_le _ _) ?_)
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro i hi
  apply le_antisymm _ zero_le
  refine le_trans (hm₁ i Set.univ MeasurableSet.univ) ?_
  rw [ENNReal.ofReal_of_nonpos (hzero i hi), zero_mul]

/-- The same for the second index. -/
lemma mass_snd_le (Q : Measure ((ι₁ × ι₂) × ℝ)) {A : ℝ} (T₂ : ι₂ → ℝ)
    (hm₂ : ∀ j (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₂ j) * volume E)
    (s : Finset ι₂) (hzero : ∀ j ∈ s, A * T₂ j ≤ 0) :
    Q {p | p.1.2 ∈ s} = 0 := by
  apply le_antisymm _ zero_le
  have : {p : (ι₁ × ι₂) × ℝ | p.1.2 ∈ s} ⊆ ⋃ j ∈ s, {p | p.1.2 = j ∧ p.2 ∈ Set.univ} := by
    intro p hp; simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    exact ⟨p.1.2, hp, rfl⟩
  refine le_trans (measure_mono this) (le_trans (measure_biUnion_finset_le _ _) ?_)
  apply le_of_eq
  apply Finset.sum_eq_zero
  intro j hj
  apply le_antisymm _ zero_le
  refine le_trans (hm₂ j Set.univ MeasurableSet.univ) ?_
  rw [ENNReal.ofReal_of_nonpos (hzero j hj), zero_mul]

theorem group_le {d η N₀ : ℝ} (hQ : MatchQ d η N₀) (hη : 0 < η)
    (c₁ : ι₁ → Fin 3 → ℝ) (c₂ : ι₂ → Fin 3 → ℝ) (T₁ : ι₁ → ℝ) (T₂ : ι₂ → ℝ)
    (Q : Measure ((ι₁ × ι₂) × ℝ)) [IsFiniteMeasure Q]
    {δ M A : ℝ} (hδ : 0 < δ) (hM : 0 < M) (hN : N₀ ≤ M / δ) (hA1 : 1 ≤ A)
    (hA : A ≤ (M / δ) ^ η)
    (hT₁ : ∀ i, 0 ≤ T₁ i) (hT₂ : ∀ j, 0 ≤ T₂ j)
    (hm₁ : ∀ i (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₁ i) * volume E)
    (hm₂ : ∀ j (E : Set ℝ), MeasurableSet E →
      Q {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (A * T₂ j) * volume E)
    (hc₁ : ∀ r : Fin 3 → ℝ,
      ((Finset.univ.filter (fun i => ∀ k, |c₁ i k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d)
    (hc₂ : ∀ r : Fin 3 → ℝ,
      ((Finset.univ.filter (fun j => ∀ k, |c₂ j k - r k| ≤ M)).card : ℝ) ≤ A * (M / δ) ^ d)
    (hae : ∀ᵐ p ∂Q, p.2 ∈ Set.Icc (0:ℝ) 1 ∧
      |quad (c₁ p.1.1) p.2 - quad (c₂ p.1.2) p.2| ≤ 2 * δ)
    (β δb : Fin 3 → ℤ) (hδb : ∀ k, |δb k| ≤ 2) :
    Q (groupSet M c₁ c₂ β δb ∩ farSet M c₁ c₂) ≤
      ENNReal.ofReal (A * (M / δ) ^ (-η) *
        ((∑ i ∈ Finset.univ.filter (fun i => binOf M (c₁ i) = β), T₁ i) +
         (∑ j ∈ Finset.univ.filter (fun j => binOf M (c₂ j) = β + δb), T₂ j))) := by
  classical
  set N := M / δ with hNdef
  have hNpos : 0 < N := div_pos hM hδ
  set s₁ := Finset.univ.filter (fun i => binOf M (c₁ i) = β) with hs₁def
  set s₂ := Finset.univ.filter (fun j => binOf M (c₂ j) = β + δb) with hs₂def
  set W₁ := ∑ i ∈ s₁, T₁ i with hW₁def
  set W₂ := ∑ j ∈ s₂, T₂ j with hW₂def
  set θ := A * N ^ (-η) with hθdef
  have hθpos : 0 < θ := mul_pos (by linarith) (Real.rpow_pos_of_pos hNpos _)
  have hW₁nn : 0 ≤ W₁ := Finset.sum_nonneg (fun i _ => hT₁ i)
  have hW₂nn : 0 ≤ W₂ := Finset.sum_nonneg (fun j _ => hT₂ j)
  set G := groupSet M c₁ c₂ β δb ∩ farSet M c₁ c₂ with hGdef
  have hGfst : G = {p : (ι₁ × ι₂) × ℝ | p.1 ∈ {x : ι₁ × ι₂ | binOf M (c₁ x.1) = β ∧
      binOf M (c₂ x.2) = β + δb ∧ M ≤ cnorm (c₁ x.1 - c₂ x.2)}} := by
    ext p; simp [hGdef, groupSet, farSet, and_assoc]
  have hGm : MeasurableSet G := by rw [hGfst]; exact measurableSet_fst_preimage _
  by_contra hcon
  push Not at hcon
  set m := Q G with hmdef
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hcon; exact absurd hcon (not_lt.mpr zero_le)
  have hmtop : m ≠ ⊤ := measure_ne_top Q G
  -- G is contained in the pairs with first index in `s₁` and second in `s₂`
  have hGsub₁ : G ⊆ {p | p.1.1 ∈ s₁} := by
    intro p hp; simp only [hGfst, Set.mem_ofPred_eq] at hp; simp [hs₁def, hp.1]
  have hGsub₂ : G ⊆ {p | p.1.2 ∈ s₂} := by
    intro p hp; simp only [hGfst, Set.mem_ofPred_eq] at hp; simp [hs₂def, hp.2.1]
  -- the reference totals are positive
  have hW₁pos : 0 < W₁ := by
    rcases lt_or_eq_of_le hW₁nn with h | h
    · exact h
    exfalso; apply hm0
    apply le_antisymm _ zero_le
    refine le_trans (measure_mono hGsub₁) (le_of_eq (mass_fst_le Q T₁ hm₁ s₁ ?_))
    intro i hi
    have : T₁ i = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hT₁ i)).mp h.symm i hi
      exact this
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
  -- the index types of the group and the normalized data
  let S₁ := {i : ι₁ // binOf M (c₁ i) = β}
  let S₂ := {j : ι₂ // binOf M (c₂ j) = β + δb}
  let a₁ : S₁ → Fin 3 → ℝ := fun s k => (c₁ s.1 k - M * β k) / M
  let a₂ : S₂ → Fin 3 → ℝ := fun s k => (c₂ s.1 k - M * β k) / M
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
  have hdiff : ∀ (s : S₁) (t : S₂), a₁ s - a₂ t = fun k => (c₁ s.1 k - c₂ t.1 k) / M := by
    intro s t; funext k; simp only [a₁, a₂, Pi.sub_apply]; field_simp; ring
  -- cardinalities
  have hcard₁ : (Fintype.card S₁ : ℝ) ≤ N ^ (d + η) := by
    have h1 : Fintype.card S₁ = s₁.card := by
      simp only [S₁, hs₁def]; rw [Fintype.card_subtype]
    have h2 : s₁ ⊆ Finset.univ.filter (fun i => ∀ k, |c₁ i k - (fun k => M * (β k : ℝ)) k| ≤ M) := by
      intro i hi
      simp only [hs₁def, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      intro k; rw [← hi]; exact abs_bin_sub_le hM _ k
    rw [h1]
    calc (s₁.card : ℝ) ≤ _ := by exact_mod_cast Finset.card_le_card h2
      _ ≤ A * N ^ d := hc₁ _
      _ ≤ N ^ η * N ^ d := by gcongr
      _ = N ^ (d + η) := by rw [← Real.rpow_add hNpos]; ring_nf
  have hcard₂ : (Fintype.card S₂ : ℝ) ≤ N ^ (d + η) := by
    have h1 : Fintype.card S₂ = s₂.card := by
      simp only [S₂, hs₂def]; rw [Fintype.card_subtype]
    have h2 : s₂ ⊆ Finset.univ.filter
        (fun j => ∀ k, |c₂ j k - (fun k => M * ((β + δb) k : ℝ)) k| ≤ M) := by
      intro j hj
      simp only [hs₂def, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro k
      have := abs_bin_sub_le hM (c₂ j) k
      rw [hj] at this; simpa using this
    rw [h1]
    calc (s₂.card : ℝ) ≤ _ := by exact_mod_cast Finset.card_le_card h2
      _ ≤ A * N ^ d := hc₂ _
      _ ≤ N ^ η * N ^ d := by gcongr
      _ = N ^ (d + η) := by rw [← Real.rpow_add hNpos]; ring_nf
  -- coefficient bounds
  have hcoef₁ : ∀ s k, |a₁ s k| ≤ 3 := by
    intro s k
    obtain ⟨h1, h2⟩ := bin_sub_bounds hM (c₁ s.1) k
    rw [s.2] at h1 h2
    simp only [a₁]
    rw [abs_le]; constructor <;> linarith
  have hcoef₂ : ∀ s k, |a₂ s k| ≤ 3 := by
    intro s k
    obtain ⟨h1, h2⟩ := bin_sub_bounds hM (c₂ s.1) k
    rw [s.2] at h1 h2
    have hk := hδb k
    rw [abs_le] at hk
    have e : (c₂ s.1 k - M * β k) / M = (c₂ s.1 k - M * ((β + δb) k : ℤ)) / M + δb k := by
      simp only [Pi.add_apply]; push_cast; field_simp; ring
    simp only [a₂]
    rw [e, abs_le]
    have hk1 : (-2:ℝ) ≤ δb k := by exact_mod_cast hk.1
    have hk2 : (δb k : ℝ) ≤ 2 := by exact_mod_cast hk.2
    constructor <;> linarith
  -- palette weights
  have hsum₁ : ∑ s : S₁, π₁ s = 1 := by
    simp only [π₁, ← Finset.sum_div]
    rw [← Finset.sum_subtype s₁ (fun i => by simp [hs₁def]) T₁]
    exact div_self (ne_of_gt hW₁pos)
  have hsum₂ : ∑ s : S₂, π₂ s = 1 := by
    simp only [π₂, ← Finset.sum_div]
    rw [← Finset.sum_subtype s₂ (fun j => by simp [hs₂def]) T₂]
    exact div_self (ne_of_gt hW₂pos)
  -- probability
  have hprob : IsProbabilityMeasure μ := by
    constructor
    rw [hμapp, Set.inter_eq_right.mpr hrange]
    exact ENNReal.inv_mul_cancel hm0 hmtop
  -- the lower bound on `m` used for both marginals
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
  -- the pairs are close and far apart
  have hprop : ∀ᵐ q ∂μ, q.2 ∈ Set.Icc (0:ℝ) 1 ∧
      |quad (a₁ q.1.1) q.2 - quad (a₂ q.1.2) q.2| ≤ 2 / N ∧
      1 ≤ cnorm (a₁ q.1.1 - a₂ q.1.2) := by
    rw [ae_iff, hμapp]
    have hnull := ae_iff.mp hae
    have hsub : ψ '' {q : (S₁ × S₂) × ℝ | ¬ (q.2 ∈ Set.Icc (0:ℝ) 1 ∧
        |quad (a₁ q.1.1) q.2 - quad (a₂ q.1.2) q.2| ≤ 2 / N ∧
        1 ≤ cnorm (a₁ q.1.1 - a₂ q.1.2))} ∩ G ⊆
        {p | ¬ (p.2 ∈ Set.Icc (0:ℝ) 1 ∧
          |quad (c₁ p.1.1) p.2 - quad (c₂ p.1.2) p.2| ≤ 2 * δ)} := by
      rintro _ ⟨⟨q, hq, rfl⟩, hG⟩
      simp only [Set.mem_ofPred_eq] at hq ⊢
      intro hgood
      apply hq
      have hfar : M ≤ cnorm (c₁ q.1.1.1 - c₂ q.1.2.1) := by
        simp only [hGfst, Set.mem_ofPred_eq, ψ] at hG; exact hG.2.2
      refine ⟨hgood.1, ?_, ?_⟩
      · rw [quad_sub, hdiff, quad_div, abs_div, abs_of_pos hM, quad_sub_fun]
        rw [div_le_div_iff₀ hM hNpos]
        have := hgood.2
        calc |quad (c₁ q.1.1.1) q.2 - quad (c₂ q.1.2.1) q.2| * N ≤ 2 * δ * N := by gcongr
          _ = 2 * M := by simp only [hNdef]; field_simp
      · rw [hdiff, cnorm_div hM, le_div_iff₀ hM, one_mul]
        exact hfar
    rw [measure_mono_null hsub hnull, mul_zero]
  exact hQ N hN S₁ S₂ a₁ a₂ π₁ π₂ μ hcard₁ hcard₂ hcoef₁ hcoef₂
    (fun s => div_nonneg (hT₁ _) (le_of_lt hW₁pos)) (fun s => div_nonneg (hT₂ _) (le_of_lt hW₂pos))
    hsum₁ hsum₂ hprob hmarg₁ hmarg₂ hprop

end Group

end Submission.Obl.k4_wide_three_layer_scalar_inputs.Inherited.MatchGroup
