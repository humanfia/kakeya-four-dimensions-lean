-- Adapted from this LOT tree, o265 (k4_staged_weak_breadth_discovery), branch x1031,
-- commit 2bb8b824, file Submission/Obl/k4_staged_weak_breadth_discovery/Broad/ChildCount.lean;
-- namespace renamed to this obligation. Attributions in the file are kept.
import Submission.Obl.k4_physical_parent_potential_candidates.Interface

/-!
# Counting finer packets inside a packet

The frozen path gives every packet two-sided original masses: the incidences of a packet at
depth `r` have product mass at least `N^(-f r) |det Q| / (2^T κ)`, and its trajectories have
prior mass at most `κ N^(-f r) |det Q|`.  Finer packets of one world and level have pairwise
null-intersecting incidence sets (disjoint trajectories within a block, distinct blocks meet in
one time).  Hence the number of finer packets whose incidences lie in a given packet is at
most the ratio of these masses.  This is the joint support count of the paper (display
`a05:local-support`), here an exact consequence of the frozen path with no exceptional set.
-/

namespace Submission.Obl.k4_physical_parent_potential_candidates.Broad

open MeasureTheory Set

/-- **Counting by floors.**  Finitely many a.e.-disjoint sets inside `Fp`, each of measure at
least `m₀`, number at most `μ Fp / m₀`. -/
theorem card_mul_floor_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {ι : Type*}
    (S : Finset ι) (F : ι → Set Ω) (Fp : Set Ω) (m₀ : ENNReal)
    (hsub : ∀ k ∈ S, F k ⊆ Fp)
    (hdisj : (S : Set ι).Pairwise (Function.onFun (AEDisjoint μ) F))
    (hmeas : ∀ k ∈ S, NullMeasurableSet (F k) μ)
    (hfloor : ∀ k ∈ S, m₀ ≤ μ (F k)) :
    (S.card : ENNReal) * m₀ ≤ μ Fp := by
  calc (S.card : ENNReal) * m₀ = ∑ _k ∈ S, m₀ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ S, μ (F k) := Finset.sum_le_sum hfloor
    _ = μ (⋃ k ∈ S, F k) := (measure_biUnion_finset₀ hdisj hmeas).symm
    _ ≤ μ Fp := measure_mono (Set.iUnion₂_subset hsub)

/-- Two closed dyadic blocks of the same length with different indices meet in at most one
time. -/
lemma block_inter_subset {T : ℕ} {j j' : ℕ} (hjj : j ≠ j') :
    ∃ t₀ : ℝ, Icc ((j : ℝ) / (2:ℝ) ^ T) (((j : ℝ) + 1) / (2:ℝ) ^ T) ∩
      Icc ((j' : ℝ) / (2:ℝ) ^ T) (((j' : ℝ) + 1) / (2:ℝ) ^ T) ⊆ {t₀} := by
  have h2 : (0:ℝ) < (2:ℝ) ^ T := by positivity
  rcases lt_or_gt_of_ne hjj with h | h
  · refine ⟨(j' : ℝ) / (2:ℝ) ^ T, fun t ht => ?_⟩
    obtain ⟨⟨_, ht1⟩, ⟨ht2, _⟩⟩ := ht
    have hj1 : ((j : ℝ) + 1) ≤ j' := by exact_mod_cast h
    have : ((j : ℝ) + 1) / (2:ℝ) ^ T ≤ (j' : ℝ) / (2:ℝ) ^ T :=
      div_le_div_of_nonneg_right hj1 h2.le
    exact le_antisymm (ht1.trans this) ht2
  · refine ⟨(j : ℝ) / (2:ℝ) ^ T, fun t ht => ?_⟩
    obtain ⟨⟨ht1, _⟩, ⟨_, ht2⟩⟩ := ht
    have hj1 : ((j' : ℝ) + 1) ≤ j := by exact_mod_cast h
    have : ((j' : ℝ) + 1) / (2:ℝ) ^ T ≤ (j : ℝ) / (2:ℝ) ^ T :=
      div_le_div_of_nonneg_right hj1 h2.le
    exact le_antisymm (ht2.trans this) ht1

/-- Incidence sets inside different blocks of one length are null-intersecting for any
product law `ν ⊗ dt`. -/
lemma aedisjoint_of_blocks {ν : Measure Ln} {T : ℕ} {j j' : ℕ} (hjj : j ≠ j')
    {F F' : Set Ev}
    (hF : ∀ p ∈ F, p.2 ∈ Icc ((j : ℝ) / (2:ℝ) ^ T) (((j : ℝ) + 1) / (2:ℝ) ^ T))
    (hF' : ∀ p ∈ F', p.2 ∈ Icc ((j' : ℝ) / (2:ℝ) ^ T) (((j' : ℝ) + 1) / (2:ℝ) ^ T)) :
    AEDisjoint (ν.prod volume) F F' := by
  obtain ⟨t₀, ht₀⟩ := block_inter_subset (T := T) hjj
  refine measure_mono_null (t := (univ : Set Ln) ×ˢ {t₀}) (fun p hp => ?_) ?_
  · exact ⟨mem_univ _, ht₀ ⟨hF p hp.1, hF' p hp.2⟩⟩
  · rw [Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- Incidence sets of trajectory-disjoint packets are disjoint. -/
lemma aedisjoint_of_lines {μ : Measure Ev} {A A' : Set Ln} {F F' : Set Ev}
    (hA : Disjoint A A') (hF : ∀ p ∈ F, p.1 ∈ A) (hF' : ∀ p ∈ F', p.1 ∈ A') :
    AEDisjoint μ F F' := by
  refine Disjoint.aedisjoint (Set.disjoint_left.mpr (fun p hp hp' => ?_))
  exact Set.disjoint_left.mp hA (hF p hp) (hF' p hp')

/-- A packet's incidence set has product mass at most its prior mass times its block length. -/
lemma prod_le_prior_mul_block {ν : Measure Ln} {A : Set Ln} {F : Set Ev}
    {T : ℕ} {j : ℝ}
    (hF : ∀ p ∈ F, p.1 ∈ A ∧ p.2 ∈ Icc (j / (2:ℝ) ^ T) ((j + 1) / (2:ℝ) ^ T)) :
    (ν.prod volume) F ≤ ν A * ENNReal.ofReal (((2:ℝ) ^ T)⁻¹) := by
  calc (ν.prod volume) F ≤ (ν.prod volume) (A ×ˢ Icc (j / (2:ℝ) ^ T) ((j + 1) / (2:ℝ) ^ T)) :=
        measure_mono (fun p hp => ⟨(hF p hp).1, (hF p hp).2⟩)
    _ = ν A * ENNReal.ofReal (((2:ℝ) ^ T)⁻¹) := by
        rw [Measure.prod_prod, Real.volume_Icc]
        congr 2
        field_simp
        ring

open Classical in
/-- **Finer packets by the full mass.**  The packets of a finer level `i'`, in the world of `b`,
whose incidences lie in those of `b`, times the original finer mass floor, carry at most the
full product mass of `b`'s incidences. -/
theorem card_finer_packets_mul_floor_le_mass
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
    {B : Fin W → ℝ} {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ} {lev : Fin C → ℕ}
    {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ} {c u : Fin C → P2}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ} {R : Fin C → Po} {A : Fin C → Set Ln}
    {F : Fin C → Set Ev} {lst : ℕ → Fin W → Ob → Finset (Fin C)}
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hN : 0 < Nk) (b : Fin C) (i' : ℕ) :
    ((Finset.univ.filter (fun b' => lev b' = i' ∧ γ b' = γ b ∧ F b' ⊆ F b)).card : ENNReal) *
        ENNReal.ofReal (Nk ^ (-f (r i')) * (Nk ^ (-(nw i' + δ₀ * L)) / (4:ℝ) ^ T i') /
          ((2:ℝ) ^ T i' * κ)) ≤ ((ν (γ b)).prod volume) (F b) := by
  classical
  set S := Finset.univ.filter (fun b' => lev b' = i' ∧ γ b' = γ b ∧ F b' ⊆ F b) with hS
  have hpack := hp.2.2.2.2.2.2.2
  have hdisjA := hp.2.2.2.2.2.2.1
  -- the floor of each finer packet
  have hfloor : ∀ b' ∈ S, ENNReal.ofReal (Nk ^ (-f (r i')) * (Nk ^ (-(nw i' + δ₀ * L)) /
      (4:ℝ) ^ T i') / ((2:ℝ) ^ T i' * κ)) ≤ ((ν (γ b)).prod volume) (F b') := by
    intro b' hb'
    obtain ⟨hlev, hγ, -⟩ := (Finset.mem_filter.mp hb').2
    obtain ⟨-, -, hch⟩ := hpack b'
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hfl, -, hdetlo, -⟩ := hch
    rw [hlev, hγ] at hfl
    rw [hlev] at hdetlo
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hfl
    have h4 : (0:ℝ) < (4:ℝ) ^ T i' := by positivity
    have hdet : Nk ^ (-(nw i' + δ₀ * L)) / (4:ℝ) ^ T i' ≤ |(Q b').det| := by
      rw [div_le_iff₀ h4]; exact hdetlo
    have hpos : 0 ≤ Nk ^ (-f (r i')) := (Real.rpow_pos_of_pos hN _).le
    have hκ : 1 ≤ κ := hp.1
    have hden : 0 < (2:ℝ) ^ T i' * κ := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdet hpos) hden.le
  refine card_mul_floor_le _ S F (F b) _ (fun b' hb' => (Finset.mem_filter.mp hb').2.2.2)
    ?_ ?_ hfloor
  · intro b₁ hb₁ b₂ hb₂ hne
    obtain ⟨hl₁, hγ₁, -⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hb₁)).2
    obtain ⟨hl₂, hγ₂, -⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hb₂)).2
    obtain ⟨-, -, hch₁⟩ := hpack b₁
    obtain ⟨-, -, hch₂⟩ := hpack b₂
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF₁, _⟩ := hch₁
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF₂, _⟩ := hch₂
    by_cases hjj : j b₁ = j b₂
    · exact aedisjoint_of_lines (hdisjA b₁ b₂ hne (hl₁.trans hl₂.symm) (hγ₁.trans hγ₂.symm) hjj)
        (fun p hp' => (hF₁ p hp').2.1) (fun p hp' => (hF₂ p hp').2.1)
    · have h₁ : ∀ p ∈ F b₁, p.2 ∈ Icc ((j b₁ : ℝ) / (2:ℝ) ^ T i') (((j b₁ : ℝ) + 1) / (2:ℝ) ^ T i') :=
        fun p hp' => by rw [← hl₁]; exact (hF₁ p hp').2.2.1
      have h₂ : ∀ p ∈ F b₂, p.2 ∈ Icc ((j b₂ : ℝ) / (2:ℝ) ^ T i') (((j b₂ : ℝ) + 1) / (2:ℝ) ^ T i') :=
        fun p hp' => by rw [← hl₂]; exact (hF₂ p hp').2.2.1
      exact aedisjoint_of_blocks hjj h₁ h₂
  · intro b' _
    obtain ⟨-, -, hch⟩ := hpack b'
    exact hch.2.2.2.2.2.2.2.1.nullMeasurableSet

open Classical in
/-- **Finer packet count.**  The packets of a finer level `i'`, in the world of `b`, whose
incidences lie in those of `b`, number at most the ratio of `b`'s original mass ceiling to the
finer original mass floor. -/
theorem card_finer_packets_le
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Ln} {E : Fin W → Set Ev}
    {B : Fin W → ℝ} {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    {r : ℕ → ℝ} {T : ℕ → ℕ} {nw : ℕ → ℝ} {κ : ℝ} {C : ℕ} {lev : Fin C → ℕ}
    {par : Fin C → Fin C} {γ : Fin C → Fin W} {j : Fin C → ℕ} {c u : Fin C → P2}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ} {R : Fin C → Po} {A : Fin C → Set Ln}
    {F : Fin C → Set Ev} {lst : ℕ → Fin W → Ob → Finset (Fin C)}
    (hp : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (hN : 0 < Nk) (b : Fin C) (i' : ℕ) :
    ((Finset.univ.filter (fun b' => lev b' = i' ∧ γ b' = γ b ∧ F b' ⊆ F b)).card : ENNReal) *
        ENNReal.ofReal (Nk ^ (-f (r i')) * (Nk ^ (-(nw i' + δ₀ * L)) / (4:ℝ) ^ T i') /
          ((2:ℝ) ^ T i' * κ)) ≤
      ENNReal.ofReal (κ * Nk ^ (-f (r (lev b))) * (Nk ^ (-(nw (lev b) - δ₀ * L)) /
          (4:ℝ) ^ T (lev b))) * ENNReal.ofReal (((2:ℝ) ^ T (lev b))⁻¹) := by
  have hκ : 1 ≤ κ := hp.1
  have hpack := hp.2.2.2.2.2.2.2
  -- the ceiling of `b`
  have hceil : ((ν (γ b)).prod volume) (F b) ≤
      ENNReal.ofReal (κ * Nk ^ (-f (r (lev b))) * (Nk ^ (-(nw (lev b) - δ₀ * L)) /
        (4:ℝ) ^ T (lev b))) * ENNReal.ofReal (((2:ℝ) ^ T (lev b))⁻¹) := by
    obtain ⟨-, -, hch⟩ := hpack b
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hF, -, hce, -, hdethi, -⟩ := hch
    refine (prod_le_prior_mul_block (fun p hp' => ⟨(hF p hp').2.1, (hF p hp').2.2.1⟩)).trans ?_
    gcongr
    refine hce.trans (ENNReal.ofReal_le_ofReal ?_)
    have h4 : (0:ℝ) < (4:ℝ) ^ T (lev b) := by positivity
    have hdet : |(Q b).det| ≤ Nk ^ (-(nw (lev b) - δ₀ * L)) / (4:ℝ) ^ T (lev b) := by
      rw [le_div_iff₀ h4]; exact hdethi
    have hpos : 0 ≤ κ * Nk ^ (-f (r (lev b))) :=
      mul_nonneg (by linarith) (Real.rpow_pos_of_pos hN _).le
    exact mul_le_mul_of_nonneg_left hdet hpos
  exact (card_finer_packets_mul_floor_le_mass hp hN b i').trans hceil

end Submission.Obl.k4_physical_parent_potential_candidates.Broad
