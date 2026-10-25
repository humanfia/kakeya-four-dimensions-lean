-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/GroupGlue.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.Core

/-!
# Gluing per-group results into the core output

Groups are the entry groups `(old packet, sub-block, box, true sign)`. Each group supplies lists of
representative entries at the terminal observation, with success on its covered incidences up to an
error; every covered incidence of an entry passes the root tests of its representative. The bins of
the core output are the representative entries themselves, and the global list at an observation is
the union of the group lists over the groups whose observation domain contains it
(`coreOutput_of_groups`).
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory MvPolynomial Submission.Lib.K4XInterface Submission.Lib.K4QuadraticSheets

/-- Entry groups. -/
abbrev Group (C s₀ K : ℕ) := Fin C × Fin (2 ^ s₀) × (Fin 2 → Fin (2 * K + 2)) × Bool

theorem measurable_gobs' (Bv a : ℝ) : Measurable (obs Bv a) := by
  change Measurable (gobs Bv a)
  unfold gobs gx
  refine Measurable.prodMk ?_ ?_
  · refine (WithLp.measurable_toLp 2 _).comp ?_
    refine Measurable.of_eval fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  · refine Measurable.floor ?_
    simp
    fun_prop

open Classical in
theorem coreOutput_of_groups
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {r₀ h θ β : ℝ} {Mc : ℕ}
    {C : ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ} {c u : Fin C → EuclideanSpace ℝ (Fin 2)}
    {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ} {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {n : ℕ} {old : Fin n → Fin C} {R' : Fin n → MvPolynomial (Fin 4) ℝ}
    {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))} {Ti s₀ K : ℕ}
    -- covered incidences
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcov : ∀ e, cov e ⊆ {p | p ∈ E (γ (old e.1)) ∧
      p.1 ∈ memE old R' A' j c u Q R Ti s₀ K e ∧ p.2 ∈ subBlock Ti s₀ (j (old e.1)) e.2.1})
    (hcovm : ∀ e, MeasurableSet (cov e))
    (hcovdisj : ∀ e e', e ≠ e' → γ (old e.1) = γ (old e'.1) → Disjoint (cov e) (cov e'))
    -- representatives
    (repOf : Entry n s₀ K → Entry n s₀ K)
    (P : Entry n s₀ K → MvPolynomial (Fin 4) ℝ) (s m₀ : Entry n s₀ K → ℝ)
    (hP : ∀ b, (P b).totalDegree ≤ 2) (hPcoef : ∀ b e, |(P b).coeff e| ≤ Nk ^ Mc)
    (hs : ∀ b, 0 < s b ∧ s b ≤ Nk ^ Mc ∧ (s b)⁻¹ ≤ Nk ^ Mc)
    (hm₀ : ∀ e, 0 ≤ m₀ (repOf e) ∧
      m₀ (repOf e) ≤ rootThreshold Nk r₀ h θ L (B (γ (old e.1))) (s (repOf e)))
    (hcurv : ∀ b, |qc (P b)| * m₀ b ≤ s b ^ 2 / 40)
    (hclose : ∀ e, ∀ p ∈ cov e, p.1 ∈ rootTestSet (P (repOf e)) (s (repOf e)) (m₀ (repOf e))
      ((subIdx s₀ (j (old e.1)) e.2.1 : ℝ) / (2 : ℝ) ^ (Ti + s₀))
      (((subIdx s₀ (j (old e.1)) e.2.1 : ℝ) + 1) / (2 : ℝ) ^ (Ti + s₀)))
    -- observation domains of groups, and per-group lists
    (S : Group C s₀ K → Set (EuclideanSpace ℝ (Fin 3) × ℤ)) (hSm : ∀ G, MeasurableSet (S G))
    (hsupp : ∀ e, ∀ p ∈ cov e, obs (B (γ (old e.1))) (δ Nk L) p ∈ S (entryGroup old e))
    (Dcount Clist : ℕ)
    (hD : ∀ w o, ((Finset.univ.filter (fun G : Group C s₀ K => γ G.1 = w ∧ o ∈ S G)).card) ≤ Dcount)
    (Lg : Group C s₀ K → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Entry n s₀ K))
    (hLm : ∀ G b, MeasurableSet {o | b ∈ Lg G o}) (hLc : ∀ G o, (Lg G o).card ≤ Clist)
    (err : Group C s₀ K → ENNReal)
    (hsucc : ∀ G, (∑ e ∈ Finset.univ.filter (fun e => entryGroup old e = G),
        ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e)) ≤
      (∑ e ∈ Finset.univ.filter (fun e => entryGroup old e = G),
        ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume)
          (cov e ∩ {p | repOf e ∈ Lg G (obs (B (γ (old e.1))) (δ Nk L) p)})) + err G)
    -- counts and the total
    (hB : ∀ w, 0 < B w) (hNk : 0 < Nk)
    (herr : ∀ G, err G ≠ ⊤)
    (hcardE : (Fintype.card (Entry n s₀ K) : ℝ) ≤ Nk ^ Mc)
    (hlistβ : ((Clist * Dcount : ℕ) : ℝ) ≤ Nk ^ β)
    (htotal : ENNReal.ofReal (Nk ^ (-β)) + ∑ G, err G ≤
      ∑ e, ENNReal.ofReal (ω (γ (old e.1))) * ((ν (γ (old e.1))).prod volume) (cov e)) :
    CoreOutput Nk L W ω ν E B r₀ h θ β Mc γ j c u Q R old R' A' Ti s₀ K := by
  classical
  let Lab := Group C s₀ K × Entry n s₀ K
  let real : Lab → Prop := fun ℓ => ∃ e, (entryGroup old e, repOf e) = ℓ
  let m₀L : Lab → ℝ := fun ℓ => if real ℓ then m₀ ℓ.2 else 0
  let lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset Lab := fun w o =>
    Finset.univ.filter (fun ℓ : Lab => γ ℓ.1.1 = w ∧ o ∈ S ℓ.1 ∧ ℓ.2 ∈ Lg ℓ.1 o)
  have hm₀L : ∀ e, m₀L (entryGroup old e, repOf e) = m₀ (repOf e) := by
    intro e
    simp only [m₀L]
    rw [if_pos ⟨e, rfl⟩]
  -- the success sets of entries
  let μE : Entry n s₀ K → Measure ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun e =>
    ENNReal.ofReal (ω (γ (old e.1))) • (ν (γ (old e.1))).prod volume
  let U : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun e =>
    cov e ∩ {p | repOf e ∈ Lg (entryGroup old e) (obs (B (γ (old e.1))) (δ Nk L) p)}
  have hUm : ∀ e, MeasurableSet (U e) := by
    intro e
    refine (hcovm e).inter ?_
    exact (measurable_gobs' _ _) (hLm (entryGroup old e) (repOf e))
  refine ⟨Entry n s₀ K, inferInstance, inferInstance, repOf, fun ℓ => P ℓ.2, fun ℓ => s ℓ.2, m₀L,
    lst, cov, hcardE, fun ℓ => hP ℓ.2, fun ℓ => hPcoef ℓ.2, fun ℓ => hs ℓ.2, ?_, ?_, hcov, ?_, ?_,
    ?_, ?_⟩
  · -- thresholds
    intro ℓ
    by_cases hr : real ℓ
    · obtain ⟨e, he⟩ := hr
      rw [← he, hm₀L]
      have := hm₀ e
      exact this
    · simp only [m₀L, if_neg hr, le_refl, true_and]
      unfold rootThreshold
      have h1 := (hs ℓ.2).1
      have h2 := gδ_pos Nk r₀
      have h3 : 0 < Nk ^ (-(θ * h * L)) := Real.rpow_pos_of_pos hNk _
      have h4 := hB (γ ℓ.1.1)
      positivity
  · -- curvature
    intro ℓ
    by_cases hr : real ℓ
    · simp only [m₀L, if_pos hr]
      exact hcurv ℓ.2
    · simp only [m₀L, if_neg hr, mul_zero]
      positivity
  · -- closeness
    intro e p hp
    rw [hm₀L]
    exact hclose e p hp
  · -- list sizes
    intro w o
    have hsub : lst w o ⊆ (Finset.univ.filter (fun G : Group C s₀ K => γ G.1 = w ∧ o ∈ S G)).biUnion
        (fun G => (Lg G o).image (fun b => (G, b))) := by
      intro ℓ hℓ
      simp only [lst, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]
      exact ⟨ℓ.1, ⟨hℓ.1, hℓ.2.1⟩, ℓ.2, hℓ.2.2, rfl⟩
    have hc : (lst w o).card ≤ Clist * Dcount := by
      calc (lst w o).card ≤ _ := Finset.card_le_card hsub
        _ ≤ ∑ G ∈ Finset.univ.filter (fun G : Group C s₀ K => γ G.1 = w ∧ o ∈ S G),
              ((Lg G o).image (fun b => (G, b))).card := Finset.card_biUnion_le
        _ ≤ ∑ _G ∈ Finset.univ.filter (fun G : Group C s₀ K => γ G.1 = w ∧ o ∈ S G), Clist :=
            Finset.sum_le_sum fun G _ => Finset.card_image_le.trans (hLc G o)
        _ = Clist * (Finset.univ.filter (fun G : Group C s₀ K => γ G.1 = w ∧ o ∈ S G)).card := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ Clist * Dcount := Nat.mul_le_mul_left _ (hD w o)
    calc ((lst w o).card : ℝ) ≤ ((Clist * Dcount : ℕ) : ℝ) := by exact_mod_cast hc
      _ ≤ Nk ^ β := hlistβ
  · -- list measurability
    intro w ℓ
    by_cases hw : γ ℓ.1.1 = w
    · have e : {o | ℓ ∈ lst w o} = S ℓ.1 ∩ {o | ℓ.2 ∈ Lg ℓ.1 o} := by
        ext o
        simp [lst, hw]
      rw [e]
      exact (hSm ℓ.1).inter (hLm ℓ.1 ℓ.2)
    · have e : {o | ℓ ∈ lst w o} = ∅ := by
        ext o
        simp [lst, hw]
      rw [e]
      exact MeasurableSet.empty
  · -- success
    -- per label, the success set contains the disjoint union of the entry success sets
    have hlab : ∀ ℓ : Lab, (∑ e ∈ Finset.univ.filter (fun e => (entryGroup old e, repOf e) = ℓ),
        μE e (U e)) ≤ ENNReal.ofReal (ω (γ ℓ.1.1)) * ((ν (γ ℓ.1.1)).prod volume)
          {p | (∃ e, (entryGroup old e, repOf e) = ℓ ∧ p ∈ cov e) ∧
            ℓ ∈ lst (γ ℓ.1.1) (obs (B (γ ℓ.1.1)) (δ Nk L) p)} := by
      intro ℓ
      set Fℓ := Finset.univ.filter (fun e => (entryGroup old e, repOf e) = ℓ)
      have hworld : ∀ e ∈ Fℓ, γ (old e.1) = γ ℓ.1.1 := by
        intro e he
        simp only [Fℓ, Finset.mem_filter, Finset.mem_univ, true_and] at he
        rw [← he]
        rfl
      have hμ : ∀ e ∈ Fℓ, μE e (U e) =
          ENNReal.ofReal (ω (γ ℓ.1.1)) * ((ν (γ ℓ.1.1)).prod volume) (U e) := by
        intro e he
        simp only [μE, Measure.smul_apply, smul_eq_mul, hworld e he]
      rw [Finset.sum_congr rfl hμ, ← Finset.mul_sum]
      refine mul_le_mul_right ?_ _
      rw [← measure_biUnion_finset]
      · apply measure_mono
        intro p hp
        simp only [Set.mem_iUnion] at hp
        obtain ⟨e, he, hpU⟩ := hp
        have he' := he
        simp only [Fℓ, Finset.mem_filter, Finset.mem_univ, true_and] at he'
        refine ⟨⟨e, he', hpU.1⟩, ?_⟩
        simp only [lst, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · rw [← he']
          exact hsupp e p hpU.1
        · rw [← he']
          exact hpU.2
      · intro e he e' he' hne
        have h1 := hworld e he
        have h2 := hworld e' he'
        exact (hcovdisj e e' hne (h1.trans h2.symm)).mono Set.inter_subset_left
          Set.inter_subset_left
      · intro e _
        exact hUm e
    -- regroup
    have hsum1 : (∑ e, μE e (U e)) ≤ ∑ ℓ : Lab, ENNReal.ofReal (ω (γ ℓ.1.1)) *
        ((ν (γ ℓ.1.1)).prod volume) {p | (∃ e, (entryGroup old e, repOf e) = ℓ ∧ p ∈ cov e) ∧
          ℓ ∈ lst (γ ℓ.1.1) (obs (B (γ ℓ.1.1)) (δ Nk L) p)} := by
      rw [← Finset.sum_fiberwise Finset.univ (fun e => (entryGroup old e, repOf e))
        (fun e => μE e (U e))]
      exact Finset.sum_le_sum fun ℓ _ => hlab ℓ
    -- group successes
    have hsum2 : (∑ e, μE e (cov e)) ≤ (∑ e, μE e (U e)) + ∑ G, err G := by
      rw [← Finset.sum_fiberwise Finset.univ (fun e => entryGroup old e) (fun e => μE e (cov e)),
        ← Finset.sum_fiberwise Finset.univ (fun e => entryGroup old e) (fun e => μE e (U e)),
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun G _ => ?_
      have := hsucc G
      have hU : ∀ x ∈ Finset.univ.filter (fun e => entryGroup old e = G), μE x (U x) =
          ENNReal.ofReal (ω (γ (old x.1))) * ((ν (γ (old x.1))).prod volume)
            (cov x ∩ {p | repOf x ∈ Lg G (obs (B (γ (old x.1))) (δ Nk L) p)}) := by
        intro x hx
        have hxG := (Finset.mem_filter.mp hx).2
        simp only [μE, U, Measure.smul_apply, smul_eq_mul, hxG]
      have hC : ∀ x ∈ Finset.univ.filter (fun e => entryGroup old e = G), μE x (cov x) =
          ENNReal.ofReal (ω (γ (old x.1))) * ((ν (γ (old x.1))).prod volume) (cov x) := by
        intro x _
        simp only [μE, Measure.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl hU, Finset.sum_congr rfl hC]
      exact this
    have hcovsum : (∑ e, ENNReal.ofReal (ω (γ (old e.1))) *
        ((ν (γ (old e.1))).prod volume) (cov e)) = ∑ e, μE e (cov e) := by
      simp only [μE, Measure.smul_apply, smul_eq_mul]
    rw [hcovsum] at htotal
    have hfin : (∑ G, err G) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun G _ => herr G
    have h3 : ENNReal.ofReal (Nk ^ (-β)) + ∑ G, err G ≤ (∑ e, μE e (U e)) + ∑ G, err G :=
      htotal.trans hsum2
    exact (ENNReal.le_of_add_le_add_right hfin h3).trans hsum1

end Submission.Obl.k4_clean_cover_graph_atlas
