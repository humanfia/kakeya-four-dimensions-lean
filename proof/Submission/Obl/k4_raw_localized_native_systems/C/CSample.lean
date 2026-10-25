import Submission.Obl.k4_raw_localized_native_systems.C.CMass
import Submission.Obl.k4_raw_localized_native_systems.C.FullTimeSample

/-
Adapted from this LOT tree, o178, session x0596, `CSample.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The full-time charts of one sample

From a narrow true later chart system with coverage `κ⁻¹`, paired full-time
binning in the good worlds (`full_time_sample`) gives the full-time charts of
`CChart`, flattened over the good worlds and their bins.  They are frozen charts at
depth zero and time exponent zero with native test, frame `stripFrame gC n`, purely
normal centre and velocity, lists of length at most `2 ⋅ 9⁴` times the later lists,
disjoint assignments in each world, selected incidences inside the later selected
incidences of their world, and weighted mass at least `(κ⁻¹ - E)² / 4` minus twice
the bad-pair bound.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- A chart predicate with a weaker extra clause. -/
theorem chart_ex_mono {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ} {Ev : Set Point}
    {c u : Plane} {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set Line}
    {F : Set Point} {ex ex' : Prop} (h : chart Nk M D κ T j r Bv Ev c u Q R A F ex)
    (hex : ex → ex') : chart Nk M D κ T j r Bv Ev c u Q R A F ex' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hex h12⟩

open Classical in
/-- **The full-time charts of one sample.** -/
theorem c_sample {CB : ℕ} (hCB2 : 2 ≤ CB) (hB : B0At CB) :
    ∀ (hp : Valid p) (a : Atlas p k) {M₂ D₂ : ℕ} {κ r : ℝ}
      {ex : Fin a.C → Prop} (hc : ChartsHyp a M₂ D₂ κ r ex)
      (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
      (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
      (κL : ℕ) (hcard : ∀ γ o, (a.lst γ o).card ≤ κL)
      (hmeas : ∀ γ b, MeasurableSet {o | b ∈ a.lst γ o})
      (hfloor : ∀ b, ENNReal.ofReal (p.N k ^ (-p.f r) * |(a.Q b).det| / ((2 : ℝ) ^ a.T * κ)) ≤
        priorMass p k (a.γ b) (a.F b))
      (hκ : 0 < κ) (hC : 0 < a.C)
      {u τ κ' lam ρ Kc KB g H E gC κC : ℝ} (M D : ℕ) (hu : 0 < u) (huη : u ≤ p.η * p.L)
      (hκ' : 1 ≤ κ') (hκκ' : κ ≤ κ') (hK : p.K k ≤ κ')
      (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ)
      (hKc : κ' + ρ ≤ Kc)
      (hKcB : 2 * Kc ≤ KB) (hκLB : (κL : ℝ) ≤ KB) (hκ'B : κ' ≤ KB) (hρB : ρ ≤ KB * g)
      (hK2 : 2 ≤ KB) (hg : 0 < g) (hgH : g * H ^ 2 ≤ 1) (hHB : (CB : ℝ) * KB ^ 2 ≤ H)
      (hρ0 : 0 ≤ ρ) (hpin : 8 * ρ / (g * H) ≤ δ (p.N k) u)
      (hE : 0 ≤ E) (hEκ : E ≤ κ⁻¹)
      (hcov : ENNReal.ofReal κ⁻¹ ≤
        ∑ b, ENNReal.ofReal (p.ω k (a.γ b)) * priorMass p k (a.γ b) (a.F b))
      (hexc : ∑ γ, ENNReal.ofReal (p.ω k γ) * (selected p k γ (angFail p k γ u τ) +
        selected p k γ (typFail p k γ p.L τ) + selected p k γ (typFail p k γ 0 τ) +
          selected p k γ (shortPath a γ u τ lam)) ≤ ENNReal.ofReal E)
      (hH1 : 1 ≤ H) (hρG : 2 * ρ + g * H * κ' ≤ 2 * (g * H ^ 2))
      (hgC : 2 * ρ + 2 * (g * H ^ 2) * κ' + 2 * (g * H ^ 2) ≤ gC) (hgC0 : 0 < gC)
      (hκC : κ' + 1 ≤ κC) (hκC2 : 2 * (1 + gC) ≤ κC)
      (hPc : ∀ γ e, |(p.P k γ).coeff e| ≤ p.N k ^ M)
      (hM₁ : 2 * Kc ≤ p.N k ^ M) (hM₂ : 2 * (2 + gC + gC⁻¹) ≤ p.N k ^ M)
      (hM₃ : 2 * (a.C : ℝ) * p.N k ^ M₂ + 88 ≤ p.N k ^ M) (hM₄ : p.N k ^ M₂ ≤ p.N k ^ M)
      (hD₂ : D₂ ≤ D) (hD : 4 ≤ D),
      ∃ (C : ℕ) (γC : Fin C → Fin (p.W k)) (rep : Fin C → Fin a.C) (t₀ : Fin C → ℝ)
        (lst : Fin (p.W k) → Observation → Finset (Fin C)),
        (C : ℝ) ≤ (p.W k : ℝ) * ((CB : ℝ) * KB / (g * H ^ 2)) ^ CB ∧
        (∀ c, chart (p.N k) M D κC 0 0 0 (p.B k (γC c)) (p.E k (γC c))
          (q2intercept a Kc (rep c) • q2normal a (rep c))
          (q2speed a Kc (rep c) • q2normal a (rep c))
          (stripFrame gC (q2normal a (rep c))) (p.P k (γC c))
          (cA a (γC c) (t₀ c) lam Kc (g * H ^ 2) gC κC (rep c))
          (cF a (γC c) (t₀ c) lam Kc (g * H ^ 2) gC κC (3 * (g * H ^ 2)) (rep c))
          (∀ z ∈ cF a (γC c) (t₀ c) lam Kc (g * H ^ 2) gC κC (3 * (g * H ^ 2)) (rep c),
            c ∈ lst (γC c) (obs (p.B k (γC c)) (δ (p.N k) p.L) z))) ∧
        (∀ c c', c ≠ c' → γC c = γC c' →
          Disjoint (cA a (γC c) (t₀ c) lam Kc (g * H ^ 2) gC κC (rep c))
            (cA a (γC c') (t₀ c') lam Kc (g * H ^ 2) gC κC (rep c'))) ∧
        (∀ γ o, (lst γ o).card ≤ 2 * 9 ^ 4 * κL) ∧
        (∀ γ c, MeasurableSet {o | c ∈ lst γ o}) ∧
        ENNReal.ofReal ((κ⁻¹ - E) ^ 2 / 4 -
            (ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
              (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
                ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r)))).toReal) ≤
          ∑ c, ENNReal.ofReal (p.ω k (γC c)) * priorMass p k (γC c)
              (cF a (γC c) (t₀ c) lam Kc (g * H ^ 2) gC κC (3 * (g * H ^ 2)) (rep c)) +
            ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
              (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
                ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r))) := by
  have hsample := full_time_sample (p := p) (k := k) hCB2 hB
  intro hp a M₂ D₂ κ r ex hc hdisj hknown κL hcard hmeas hfloor hκ hC u τ κ' lam ρ Kc KB g H E gC
    κC M D hu huη hκ' hκκ' hK hρ hKc hKcB hκLB hκ'B hρB hK2 hg hgH hHB hρ0 hpin hE hEκ hcov
    hexc hH1 hρG hgC hgC0 hκC hκC2 hPc hM₁ hM₂ hM₃ hM₄ hD₂ hD
  obtain ⟨S, hS, hineq⟩ := hsample hp a hc hdisj hknown κL hcard hmeas hfloor hκ hC hu huη hκ'
    hκκ' hK hρ hKc hKcB hκLB hκ'B hρB hK2 hg hgH hHB hρ0 hpin hE hEκ hcov hexc
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  set G := g * H ^ 2 with hGdef
  have hG : 0 < G := by positivity
  set Y := ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
    (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
      ENNReal.ofReal (256 * κ' ^ 4 * stripScale a.T ^ 2 * (κ * p.N k ^ p.f r))) with hY
  have hKC : p.K k ≤ κC := by linarith
  have hKc0 : 0 ≤ Kc := by linarith
  -- per-world data, empty off the good worlds
  have hdata : ∀ γ : Fin (p.W k), ∃ (t₀ : ℝ) (m : ℕ) (rep : Fin m → Fin a.C)
      (A : Fin m → Set Line) (L : Observation → Finset (Fin m)),
      (m : ℝ) ≤ ((CB : ℝ) * KB / G) ^ CB ∧
      Function.Injective (fun i => q2bin a Kc G (rep i)) ∧
      (γ ∈ S → (∀ i, A i = {l | (l, t₀) ∈ goodPath a γ u τ κ' lam ∧
          q2bin a Kc G (tagOf a γ hC (l, t₀)) = q2bin a Kc G (rep i)}) ∧
        ENNReal.ofReal (worldMass a γ u τ κ' lam ^ 2 / 4) ≤
          (((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam))
            {q | ∃ i, q.1 ∈ A i ∧ i ∈ L (obs (p.B k γ) (δ (p.N k) p.L) q)}) := by
    intro γ
    by_cases hγ : γ ∈ S
    · obtain ⟨t₀, m, rep, A, L, -, hm, hinj, hA, -, -, -, -, -, hret⟩ := hS γ hγ
      exact ⟨t₀, m, rep, A, L, hm, hinj, fun _ => ⟨hA, hret⟩⟩
    · refine ⟨0, 0, Fin.elim0, Fin.elim0, fun _ => ∅, ?_, fun i => i.elim0, fun h => absurd h hγ⟩
      simp only [CharP.cast_eq_zero]
      positivity
  choose t₀ m rep A L hm hinj hgood using hdata
  -- flatten over worlds and bins
  let e : (Σ γ : Fin (p.W k), Fin (m γ)) ≃ Fin (Fintype.card (Σ γ : Fin (p.W k), Fin (m γ))) :=
    Fintype.equivFin _
  let C := Fintype.card (Σ γ : Fin (p.W k), Fin (m γ))
  let γC : Fin C → Fin (p.W k) := fun c => (e.symm c).1
  let repC : Fin C → Fin a.C := fun c => rep (e.symm c).1 (e.symm c).2
  let t₀C : Fin C → ℝ := fun c => t₀ (e.symm c).1
  let emb : ∀ γ, Fin (m γ) ↪ Fin C := fun γ =>
    ⟨fun i => e ⟨γ, i⟩, fun i j h => by
      have := e.injective h
      exact eq_of_heq (Sigma.mk.inj_iff.1 this).2⟩
  let lstC : Fin (p.W k) → Observation → Finset (Fin C) := fun γ o =>
    (cLst a γ Kc (3 * G) (rep γ) o).map (emb γ)
  have hmem_lst : ∀ γ o c, c ∈ lstC γ o ↔ ∃ i ∈ cLst a γ Kc (3 * G) (rep γ) o, e ⟨γ, i⟩ = c := by
    intro γ o c
    simp only [lstC, Finset.mem_map]
    rfl
  have hγC : ∀ x, γC (e x) = x.1 := fun x => by
    show (e.symm (e x)).1 = x.1
    rw [Equiv.symm_apply_apply]
  have hrepC : ∀ x, repC (e x) = rep x.1 x.2 := fun x => by
    show rep (e.symm (e x)).1 (e.symm (e x)).2 = rep x.1 x.2
    rw [Equiv.symm_apply_apply]
  have ht₀C : ∀ x, t₀C (e x) = t₀ x.1 := fun x => by
    show t₀ (e.symm (e x)).1 = t₀ x.1
    rw [Equiv.symm_apply_apply]
  refine ⟨C, γC, repC, t₀C, lstC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the number of charts
    have hcardι : (C : ℝ) = ∑ γ, (m γ : ℝ) := by
      simp only [C, Fintype.card_sigma, Fintype.card_fin]
      push_cast
      rfl
    rw [hcardι]
    calc ∑ γ, (m γ : ℝ) ≤ ∑ _γ : Fin (p.W k), ((CB : ℝ) * KB / G) ^ CB :=
          Finset.sum_le_sum fun γ _ => hm γ
      _ = (p.W k : ℝ) * ((CB : ℝ) * KB / G) ^ CB := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · -- the chart predicate
    intro c
    have hfm := (hfmt k).2.2.2.1 (γC c)
    have hc' := cChart hc hknown (γC c) (rep (e.symm c).1) (e.symm c).2 (t₀ := t₀C c)
      (lam := lam) (Kc := Kc) (G := G) (g := gC) (κC := κC) (ε := 3 * G) M D hfm.2.2.2.2.1
      (hPc (γC c)) hfm.2.2.2.2.2.2.2.2.1 hKc0 hgC0 hκC2 hM₁ hM₂ hM₃ hM₄
      (by have := hp.scale_pos k; positivity) hD₂ hD
    refine chart_ex_mono hc' ?_
    intro hex z hz
    rw [hmem_lst]
    exact ⟨(e.symm c).2, hex z hz, by simp [γC]⟩
  · -- disjointness
    intro c c' hne hγ
    obtain ⟨⟨γ, i⟩, rfl⟩ := e.surjective c
    obtain ⟨⟨γ', i'⟩, rfl⟩ := e.surjective c'
    rw [hγC, hγC] at hγ
    rw [hγC, hγC, hrepC, hrepC, ht₀C, ht₀C]
    dsimp only at hγ ⊢
    subst hγ
    have hii : i ≠ i' := fun h => hne (by rw [h])
    exact cA_disjoint hdisj γ (rep γ) (hinj γ) hii
  · intro γ o
    rw [Finset.card_map]
    exact (card_cLst_le γ hG (rep γ) (hinj γ) o).trans
      (Nat.mul_le_mul_left _ (hcard γ o))
  · intro γ c
    have : {o | c ∈ lstC γ o} = ⋃ i : Fin (m γ),
        (if e ⟨γ, i⟩ = c then {o | i ∈ cLst a γ Kc (3 * G) (rep γ) o} else ∅) := by
      ext o
      simp only [Set.mem_ofPred_eq, hmem_lst, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, by simp [hi]⟩
      · rintro ⟨i, hi⟩
        by_cases h : e ⟨γ, i⟩ = c
        · rw [if_pos h] at hi; exact ⟨i, hi, h⟩
        · rw [if_neg h] at hi; exact absurd hi (Set.notMem_empty _)
    rw [this]
    refine MeasurableSet.iUnion fun i => ?_
    split_ifs
    · exact measurableSet_cLst γ Kc (3 * G) (rep γ) (hmeas γ) i
    · exact MeasurableSet.empty
  · -- the mass
    have hω0 : ∀ γ, 0 ≤ p.ω k γ := (hfmt k).2.1
    have hω1 : ∑ γ, p.ω k γ = 1 := (hfmt k).2.2.1
    have hsumω : ∑ γ, ENNReal.ofReal (p.ω k γ) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => hω0 γ), hω1, ENNReal.ofReal_one]
    set μF : Fin (p.W k) → ENNReal := fun γ =>
      ∑ i : Fin (m γ), priorMass p k γ (cF a γ (t₀ γ) lam Kc G gC κC (3 * G) (rep γ i)) with hμF
    have hflat : ∑ c, ENNReal.ofReal (p.ω k (γC c)) *
          priorMass p k (γC c) (cF a (γC c) (t₀C c) lam Kc G gC κC (3 * G) (repC c)) =
        ∑ γ, ENNReal.ofReal (p.ω k γ) * μF γ := by
      refine (Equiv.sum_comp e (fun c => ENNReal.ofReal (p.ω k (γC c)) * priorMass p k (γC c)
        (cF a (γC c) (t₀C c) lam Kc G gC κC (3 * G) (repC c)))).symm.trans ?_
      simp only [hγC, hrepC, ht₀C]
      rw [Fintype.sum_sigma]
      simp only [hμF, Finset.mul_sum]
    have hworld : ∀ γ ∈ S, ENNReal.ofReal (worldMass a γ u τ κ' lam ^ 2 / 4) ≤ μF γ + Y := by
      intro γ hγ
      obtain ⟨hA, hret⟩ := hgood γ hγ
      have h1 := cF_world_mass hp a γ hc hdisj hC hu huη hρ hKc hg hH1 hρG hgC hgC0 hκC hκ' hKC
        (t₀ γ) (rep γ) (A γ) (L γ) hA hret
      have h2 := q2_world_fixed_total_le hp a γ hc hdisj hknown κL (hcard γ) (hmeas γ) hfloor hκ
        hC (τ := τ) hu huη hκ' hκκ' hρ hKc hg (by linarith) hpin (t₀ γ)
      refine h1.trans (add_le_add ?_ h2)
      exact measure_iUnion_fintype_le _ _
    have hreal : (κ⁻¹ - E) ^ 2 / 4 - Y.toReal ≤
        ∑ γ ∈ S, p.ω k γ * (worldMass a γ u τ κ' lam ^ 2 / 4) := hineq
    calc ENNReal.ofReal ((κ⁻¹ - E) ^ 2 / 4 - Y.toReal)
        ≤ ENNReal.ofReal (∑ γ ∈ S, p.ω k γ * (worldMass a γ u τ κ' lam ^ 2 / 4)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ∑ γ ∈ S, ENNReal.ofReal (p.ω k γ) *
            ENNReal.ofReal (worldMass a γ u τ κ' lam ^ 2 / 4) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun γ _ => mul_nonneg (hω0 γ) (by positivity))]
          refine Finset.sum_congr rfl fun γ _ => ?_
          exact ENNReal.ofReal_mul (hω0 γ)
      _ ≤ ∑ γ ∈ S, ENNReal.ofReal (p.ω k γ) * (μF γ + Y) :=
          Finset.sum_le_sum fun γ hγ => by gcongr; exact hworld γ hγ
      _ ≤ ∑ γ, ENNReal.ofReal (p.ω k γ) * (μF γ + Y) :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = ∑ γ, ENNReal.ofReal (p.ω k γ) * μF γ + Y := by
          simp only [mul_add, Finset.sum_add_distrib]
          rw [← Finset.sum_mul, hsumω, one_mul]
      _ = _ := by rw [hflat]

end

end Submission.Obl.k4_raw_localized_native_systems.C
