import Mathlib
import ChallengeDeps
import Submission.Obl.k4_scalar_coefficient_clustering.Combine
import Submission.Obl.k4_scalar_coefficient_clustering.Powers
set_option linter.unusedVariables false

/-!
# `Submission.k4_scalar_coefficient_clustering`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_scalar_coefficient_clustering`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_scalar_coefficient_clustering/`
belong to this obligation.
-/

theorem Submission.k4_scalar_coefficient_clustering : (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D → ∀ (n : ℕ) (b u : Fin n → EuclideanSpace ℝ (Fin 2)) (ω : Fin n → ℝ) (A : ℝ) (J : Fin n → Finset (Fin D)), (∀ i : Fin n, ‖b i‖ ≤ 1 ∧ ‖u i‖ ≤ 1) → (∀ i : Fin n, 0 < ω i) → 0 < A → (∀ (c w e₁ e₂ : EuclideanSpace ℝ (Fin 2)) (a β : ℝ), ‖e₁‖ = 1 → ‖e₂‖ = 1 → inner ℝ e₁ e₂ = 0 → 1 ≤ a → a ≤ β → β ≤ (D : ℝ) → ∀ S : Finset (Fin n), (∀ i ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) 1, |inner ℝ (b i + t • u i - c - t • w) e₁| ≤ a / (D : ℝ) ∧ |inner ℝ (b i + t • u i - c - t • w) e₂| ≤ β / (D : ℝ)) → ∑ i ∈ S, ω i ≤ A * a * β) → (∀ i : Fin n, (D : ℝ) ^ (1 - η) ≤ ((J i).card : ℝ)) → ∑ i : Fin n, ω i * ((J i).card : ℝ) ≤ C * A * (D : ℝ) ^ ε * ((((Finset.univ : Finset (Fin n)).sigma J).image (fun p => ((p.2 : ℕ), fun k : Fin 2 => ⌊(D : ℝ) * (b p.1 + (((((p.2 : ℕ) : ℝ) + 1 / 2) / (D : ℝ)) • u p.1)) k⌋))).card : ℝ)) → ∀ d c ε : ℝ, 0 ≤ d → d < 1 → 0 < c → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (a : α → EuclideanSpace ℝ (Fin 3)) (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)), Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 → (∀ l : α, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) → ENNReal.ofReal (N ^ (-η)) ≤ (ν.prod MeasureTheory.volume) E → (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) → (∀ l : α, ∀ t : ℝ, (l, t) ∈ E → (⌊t / (N ^ (-c))⌋, ⌊(a l 0 + t * a l 1 + t ^ 2 * a l 2) / (N ^ (-c))⌋) ∈ F) → (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-c) ≤ r → ν {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η * r ^ d)) → ∃ q : Fin 3 → ℤ, ENNReal.ofReal (N ^ (-c * d - ε)) ≤ ν {l | (∀ j : Fin 3, ⌊a l j / (N ^ (-c))⌋ = q j) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ MeasureTheory.volume {t : ℝ | (l, t) ∈ E}} := by
  classical
  intro hinput
  change Submission.Obl.k4_scalar_coefficient_clustering.PlankInput at hinput
  intro d c ε hd0 hd1 hc hε
  let s : ℝ := ε / 8
  let γ : ℝ := s * (1 - d)
  have hs : 0 < s := by dsimp [s]; positivity
  have hγ : 0 < γ := mul_pos hs (sub_pos.mpr hd1)
  have hγs : γ ≤ s := by dsimp [γ]; nlinarith [mul_nonneg hs.le hd0]
  let τ : ℝ := γ / (4 * (c + 2))
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτeq : (c + 2) * τ = γ / 4 := by dsimp [τ]; field_simp
  obtain ⟨ζ, hζ, C, hC, hplank⟩ := hinput τ hτ
  let η : ℝ := min 1 (min (ε / 12) (min (γ / 100) (c * ζ / 12)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / 12 := (min_le_right _ _).trans (min_le_left _ _)
  have hηγ : η ≤ γ / 100 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hηζ : η ≤ c * ζ / 12 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have he₁ : 7 * η + (c + 2) * τ + s * (d - 1) < 0 := by
    have hg : s * (d - 1) = -γ := by dsimp [γ]; ring
    rw [hg, hτeq]
    linarith
  have he₂ : 6 * η + (c + 2) * τ + 3 * s - ε < 0 := by
    rw [hτeq]
    dsimp [s] at hs hγs ⊢
    linarith
  have hbud := Submission.Obl.k4_scalar_coefficient_clustering.negative_two_powers_eventually
    (C := 4000000000000 * C) he₁ he₂
  have hKevent : ∀ᶠ N : ℝ in Filter.atTop, 2 ≤ N ^ η :=
    (tendsto_rpow_atTop hη).eventually (Filter.eventually_ge_atTop 2)
  have hevent : ∀ᶠ N : ℝ in Filter.atTop, 8 ≤ N ∧ 2 ≤ N ^ η ∧
      4000000000000 * C * (N ^ (7 * η + (c + 2) * τ + s * (d - 1)) +
        N ^ (6 * η + (c + 2) * τ + 3 * s - ε)) < 1 := by
    filter_upwards [Filter.eventually_ge_atTop (8 : ℝ), hKevent, hbud] with N hN hK hb
    exact ⟨hN, hK, hb⟩
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨η, hη, max 8 N₁, by exact le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro N hN α mα ν a E F ha hE hunit hB hν hinc hsize hF hcap
  have hN' : N₁ ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hN8, hK, hbudget⟩ := hN₁ N hN'
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  let K : ℝ := N ^ η
  let p : ℝ := N ^ (-c)
  let R : ℝ := 4 * K
  let H : ℝ := N ^ (-c * d - ε)
  let Λ : ℝ := N ^ s
  have hp : 0 < p := Real.rpow_pos_of_pos hNpos _
  have hH : 0 < H := Real.rpow_pos_of_pos hNpos _
  have hΛ : 1 ≤ Λ := Real.one_le_rpow hN1 hs.le
  obtain ⟨D, hD, hlo, hhi, hhigh, hbase⟩ :=
    Submission.Obl.k4_scalar_coefficient_clustering.discrete_scale hN8 hη.le hη1 hc
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hdense : (D : ℝ) ^ (1 - ζ) ≤ (D : ℝ) / K ^ 3 :=
    Submission.Obl.k4_scalar_coefficient_clustering.discrete_density hN1 hDpos hζ hbase (by nlinarith)
  have hlong : N ^ (-ε) ≤ 1 / K ^ 3 :=
    Submission.Obl.k4_scalar_coefficient_clustering.long_label_threshold hN1 (by linarith)
  by_contra hno
  push_neg at hno
  have hbin : ∀ q : Fin 3 → ℤ,
      ν {l | Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode p (a l) = q ∧
        ENNReal.ofReal (1 / K ^ 3) ≤ MeasureTheory.volume {t : ℝ | (l, t) ∈ E}} ≤ ENNReal.ofReal H := by
    intro q
    have hsub : {l | Submission.Obl.k4_scalar_coefficient_clustering.coefficientCode p (a l) = q ∧
        ENNReal.ofReal (1 / K ^ 3) ≤ MeasureTheory.volume {t : ℝ | (l, t) ∈ E}} ⊆
        {l | (∀ j : Fin 3, ⌊a l j / p⌋ = q j) ∧
          ENNReal.ofReal (N ^ (-ε)) ≤ MeasureTheory.volume {t : ℝ | (l, t) ∈ E}} := by
      intro l hl
      exact ⟨fun j => congrFun hl.1 j, (ENNReal.ofReal_le_ofReal hlong).trans hl.2⟩
    exact (MeasureTheory.measure_mono hsub).trans (hno q).le
  have hinc' : ENNReal.ofReal (1 / K) ≤ (ν.prod MeasureTheory.volume) E := by
    simpa only [K, one_div, ← Real.rpow_neg hNpos.le] using hinc
  have hb := Submission.Obl.k4_scalar_coefficient_clustering.clustering_mass_bound
    hplank hC hd0 hd1 hp hK (show 3 * K ≤ R by dsimp [R]; linarith) hH.le hΛ hD
    hlo hhi hdense ν ha hE hunit hB hν hinc' F hF hcap hbin
  have hu := Submission.Obl.k4_scalar_coefficient_clustering.scalar_budget_upper hNpos hDpos
    C η c s τ d ε hC.le hτ.le (Nat.cast_nonneg F.card) hlo hhigh hsize
  have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * K ^ 4)
  have hcontra : 1 ≤ 4000000000000 * C *
      (N ^ (7 * η + (c + 2) * τ + s * (d - 1)) +
        N ^ (6 * η + (c + 2) * τ + 3 * s - ε)) := by
    have hh := hm.trans hu
    convert hh using 1 <;> dsimp [K] <;> field_simp
  exact (not_le_of_gt hbudget) hcontra
