import Submission.Obl.k4_dyadic_crop_worlds.Assembly

/-!
# The construction of the crop worlds

`main_construction` is the frozen conclusion of `Submission.k4_dyadic_crop_worlds`, from the
single-world hypotheses unpacked into the predicates of `Definitions.lean`.

* `world_partition` (Partition.lean): finitely many cells carry the prior; real cell masses.
* `exists_common_mass_class` (Selection.lean): subsequence, retained cells, common exponent.
* `cropped_world` (NativeBounds.lean, x0298): one normalized crop of one world.
-/

open MeasureTheory Filter

namespace Submission.Obl.k4_dyadic_crop_worlds

noncomputable section

lemma weighted_term {p ρ S : ℝ} (hp : 0 < p) (hS : 0 ≤ S) :
    ENNReal.ofReal (p / ρ) * ((ENNReal.ofReal p)⁻¹ * ENNReal.ofReal S) =
      ENNReal.ofReal (S / ρ) := by
  rw [div_eq_mul_inv, ENNReal.ofReal_mul hp.le, div_eq_mul_inv, ENNReal.ofReal_mul hS]
  have h1 : ENNReal.ofReal p ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp
  have h2 : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ENNReal.ofReal p * ENNReal.ofReal ρ⁻¹ * ((ENNReal.ofReal p)⁻¹ * ENNReal.ofReal S)
      = (ENNReal.ofReal p * (ENNReal.ofReal p)⁻¹) * (ENNReal.ofReal S * ENNReal.ofReal ρ⁻¹) := by
        ring
    _ = ENNReal.ofReal S * ENNReal.ofReal ρ⁻¹ := by rw [ENNReal.mul_inv_cancel h1 h2, one_mul]

lemma eventually_six_mul_le {N X Y : ℕ → ℝ} (hNt : Tendsto N atTop atTop)
    (hN : ∀ k, 0 < N k) (hX0 : ∀ k, 0 ≤ X k) (hY0 : ∀ k, 0 ≤ Y k)
    (hX : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, X k ≤ N k ^ ε)
    (hY : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, Y k ≤ N k ^ ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, 6 * X k * Y k ≤ N k ^ ε := by
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  have h6 : ∀ᶠ k in atTop, (6 : ℝ) ≤ N k ^ (ε / 3) :=
    ((tendsto_rpow_atTop hε3).comp hNt).eventually_ge_atTop 6
  filter_upwards [h6, hX _ hε3, hY _ hε3] with k hk6 hkX hkY
  have hNk := hN k
  have hpow : N k ^ (ε / 3) * N k ^ (ε / 3) * N k ^ (ε / 3) = N k ^ ε := by
    rw [← Real.rpow_add hNk, ← Real.rpow_add hNk]; ring_nf
  calc 6 * X k * Y k ≤ N k ^ (ε / 3) * N k ^ (ε / 3) * N k ^ (ε / 3) := by
        apply mul_le_mul (mul_le_mul hk6 hkX (hX0 k) (by positivity)) hkY (hY0 k)
        positivity
    _ = N k ^ ε := hpow

theorem main_construction (N₀ K₀ : ℕ → ℝ) (ν₀ : ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ)))
    (E₀ : ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (u₀ : ℝ)
    (hN : ∀ k, 2 ≤ N₀ k) (hNt : Filter.Tendsto N₀ Filter.atTop Filter.atTop)
    (hK1 : ∀ k, 1 ≤ K₀ k) (hKsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K₀ k ≤ N₀ k ^ ε)
    (M D : ℕ) (hprob : ∀ k, MeasureTheory.IsProbabilityMeasure (ν₀ k))
    (hPF : ∀ k, PriorFormat (N₀ k ^ M) D (ν₀ k)) (hEF : ∀ k, EventFormat (N₀ k ^ M) D (E₀ k))
    (hNB : ∀ k, ∀ᵐ l ∂(ν₀ k), NativeBound (K₀ k) l)
    (hmass : ∀ k, ENNReal.ofReal ((K₀ k)⁻¹) ≤ ((ν₀ k).prod MeasureTheory.volume) (E₀ k))
    (hu0 : 0 ≤ u₀) (hu4 : u₀ ≤ 4) :
    ∃ (ψ : ℕ → ℕ) (K : ℕ → ℝ) (β : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (p : (k : ℕ) → Fin (W k) → ℝ) (q : (k : ℕ) → Fin (W k) → (Fin 4 → ℤ)) (ρ : ℕ → ℝ), StrictMono ψ ∧ (fun (N K : ℕ → ℝ) => ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε)) (N₀ ∘ ψ) K ∧ (fun (N K : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ) (B : (k : ℕ) → Fin (W k) → ℝ) => ((∃ M D : ℕ, ∀ k, (W k : ℝ) ≤ N k ^ M ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧ (P k γ).totalDegree ≤ 2 ∧ (∀ b, |(P k γ).coeff b| ≤ N k ^ M) ∧ (∃ m : ℕ, (m : ℝ) ≤ N k ^ M ∧ ∃ (c : Fin m → ℝ) (i : Fin m → ℕ) (A : Fin m → Set (Fin 6 → ℝ)), (∀ j, 0 ≤ c j ∧ c j ≤ N k ^ M ∧ (i j : ℝ) ≤ N k ^ M ∧ (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 6) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ (A j) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true) ∧ (∀ x ∈ A j, ∀ b, |x b| ≤ N k ^ M)) ∧ ν k γ = ∑ j, (ENNReal.ofReal (c j)) • MeasureTheory.Measure.map (fun x => (i j, x)) (MeasureTheory.volume.restrict (A j))) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧ (∀ i, (∃ m₀ : ℕ, (m₀ : ℝ) ≤ (N k ^ M) ∧ ∃ p₀ : Fin m₀ → MvPolynomial (Fin 7) ℝ, (∀ i₀, (p₀ i₀).totalDegree ≤ D) ∧ ∃ b₀ : (Fin m₀ → Bool) → Bool, ∀ x₀, x₀ ∈ ({x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ (E k γ)}) ↔ b₀ (fun i₀ => decide (0 ≤ MvPolynomial.eval x₀ (p₀ i₀))) = true)) ∧ (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(WithLp.toLp 2 ![![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 1, ![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5] 2])‖ + ‖(WithLp.toLp 2 ![l.2 3, l.2 4])‖ ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (P k γ)| ≤ K k ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧ |MvPolynomial.eval (![t, l.2 0 + t * l.2 3, l.2 1 + t * l.2 4, l.2 2 + t * l.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧ (∀ᵐ p ∂(((ν k γ).prod MeasureTheory.volume).restrict (E k γ)), B k γ / K k ≤ |MvPolynomial.eval (![p.2, p.1.2 0 + p.2 * p.1.2 3, p.1.2 1 + p.2 * p.1.2 4, p.1.2 2 + p.2 * p.1.2 5]) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|)) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) Set.univ))) (N₀ ∘ ψ) K W ω ν E (fun _ _ => MvPolynomial.X (3 : Fin 4)) (fun _ _ => 1) ∧ (fun (N : ℕ → ℝ) (ν₀ : ℕ → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E₀ : ℕ → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (u₀ β : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (p : (k : ℕ) → Fin (W k) → ℝ) (q : (k : ℕ) → Fin (W k) → (Fin 4 → ℤ)) (ρ : ℕ → ℝ) => ( (∀ k, Function.Injective (q k)) ∧ (∀ k γ, 0 < p k γ ∧ p k γ = ((ν₀ k) ((fun (a : ℝ) (q : Fin 4 → ℤ) => ({l | ⌊l.2 0 / a⌋ = q 0 ∧ ⌊l.2 1 / a⌋ = q 1 ∧ ⌊l.2 3 / a⌋ = q 2 ∧ ⌊l.2 4 / a⌋ = q 3})) ((fun (N : ℕ → ℝ) (k : ℕ) (u : ℝ) => ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))) N k u₀) (q k γ))).toReal ∧ ν k γ = (ENNReal.ofReal (p k γ))⁻¹ • MeasureTheory.Measure.map ((fun (a : ℝ) (q : Fin 4 → ℤ) (l : (ℕ × (Fin 6 → ℝ))) => ((l.1, ![l.2 0 / a - (q 0 : ℝ), l.2 1 / a - (q 1 : ℝ), l.2 2, l.2 3 / a - (q 2 : ℝ), l.2 4 / a - (q 3 : ℝ), l.2 5]))) ((fun (N : ℕ → ℝ) (k : ℕ) (u : ℝ) => ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))) N k u₀) (q k γ)) ((ν₀ k).restrict ((fun (a : ℝ) (q : Fin 4 → ℤ) => ({l | ⌊l.2 0 / a⌋ = q 0 ∧ ⌊l.2 1 / a⌋ = q 1 ∧ ⌊l.2 3 / a⌋ = q 2 ∧ ⌊l.2 4 / a⌋ = q 3})) ((fun (N : ℕ → ℝ) (k : ℕ) (u : ℝ) => ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))) N k u₀) (q k γ))) ∧ E k γ = ((fun (a : ℝ) (q : Fin 4 → ℤ) (p : ((ℕ × (Fin 6 → ℝ)) × ℝ)) => (((fun (a : ℝ) (q : Fin 4 → ℤ) (l : (ℕ × (Fin 6 → ℝ))) => ((l.1, ![l.2 0 / a - (q 0 : ℝ), l.2 1 / a - (q 1 : ℝ), l.2 2, l.2 3 / a - (q 2 : ℝ), l.2 4 / a - (q 3 : ℝ), l.2 5]))) a q p.1, p.2))) ((fun (N : ℕ → ℝ) (k : ℕ) (u : ℝ) => ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))) N k u₀) (q k γ)) '' (E₀ k ∩ ((fun (a : ℝ) (q : Fin 4 → ℤ) => ({l | ⌊l.2 0 / a⌋ = q 0 ∧ ⌊l.2 1 / a⌋ = q 1 ∧ ⌊l.2 3 / a⌋ = q 2 ∧ ⌊l.2 4 / a⌋ = q 3})) ((fun (N : ℕ → ℝ) (k : ℕ) (u : ℝ) => ((2 : ℝ) ^ (-(⌊u * Real.log (N k) / Real.log 2⌋ : ℤ)))) N k u₀) (q k γ) ×ˢ Set.univ))) ∧ (∀ k, 0 < ρ k ∧ (∑ γ, p k γ) = ρ k ∧ ∀ γ, ω k γ = p k γ / ρ k) ∧ (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, (ρ k)⁻¹ ≤ N k ^ ε) ∧ (∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, ∀ γ, N k ^ (-β - ε) ≤ p k γ ∧ p k γ ≤ N k ^ (-β + ε)))) (N₀ ∘ ψ) (ν₀ ∘ ψ) (E₀ ∘ ψ) u₀ β W ω ν E p q ρ := by
  classical
  have hNpos : ∀ k, 0 < N₀ k := fun k => by linarith [hN k]
  have hN1 : ∀ k, 1 ≤ N₀ k := fun k => by linarith [hN k]
  -- the finite partition of every world
  have hpart := fun k => @world_partition (N₀ k) (hN k) M D u₀ hu4 (ν₀ k) (hprob k) (hPF k)
    (E₀ k) (hEF k).2.1
  obtain ⟨ψ, Q, β, K', hψ, hQF, hQlow, hK'1, hK'sub, hK'mass, hβ⟩ :=
    exists_common_mass_class N₀ K₀ hN hNt hK1 hKsub
      (fun k => labelBox ⌈N₀ k ^ M / side (N₀ k) u₀⌉₊)
      (fun k q => (ν₀ k (cell (side (N₀ k) u₀) q)).toReal)
      (fun k q => (((ν₀ k).prod MeasureTheory.volume)
        (E₀ k ∩ (cell (side (N₀ k) u₀) q ×ˢ Set.univ))).toReal)
      (4 * M + 28) (fun k => (hpart k).1) (fun k q => ENNReal.toReal_nonneg)
      (fun k q => (hpart k).2.2.2.1 q) (fun k => (hpart k).2.1.le)
      (fun k => by
        rw [(hpart k).2.2.1]
        exact (ENNReal.ofReal_le_iff_le_toReal
          (ne_top_of_le_ne_top ENNReal.one_ne_top (hpart k).2.2.2.2)).1 (hmass k))
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  -- abbreviations for the retained cells
  have hQlow' : ∀ k, ∀ q ∈ Q k, N₀ (ψ k) ^ (-(((4 * M + 28 : ℕ) : ℝ) + 1)) ≤
      (ν₀ (ψ k) (cell (side (N₀ (ψ k)) u₀) q)).toReal := hQlow
  have hK'mass' : ∀ k, (K' k)⁻¹ ≤ ∑ q ∈ Q k, (((ν₀ (ψ k)).prod MeasureTheory.volume)
      (E₀ (ψ k) ∩ (cell (side (N₀ (ψ k)) u₀) q ×ˢ Set.univ))).toReal := hK'mass
  have hβ' : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ q ∈ Q k,
      N₀ (ψ k) ^ (-β - ε) ≤ (ν₀ (ψ k) (cell (side (N₀ (ψ k)) u₀) q)).toReal ∧
      (ν₀ (ψ k) (cell (side (N₀ (ψ k)) u₀) q)).toReal ≤ N₀ (ψ k) ^ (-β + ε) := hβ
  -- the data
  set W : ℕ → ℕ := fun k => (Q k).card with hW
  set qq : (k : ℕ) → Fin (W k) → Label := fun k γ => ((Q k).equivFin.symm γ).1 with hqq
  set pp : (k : ℕ) → Fin (W k) → ℝ :=
    fun k γ => (ν₀ (ψ k) (cell (side (N₀ (ψ k)) u₀) (qq k γ))).toReal with hpp
  set ρ : ℕ → ℝ := fun k => ∑ γ, pp k γ with hρ
  set ω : (k : ℕ) → Fin (W k) → ℝ := fun k γ => pp k γ / ρ k with hω
  set ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)) :=
    fun k γ => cropPrior (ν₀ (ψ k)) (side (N₀ (ψ k)) u₀) (qq k γ) (pp k γ) with hν
  set E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) :=
    fun k γ => cropEvent (E₀ (ψ k)) (side (N₀ (ψ k)) u₀) (qq k γ) with hE
  set K : ℕ → ℝ := fun k => 6 * K' k * K₀ (ψ k) with hK
  -- basic facts
  have hqmem : ∀ k γ, qq k γ ∈ Q k := fun k γ => ((Q k).equivFin.symm γ).2
  have hδpos : ∀ k, 0 < N₀ (ψ k) ^ (-(((4 * M + 28 : ℕ) : ℝ) + 1)) :=
    fun k => Real.rpow_pos_of_pos (hNpos _) _
  have hδle : ∀ k, N₀ (ψ k) ^ (-(((4 * M + 28 : ℕ) : ℝ) + 1)) ≤ 1 :=
    fun k => Real.rpow_le_one_of_one_le_of_nonpos (hN1 _) (neg_nonpos.2 (by positivity))
  have hppδ : ∀ k γ, N₀ (ψ k) ^ (-(((4 * M + 28 : ℕ) : ℝ) + 1)) ≤ pp k γ :=
    fun k γ => hQlow' k (qq k γ) (hqmem k γ)
  have hpppos : ∀ k γ, 0 < pp k γ := fun k γ => (hδpos k).trans_le (hppδ k γ)
  have hρQ : ∀ k, ρ k = ∑ q ∈ Q k, (ν₀ (ψ k) (cell (side (N₀ (ψ k)) u₀) q)).toReal :=
    fun k => sum_equivFin (Q k) (fun q => (ν₀ (ψ k) (cell (side (N₀ (ψ k)) u₀) q)).toReal)
  have hSQ_le : ∀ k, ∑ q ∈ Q k, (((ν₀ (ψ k)).prod MeasureTheory.volume)
      (E₀ (ψ k) ∩ (cell (side (N₀ (ψ k)) u₀) q ×ˢ Set.univ))).toReal ≤ ρ k := by
    intro k
    rw [hρQ k]
    exact Finset.sum_le_sum fun q _ => (hpart (ψ k)).2.2.2.1 q
  have hK'pos : ∀ k, 0 < K' k := fun k => by linarith [hK'1 k]
  have hρge : ∀ k, (K' k)⁻¹ ≤ ρ k := fun k => (hK'mass' k).trans (hSQ_le k)
  have hρpos : ∀ k, 0 < ρ k := fun k => (inv_pos.2 (hK'pos k)).trans_le (hρge k)
  have hρle : ∀ k, ρ k ≤ 1 := by
    intro k
    rw [hρQ k, ← (hpart (ψ k)).2.1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hQF k) fun q _ _ => ENNReal.toReal_nonneg
  have hK1' : ∀ k, 1 ≤ K k := by
    intro k
    have h1 := hK'1 k
    have h2 := hK1 (ψ k)
    show 1 ≤ 6 * K' k * K₀ (ψ k)
    nlinarith
  have hK6 : ∀ k, 6 ≤ K k := by
    intro k
    have h1 := hK'1 k
    have h2 := hK1 (ψ k)
    show 6 ≤ 6 * K' k * K₀ (ψ k)
    nlinarith
  have hKK₀ : ∀ k, K₀ (ψ k) ≤ K k := by
    intro k
    have h1 := hK'1 k
    have h2 := hK1 (ψ k)
    show K₀ (ψ k) ≤ 6 * K' k * K₀ (ψ k)
    nlinarith
  have hKK' : ∀ k, K' k ≤ K k := by
    intro k
    have h1 := hK'1 k
    have h2 := hK1 (ψ k)
    show K' k ≤ 6 * K' k * K₀ (ψ k)
    nlinarith
  -- one crop of one world
  have hcrop : ∀ k γ, _ := fun k γ =>
    @cropped_world (N₀ (ψ k) ^ M) (K₀ (ψ k)) (K k) (N₀ (ψ k) ^ (-(((4 * M + 28 : ℕ) : ℝ) + 1)))
      (side (N₀ (ψ k)) u₀) (pp k γ) D (ν₀ (ψ k)) (hprob (ψ k)) (E₀ (ψ k)) (qq k γ)
      (one_le_pow₀ (hN1 _)) (hPF (ψ k)) (hEF (ψ k)) (hNB (ψ k)) (hKK₀ k) (hK6 k)
      (side_pos _ _) (side_le_one (hN1 _) hu0) (hδpos k) (hδle k) (hppδ k γ) rfl
  refine ⟨ψ, K, β, W, ω, ν, E, pp, qq, ρ, hψ, ⟨hK1', ?_⟩, ?_, ?_⟩
  · -- the new tempered constant
    have hK₀ψ : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K₀ (ψ k) ≤ N₀ (ψ k) ^ ε :=
      fun ε hε => hψt.eventually (hKsub ε hε)
    exact eventually_six_mul_le (N := N₀ ∘ ψ) (hNt.comp hψt) (fun k => hNpos _)
      (fun k => (hK'pos k).le) (fun k => by linarith [hK1 (ψ k)]) hK'sub hK₀ψ
  · -- the weighted world format
    beta_reduce
    refine ⟨M + (4 * M + 28) + 5, max D 1, fun k => ?_⟩
    have hNk1 : (1 : ℝ) ≤ (N₀ ∘ ψ) k ^ (M + (4 * M + 28) + 5) := one_le_pow₀ (hN1 _)
    refine ⟨?_, ?_, ?_, fun γ => ?_, ?_⟩
    · calc ((W k : ℕ) : ℝ) ≤ ((labelBox ⌈N₀ (ψ k) ^ M / side (N₀ (ψ k)) u₀⌉₊).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (hQF k)
        _ ≤ N₀ (ψ k) ^ (4 * M + 28) := (hpart (ψ k)).1
        _ ≤ N₀ (ψ k) ^ (M + (4 * M + 28) + 5) := pow_le_pow_right₀ (hN1 _) (by omega)
    · intro γ
      exact div_nonneg (hpppos k γ).le (hρpos k).le
    · show ∑ γ, pp k γ / ρ k = 1
      rw [← Finset.sum_div]
      exact div_self (hρpos k).ne'
    · obtain ⟨hpr, hPFγ, hEFγ, hNBγ, -⟩ := hcrop k γ
      exact crop_gamma_facts (ν k γ) (E k γ) hpr hNk1
        (hPFγ.mono (prior_budget (hN _) M (4 * M + 28)))
        (hEFγ.mono (event_budget (hN _) M (4 * M + 28))) hNBγ (hK1' k)
    · have hterm : ∀ γ, ENNReal.ofReal (ω k γ) *
          (((ν k γ).prod MeasureTheory.volume).restrict (E k γ)) Set.univ =
          ENNReal.ofReal ((((ν₀ (ψ k)).prod MeasureTheory.volume)
            (E₀ (ψ k) ∩ (cell (side (N₀ (ψ k)) u₀) (qq k γ) ×ˢ Set.univ))).toReal / ρ k) := by
        intro γ
        rw [Measure.restrict_apply_univ, (hcrop k γ).2.2.2.2]
        have hfin : ((ν₀ (ψ k)).prod MeasureTheory.volume)
            (E₀ (ψ k) ∩ (cell (side (N₀ (ψ k)) u₀) (qq k γ) ×ˢ Set.univ)) ≠ ⊤ :=
          ((selected_le_cell (hEF (ψ k)).2.1 _ _).trans_lt (measure_lt_top _ _)).ne
        have h := weighted_term (ρ := ρ k) (hpppos k γ) (ENNReal.toReal_nonneg (a :=
          ((ν₀ (ψ k)).prod MeasureTheory.volume)
            (E₀ (ψ k) ∩ (cell (side (N₀ (ψ k)) u₀) (qq k γ) ×ˢ Set.univ))))
        rw [ENNReal.ofReal_toReal hfin] at h
        exact h
      rw [Finset.sum_congr rfl (fun γ _ => hterm γ), ← ENNReal.ofReal_sum_of_nonneg
        (fun γ _ => div_nonneg ENNReal.toReal_nonneg (hρpos k).le)]
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.sum_div]
      rw [sum_equivFin (Q k) (fun q => (((ν₀ (ψ k)).prod MeasureTheory.volume)
            (E₀ (ψ k) ∩ (cell (side (N₀ (ψ k)) u₀) q ×ˢ Set.univ))).toReal)]
      calc (K k)⁻¹ ≤ (K' k)⁻¹ := inv_anti₀ (hK'pos k) (hKK' k)
        _ ≤ _ := hK'mass' k
        _ ≤ _ := le_div_self (Finset.sum_nonneg fun q _ => ENNReal.toReal_nonneg) (hρpos k)
            (hρle k)
  · -- the crop representation
    beta_reduce
    refine ⟨fun k => injective_equivFin (Q k), fun k γ => ⟨hpppos k γ, rfl, rfl, rfl⟩,
      fun k => ⟨hρpos k, rfl, fun γ => rfl⟩, ?_, ?_⟩
    · intro ε hε
      filter_upwards [hK'sub ε hε] with k hk
      exact (inv_le_of_inv_le₀ (hK'pos k) (hρge k)).trans hk
    · intro ε hε
      filter_upwards [hβ' ε hε] with k hk γ
      exact hk (qq k γ) (hqmem k γ)

end

end Submission.Obl.k4_dyadic_crop_worlds
