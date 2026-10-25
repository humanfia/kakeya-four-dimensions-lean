-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.Reduction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
/-!
# Outer reduction for `wz_frostman_family_improvement` (o038)

`O038` is the frozen type of o038, `Core` the same estimate for a Frostman family alone:
for every `ξ > 0` there are `α, ζ > 0` such that, for every `ε > 0`, some `c, η > 0` give

    vol(⋃ Y) ≥ c δ^(ω'-α+ε) (n δ⁴)^(σ/2)

for every admissible family of `n` δ-tubes (frozen `H` with exponent `η`) whose shadings are
individually `δ^η`-dense, which is `δ^(-ζ)`-Frostman for convex sets and has no `ξ`-sticky
subfamily. `o038_of_core : Core → O038` passes to the Frostman subfamily `g` (it inherits every
hypothesis; a sticky subfamily of it is a sticky subfamily of the family), and compares the
targets: `K(m)` on `B(0,1)` gives `n δ² ≤ 5 m`, hence with `p = 1 - 3σ/2`

    m⁻¹ (nδ²) (m^(-3/2) nδ)^(-σ) = m^(-p) (nδ²)(nδ)^(-σ) ≤ 5^p (nδ⁴)^(σ/2),

and `n ≤ δ^(-η) k` costs `δ^(-ησ/2) ≤ δ^(-ε/2)` once `η ≤ ε`.
-/

set_option linter.unusedVariables false

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy

/-- The `R`-target, rewritten with the exponent `p = 1 - 3σ/2` of `m`. -/
lemma target_rewrite (σ m N δ : ℝ) (hm : 0 < m) (hN : 0 < N) (hδ : 0 < δ) :
    m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (N * δ)) ^ (-σ)
      = m ^ (-(1 - 3/2 * σ)) * ((N * δ ^ 2) * (N * δ) ^ (-σ)) := by
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hm.le,
    ← Real.rpow_neg_one m]
  have : m ^ (-(1 - 3/2 * σ)) = m ^ (-1 : ℝ) * m ^ (-(3/2 : ℝ) * -σ) := by
    rw [← Real.rpow_add hm]; ring_nf
  rw [this]; ring

/-- `(Nδ²)^(3σ/2) (Nδ)^(-σ) = (Nδ⁴)^(σ/2)`. -/
lemma shape_eq (σ N δ : ℝ) (hN : 0 < N) (hδ : 0 < δ) :
    (N * δ ^ 2) ^ (3/2 * σ) * (N * δ) ^ (-σ) = (N * δ ^ 4) ^ (σ / 2) := by
  rw [Real.mul_rpow hN.le (by positivity), Real.mul_rpow hN.le hδ.le,
    Real.mul_rpow hN.le (by positivity)]
  rw [← Real.rpow_natCast δ 2, ← Real.rpow_natCast δ 4, ← Real.rpow_mul hδ.le,
    ← Real.rpow_mul hδ.le]
  have h1 : N ^ (3/2 * σ) * N ^ (-σ) = N ^ (σ / 2) := by
    rw [← Real.rpow_add hN]; ring_nf
  have h2 : δ ^ ((2:ℕ) * (3/2 * σ) : ℝ) * δ ^ (-σ) = δ ^ ((4:ℕ) * (σ / 2) : ℝ) := by
    rw [← Real.rpow_add hδ]; push_cast; ring_nf
  calc N ^ (3/2 * σ) * δ ^ ((2:ℕ) * (3/2 * σ) : ℝ) * (N ^ (-σ) * δ ^ (-σ))
      = (N ^ (3/2 * σ) * N ^ (-σ)) * (δ ^ ((2:ℕ) * (3/2 * σ) : ℝ) * δ ^ (-σ)) := by ring
    _ = N ^ (σ / 2) * δ ^ ((4:ℕ) * (σ / 2) : ℝ) := by rw [h1, h2]

/-- The comparison of the `R`-target with the Frostman-core bound. -/
lemma target_le_core (σ w ε η c δ m N K : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1/2)
    (hε : 0 < ε) (hη : 0 < η) (hηε : η ≤ ε) (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 1 ≤ m) (hN : 0 < N) (hNK : δ ^ η * N ≤ K) (hKm : N * δ ^ 2 ≤ 5 * m) :
    c / 5 * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (N * δ)) ^ (-σ)
      ≤ c * δ ^ (w + ε / 2) * (K * δ ^ 4) ^ (σ / 2) := by
  have hm0 : 0 < m := by linarith
  have hK : 0 < K := lt_of_lt_of_le (by positivity) hNK
  set p : ℝ := 1 - 3/2 * σ with hp
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  have hp1 : p ≤ 1 := by rw [hp]; linarith
  have hA : 0 < N * δ ^ 2 := by positivity
  -- step 1: rewrite and use `m ≥ Nδ²/5`
  have e1 : c / 5 * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (N * δ)) ^ (-σ)
      = c / 5 * δ ^ (w + ε) * (m ^ (-p) * ((N * δ ^ 2) * (N * δ) ^ (-σ))) := by
    rw [← target_rewrite σ m N δ hm0 hN hδ0]; ring
  have hmp : m ^ (-p) ≤ (N * δ ^ 2 / 5) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have e2 : (N * δ ^ 2 / 5) ^ (-p) * ((N * δ ^ 2) * (N * δ) ^ (-σ))
      = 5 ^ p * (N * δ ^ 4) ^ (σ / 2) := by
    rw [Real.div_rpow hA.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 5),
      div_inv_eq_mul, ← shape_eq σ N δ hN hδ0]
    have : (N * δ ^ 2) ^ (-p) * (N * δ ^ 2) = (N * δ ^ 2) ^ (3/2 * σ) := by
      rw [← Real.rpow_add_one hA.ne']; congr 1; rw [hp]; ring
    rw [← this]; ring
  -- step 2: `N ≤ δ^(-η) K`
  have hN' : N ≤ δ ^ (-η) * K := by
    rw [Real.rpow_neg hδ0.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    linarith
  have hNK4 : (N * δ ^ 4) ^ (σ / 2) ≤ δ ^ (-η * (σ / 2)) * (K * δ ^ 4) ^ (σ / 2) := by
    calc (N * δ ^ 4) ^ (σ / 2) ≤ (δ ^ (-η) * K * δ ^ 4) ^ (σ / 2) :=
          Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)
      _ = δ ^ (-η * (σ / 2)) * (K * δ ^ 4) ^ (σ / 2) := by
          rw [mul_assoc, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hδ0.le]
  have h5p : (5:ℝ) ^ p ≤ 5 := by
    calc (5:ℝ) ^ p ≤ 5 ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
      _ = 5 := Real.rpow_one 5
  have hδexp : δ ^ (w + ε) * δ ^ (-η * (σ / 2)) ≤ δ ^ (w + ε / 2) := by
    rw [← Real.rpow_add hδ0]
    apply Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1
    nlinarith
  have hpos1 : 0 ≤ (K * δ ^ 4) ^ (σ / 2) := by positivity
  calc c / 5 * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (N * δ)) ^ (-σ)
      = c / 5 * δ ^ (w + ε) * (m ^ (-p) * ((N * δ ^ 2) * (N * δ) ^ (-σ))) := e1
    _ ≤ c / 5 * δ ^ (w + ε) * ((N * δ ^ 2 / 5) ^ (-p) * ((N * δ ^ 2) * (N * δ) ^ (-σ))) := by
        gcongr
    _ = c / 5 * δ ^ (w + ε) * (5 ^ p * (N * δ ^ 4) ^ (σ / 2)) := by rw [e2]
    _ ≤ c / 5 * δ ^ (w + ε) * (5 * (δ ^ (-η * (σ / 2)) * (K * δ ^ 4) ^ (σ / 2))) := by
        gcongr
    _ = c * (δ ^ (w + ε) * δ ^ (-η * (σ / 2))) * (K * δ ^ 4) ^ (σ / 2) := by ring
    _ ≤ c * δ ^ (w + ε / 2) * (K * δ ^ 4) ^ (σ / 2) := by gcongr


/-- The frozen statement of o038. -/
def O038 : Prop := ∀ σ ω ω' : ℝ, (fun (B : Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (μ : MeasureTheory.Measure LeanEval.Analysis.WangZahlKakeya.Space) => (fun (o : ℝ → ENNReal) => (fun (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop → Prop) => (fun (J : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop) => (fun (K : ℝ → ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop → Prop) => (fun (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) => (fun (d : ℝ → ℝ → Prop) => (fun (e : ℝ → ℝ → Prop) => (fun (S : ℝ → ℝ → (k : ℕ) → (Fin k → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin k → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) => 0 < σ → σ ≤ 1/2 → 0 < ω → ω < ω' → d σ ω → e σ ω' → ∀ ξ : ℝ, 0 < ξ → ∃ α : ℝ, 0 < α ∧ ∃ ζ : ℝ, 0 < ζ ∧ J (fun ε a η δ => ∀ m : ℝ, 1 ≤ m → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y (K δ m (δ ^ (-η)) n x v ((∀ i, o (δ ^ η * δ ^ 2) ≤ μ (Y i)) → (¬ ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧ S ξ δ k (fun j => x (g j)) (fun j => v (g j))) → (∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ δ ^ η * n ≤ k ∧ ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → o (Set.ncard {j | T δ (x (g j)) (v (g j)) ⊆ W} : ℝ) ≤ o (δ ^ (-ζ) * k) * μ W) → o (a * δ ^ (ω' - α + ε) * m⁻¹ * (n * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * (n * δ)) ^ (-σ)) ≤ μ (⋃ i, Y i))))) (fun ξ δ k x v => ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-ξ) * ρ₀ ∧ ∃ q : ℕ, 0 < q ∧ ∃ z w : Fin q → LeanEval.Analysis.WangZahlKakeya.Space, (∀ j, ‖w j‖ = 1) ∧ (∀ j j', j ≠ j' → μ (T ρ (z j) (w j) ∩ T ρ (z j') (w j')) ≤ (1/2 : ENNReal) * μ (T ρ (z j) (w j))) ∧ (∀ i, ∃! j, T δ (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j, ∃ i, T δ (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j j', (Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j) (w j)} : ℝ) ≤ δ ^ (-ξ) * (Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j') (w j')} : ℝ)) ∧ (∀ j, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j) (w j) ∧ T δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤ o (δ ^ (-ξ) * (Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j) (w j)} : ℝ)) * μ W))) (fun s w => J (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * (N * δ)) ^ (-s))))) (fun s w => J (fun ε a η δ => Q η δ (δ ^ (-η)) (δ ^ (-η)) (fun N => a * δ ^ (w + ε) * (N * δ ^ 2) * (N * δ) ^ (-s))))) (fun η δ m l f => ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y (K δ m l n x v (o (f n) ≤ μ (⋃ i, Y i))))) (fun δ m l n x v P => (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ o m * μ W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → o (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ o (l * n) * μ (B ∩ {p | |inner ℝ u p - t| ≤ r})) → P)) (fun P => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → P ε a η δ)) (fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i j, i ≠ j → μ (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * μ (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → P)) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) ENNReal.ofReal) MeasureTheory.volume) (Metric.ball 0 1)

/-- The core: the improvement for Frostman families alone (no `m`, no slab error). -/
def Core : Prop := ∀ σ ω ω' : ℝ, (fun (B : Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (μ : MeasureTheory.Measure LeanEval.Analysis.WangZahlKakeya.Space) => (fun (o : ℝ → ENNReal) => (fun (T : ℝ → LeanEval.Analysis.WangZahlKakeya.Space → LeanEval.Analysis.WangZahlKakeya.Space → Set LeanEval.Analysis.WangZahlKakeya.Space) => (fun (H : ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space) → Prop → Prop) => (fun (J : (ℝ → ℝ → ℝ → ℝ → Prop) → Prop) => (fun (K : ℝ → ℝ → ℝ → (n : ℕ) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin n → LeanEval.Analysis.WangZahlKakeya.Space) → Prop → Prop) => (fun (Q : ℝ → ℝ → ℝ → ℝ → (ℝ → ℝ) → Prop) => (fun (d : ℝ → ℝ → Prop) => (fun (e : ℝ → ℝ → Prop) => (fun (S : ℝ → ℝ → (k : ℕ) → (Fin k → LeanEval.Analysis.WangZahlKakeya.Space) → (Fin k → LeanEval.Analysis.WangZahlKakeya.Space) → Prop) => 0 < σ → σ ≤ 1/2 → 0 < ω → ω < ω' → d σ ω → e σ ω' → ∀ ξ : ℝ, 0 < ξ → ∃ α : ℝ, 0 < α ∧ ∃ ζ : ℝ, 0 < ζ ∧ J (fun ε a η δ => ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y ((∀ i, o (δ ^ η * δ ^ 2) ≤ μ (Y i)) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → o (Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) ≤ o (δ ^ (-ζ) * n) * μ W) → (¬ ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧ S ξ δ k (fun j => x (g j)) (fun j => v (g j))) → o (a * δ ^ (ω' - α + ε) * (n * δ ^ 4) ^ (σ / 2)) ≤ μ (⋃ i, Y i)))) (fun ξ δ k x v => ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ δ ^ (-ξ) * ρ₀ ∧ ∃ q : ℕ, 0 < q ∧ ∃ z w : Fin q → LeanEval.Analysis.WangZahlKakeya.Space, (∀ j, ‖w j‖ = 1) ∧ (∀ j j', j ≠ j' → μ (T ρ (z j) (w j) ∩ T ρ (z j') (w j')) ≤ (1/2 : ENNReal) * μ (T ρ (z j) (w j))) ∧ (∀ i, ∃! j, T δ (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j, ∃ i, T δ (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j j', (Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j) (w j)} : ℝ) ≤ δ ^ (-ξ) * (Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j') (w j')} : ℝ)) ∧ (∀ j, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j) (w j) ∧ T δ (x i) (v i) ⊆ W} : ℝ) * ρ ^ 2) ≤ o (δ ^ (-ξ) * (Set.ncard {i | T δ (x i) (v i) ⊆ T ρ (z j) (w j)} : ℝ)) * μ W))) (fun s w => J (fun ε a η δ => ∀ m l : ℝ, 1 ≤ m → 1 ≤ l → Q η δ m l (fun N => a * δ ^ (w + ε) * m⁻¹ * (N * δ ^ 2) * (m ^ (-(3/2 : ℝ)) * l * (N * δ)) ^ (-s))))) (fun s w => J (fun ε a η δ => Q η δ (δ ^ (-η)) (δ ^ (-η)) (fun N => a * δ ^ (w + ε) * (N * δ ^ 2) * (N * δ) ^ (-s))))) (fun η δ m l f => ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), H η δ n x v Y (K δ m l n x v (o (f n) ≤ μ (⋃ i, Y i))))) (fun δ m l n x v P => (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → o ((Set.ncard {i | T δ (x i) (v i) ⊆ W} : ℝ) * δ ^ 2) ≤ o m * μ W) → (∀ (u : LeanEval.Analysis.WangZahlKakeya.Space) (t r : ℝ), ‖u‖ = 1 → 0 < r → o (Set.ncard {i | T δ (x i) (v i) ⊆ (B ∩ {p | |inner ℝ u p - t| ≤ r})} : ℝ) ≤ o (l * n) * μ (B ∩ {p | |inner ℝ u p - t| ≤ r})) → P)) (fun P => ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1/100 → P ε a η δ)) (fun η δ n x v Y P => 0 < n → (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ B) → (∀ i j, i ≠ j → μ (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1/2 : ENNReal) * μ (T δ (x i) (v i))) → (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ T δ (x i) (v i)) → o (δ ^ η * n * δ ^ 2) ≤ ∑ i, μ (Y i) → P)) (fun δ x v => Metric.thickening δ (segment ℝ x (x + v)))) ENNReal.ofReal) MeasureTheory.volume) (Metric.ball 0 1)

theorem o038_of_core (hcore : Core) : O038 := by
  intro σ ω ω'
  have hc := hcore σ ω ω'
  beta_reduce at hc ⊢
  intro hσ0 hσ1 hω0 hωω' hd he ξ hξ
  obtain ⟨α, hα, ζ, hζ, hJ⟩ := hc hσ0 hσ1 hω0 hωω' hd he ξ hξ
  refine ⟨α, hα, ζ, hζ, ?_⟩
  intro ε hε
  obtain ⟨c, hc0, ηc, hηc, hδc⟩ := hJ (ε / 2) (by positivity)
  refine ⟨c / 5, by positivity, min ηc ε, lt_min hηc hε, ?_⟩
  intro δ hδ0 hδ1 m hm n x v Y hn hv hTB hov hYm hYT hsum hK hslab hind hnost hfrost
  obtain ⟨k, g, hg, hkn, hgF⟩ := hfrost
  have hδ1' : δ ≤ 1 := by linarith
  have hηle : min ηc ε ≤ ηc := min_le_left _ _
  have hηε : min ηc ε ≤ ε := min_le_right _ _
  have hη0 : 0 < min ηc ε := lt_min hηc hε
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hkpos : 0 < k := by
    have : (0:ℝ) < k := lt_of_lt_of_le (by positivity) hkn
    exact_mod_cast this
  have hδpow : δ ^ ηc ≤ δ ^ (min ηc ε) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1' hηle
  have hind' : ∀ j, ENNReal.ofReal (δ ^ ηc * δ ^ 2) ≤ MeasureTheory.volume (Y (g j)) := fun j =>
    le_trans (ENNReal.ofReal_le_ofReal (by gcongr)) (hind (g j))
  have hsum' : ENNReal.ofReal (δ ^ ηc * (k:ℝ) * δ ^ 2) ≤ ∑ j, MeasureTheory.volume (Y (g j)) := by
    calc ENNReal.ofReal (δ ^ ηc * (k:ℝ) * δ ^ 2)
        = ∑ _j : Fin k, ENNReal.ofReal (δ ^ ηc * δ ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
      _ ≤ ∑ j, MeasureTheory.volume (Y (g j)) := Finset.sum_le_sum fun j _ => hind' j
  have hcore_app := hδc δ hδ0 hδ1 k (fun j => x (g j)) (fun j => v (g j)) (fun j => Y (g j))
    hkpos (fun j => hv (g j)) (fun j => hTB (g j))
    (fun i j hij => hov (g i) (g j) (hg.ne hij)) (fun j => hYm (g j)) (fun j => hYT (g j))
    hsum' hind' hgF
    (by rintro ⟨k', g', hg', hk', hS⟩; exact hnost ⟨k', g ∘ g', hg.comp hg', hk', hS⟩)
  have hKB := hK (Metric.ball 0 1) (convex_ball 0 1)
  have hcard : (({i | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
      Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1}.ncard : ℕ) : ℝ) = n := by
    have : {i | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆
        Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1} = Set.univ := by
      ext i; simp [hTB i]
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [hcard, EuclideanSpace.volume_ball_fin_three] at hKB
  have hKm : (n:ℝ) * δ ^ 2 ≤ 5 * m := by
    have h1 : ENNReal.ofReal ((n:ℝ) * δ ^ 2) ≤ ENNReal.ofReal (5 * m) := by
      refine le_trans hKB ?_
      rw [ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_mul (by linarith)]
      apply ENNReal.ofReal_le_ofReal
      have := Real.pi_lt_d2
      nlinarith
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have hunion : MeasureTheory.volume (⋃ j, Y (g j)) ≤ MeasureTheory.volume (⋃ i, Y i) :=
    MeasureTheory.measure_mono (Set.iUnion_subset fun j => Set.subset_iUnion Y (g j))
  refine le_trans ?_ (le_trans hcore_app hunion)
  apply ENNReal.ofReal_le_ofReal
  exact target_le_core σ (ω' - α) ε (min ηc ε) c δ m n k hσ0 hσ1 hε hη0 hηε hc0 hδ0 hδ1' hm
    hnpos hkn hKm

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy
