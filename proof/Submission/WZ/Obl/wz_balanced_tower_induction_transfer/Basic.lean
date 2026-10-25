-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_balanced_tower_induction_transfer.Basic.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Basic
import Submission.WZ.Obl.wz_nonflat_factored_improvement.CoarseGeometry
import Submission.WZ.Obl.wz_nonflat_factored_improvement.RealWeight

namespace WangZahlLot.Obl.wz_balanced_tower_induction_transfer

open MeasureTheory
open scoped ENNReal

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Admissible := WangZahlLot.Obl.wz_tower_balanced_refinement.Admissible

/-- The induction uses the tower certificates only through their two interfaces. -/
abbrev TowerPredicate := Bool → ℝ → ℝ → ℝ → ℕ →
  (n : ℕ) → (Fin n → Space) → (Fin n → Space) → (Fin n → Set Space) → Prop

noncomputable abbrev gap (ω : ℝ) (q : ℕ) : ℝ :=
  (2 - (1 / 2 : ℝ) ^ q) * (1 - ω / 100) ^ q

noncomputable abbrev gain (σ ω α κ δ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (κ * δ ^ (ω - α) * (n * δ ^ 2) * (n * δ) ^ (-σ))

def Depth (σ ω : ℝ) (H : TowerPredicate) (q : ℕ) : Prop :=
  ∀ ε D : ℝ, 0 < ε → 0 < D → ∃ α : ℝ, 0 < α ∧ ∃ κ : ℝ, 0 < κ ∧
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
    Admissible δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y →
    gain σ ω α κ δ n ≤ volume (⋃ i, Y i) ∨
    (δ ≤ D ∧ ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M L : ℝ),
      Admissible δ ε M L m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
      ENNReal.ofReal (δ ^ ε) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
      H true δ (δ ^ (-ε)) (gap ω q) (2 ^ q) m x' v' Y')

def Insertion (σ ω : ℝ) (H : TowerPredicate) (g h : ℝ) (B : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ α κ θ d₀ : ℝ,
    0 < α ∧ 0 < κ ∧ 0 < θ ∧ 0 < d₀ ∧ θ ≤ ε / 8 ∧ θ ≤ α / 8 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d₀ →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (M L : ℝ),
    Admissible δ θ M L n x v Y → H true δ (δ ^ (-θ)) g B n x v Y →
    gain σ ω α κ δ n ≤ volume (⋃ i, Y i) ∨
    ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M' L' : ℝ),
      Admissible δ ε M' L' m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
      ENNReal.ofReal (δ ^ (ε / 4)) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
      H false δ (δ ^ (-ε)) h (2 * B) m x' v' Y'

def Exactification (H : TowerPredicate) (g h : ℝ) (B : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ θ d₀ : ℝ, 0 < θ ∧ 0 < d₀ ∧ θ ≤ ε / 8 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → δ ≤ d₀ →
    ∀ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space) (M L : ℝ),
    Admissible δ θ M L n x v Y → H false δ (δ ^ (-θ)) g B n x v Y →
    ∃ (m : ℕ) (x' v' : Fin m → Space) (Y' : Fin m → Set Space) (M' L' : ℝ),
      Admissible δ ε M' L' m x' v' Y' ∧ (⋃ j, Y' j) ⊆ (⋃ i, Y i) ∧
      ENNReal.ofReal (δ ^ (ε / 4)) * (∑ i, volume (Y i)) ≤ ∑ j, volume (Y' j) ∧
      H true δ (δ ^ (-ε)) h B m x' v' Y'

lemma admissible_weaken {δ η η' : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hη : η ≤ η') {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hA : Admissible δ η (δ ^ (-η)) (δ ^ (-η)) n x v Y) :
    Admissible δ η' (δ ^ (-η')) (δ ^ (-η')) n x v Y := by
  refine ⟨hA.1, hA.2.1, hA.2.2.1, ?_, ?_, ?_⟩
  · apply le_trans _ hA.2.2.2.1
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hη) (Nat.cast_nonneg n))
      (sq_nonneg δ)
  · apply WangZahlLot.Obl.wz_tower_balanced_refinement.convexCount_mono hA.2.2.2.2.1
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)
  · intro u t r hu hr
    apply (hA.2.2.2.2.2 u t r hu hr).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (neg_le_neg hη)) (Nat.cast_nonneg n)

lemma admissible_mass_upper {δ η M L : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hA : Admissible δ η M L n x v Y) :
    (∑ i, volume (Y i)) ≤ ENNReal.ofReal (56 * n * δ ^ 2) := by
  calc
    _ ≤ ∑ _i : Fin n, ENNReal.ofReal (56 * δ ^ 2) :=
      Finset.sum_le_sum (fun i _ => (measure_mono (hA.2.1 i).2.2.2).trans
        (WangZahlLot.Obl.wz_nonflat_factored_improvement.tube_volume_upper
          hδ.le hδ1 _ _ (hA.2.1 i).1))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

lemma retained_cardinality {δ η θ η' M L M' L' : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n m : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    {x' v' : Fin m → Space} {Y' : Fin m → Set Space}
    (hA : Admissible δ η M L n x v Y)
    (hA' : Admissible δ η' M' L' m x' v' Y')
    (hmass : ENNReal.ofReal (δ ^ θ) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Y' i)) :
    (δ ^ (θ + η) / 56) * n ≤ (m : ℝ) := by
  have hlo : ENNReal.ofReal (δ ^ (θ + η) * n * δ ^ 2) ≤
      ENNReal.ofReal (56 * m * δ ^ 2) := by
    calc
      _ = ENNReal.ofReal (δ ^ θ) * ENNReal.ofReal (δ ^ η * n * δ ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_add hδ]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (δ ^ θ) * (∑ i, volume (Y i)) :=
        mul_le_mul' le_rfl hA.2.2.2.1
      _ ≤ _ := hmass.trans (admissible_mass_upper hδ hδ1 hA')
  have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 56 * m * δ ^ 2)).mp hlo
  have hh' := (mul_le_mul_iff_left₀ (sq_pos_of_pos hδ)).mp hh
  linarith

lemma gain_mono {σ ω α α' κ κ' δ : ℝ} {n : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hκ : 0 ≤ κ) (hα : α ≤ α') (hκ' : κ ≤ κ') :
    gain σ ω α κ δ n ≤ gain σ ω α' κ' δ n := by
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul hκ'
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
    (by positivity) (hκ.trans hκ')

lemma gain_transfer {σ ω α α' κ κ' δ t : ℝ} {n m : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < n)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hκ' : 0 ≤ κ')
    (ht : 0 ≤ t) (hα : α + t ≤ α') (hk : κ ≤ κ' / 56)
    (hcard : (δ ^ t / 56) * n ≤ (m : ℝ)) :
    gain σ ω α κ δ n ≤ gain σ ω α' κ' δ m := by
  have hf : 0 < δ ^ t / 56 := by positivity
  have hf1 : δ ^ t / 56 ≤ 1 := by
    have := Real.rpow_le_one hδ.le hδ1 ht
    linarith
  have hcount := WangZahlLot.Obl.wz_nonflat_factored_improvement.count_power_fraction
    hδ (Nat.cast_pos.mpr hn) hf hf1 hcard hσ hσ1
  have hcount' : (δ ^ t / 56) * ((n : ℝ) * δ ^ 2 * (n * δ) ^ (-σ)) ≤
      (m : ℝ) * δ ^ 2 * (m * δ) ^ (-σ) := by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right hcount (sq_nonneg δ)
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (κ' / 56) * δ ^ (ω - α' + t) * (n * δ ^ 2) * (n * δ) ^ (-σ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hk
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
        (by positivity) (by positivity)
    _ = (κ' * δ ^ (ω - α')) *
        ((δ ^ t / 56) * ((n : ℝ) * δ ^ 2 * (n * δ) ^ (-σ))) := by
      rw [Real.rpow_add hδ]
      ring
    _ ≤ (κ' * δ ^ (ω - α')) * ((m : ℝ) * δ ^ 2 * (m * δ) ^ (-σ)) :=
      mul_le_mul_of_nonneg_left hcount' (by positivity)
    _ = _ := by ring

lemma compose_mass {δ a b c ε : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbudget : a + b + c ≤ ε) {s₀ s₁ s₂ s₃ : ℝ≥0∞}
    (h₁ : ENNReal.ofReal (δ ^ a) * s₀ ≤ s₁)
    (h₂ : ENNReal.ofReal (δ ^ b) * s₁ ≤ s₂)
    (h₃ : ENNReal.ofReal (δ ^ c) * s₂ ≤ s₃) :
    ENNReal.ofReal (δ ^ ε) * s₀ ≤ s₃ := by
  calc
    _ ≤ ENNReal.ofReal (δ ^ (a + b + c)) * s₀ :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hbudget)) le_rfl
    _ = ENNReal.ofReal (δ ^ c) *
        (ENNReal.ofReal (δ ^ b) * (ENNReal.ofReal (δ ^ a) * s₀)) := by
      rw [Real.rpow_add hδ, Real.rpow_add hδ,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      ac_rfl
    _ ≤ ENNReal.ofReal (δ ^ c) * (ENNReal.ofReal (δ ^ b) * s₁) := by gcongr
    _ ≤ ENNReal.ofReal (δ ^ c) * s₂ := mul_le_mul' le_rfl h₂
    _ ≤ s₃ := h₃

end WangZahlLot.Obl.wz_balanced_tower_induction_transfer
