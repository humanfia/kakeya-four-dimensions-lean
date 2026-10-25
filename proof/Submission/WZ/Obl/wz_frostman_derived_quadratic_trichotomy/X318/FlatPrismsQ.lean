-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.FlatPrismsQ.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.QuadCount
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalFlatQuantitative
-- Copied from session x0338 (o070 branch, commit ec01e52, file FlatPrismsQ.lean), namespace renamed.

/-!
# Frozen `SC` with the quadratic count, through x0210's flat chain

`FlatPrismsQ` is `FlatPrisms` (frozen `SC`) together with the global quadratic count
`#{j | P j ⊆ U} (ab)² ≤ δ^(-ζ₃) |U|²` for the same prisms (the extra hypothesis of x0264's
`countedGain_of_estimateE`, o072).  The `_q_` theorems are x0210's
`flat_prisms_of_bounded_parent_cover`, `flat_prisms_of_local_saturation`,
`flat_refinement_of_local_saturated_cover` and `flat_refinement_of_local_factor` (proofs copied,
same names with `_q_`), carrying the count; it comes from `quad_count_of_parents` applied to the
normalized prisms, for `NetSeparated` parents (`LocalFactorN`).
-/

namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory
open WangZahlLot.Obl.wz_concentrated_convex_factorization

attribute [local instance] Classical.propDecidable

/-- Frozen `SC` (`FlatPrisms`) together with the global quadratic count of the same prisms. -/
def FlatPrismsQ (ζ₂ ζ₃ δ : ℝ) {n : ℕ} (A : Fin n → Set Space) : Prop :=
  ∃ a b : ℝ, δ ≤ a ∧ a ≤ δ ^ (ζ₂ / 200) * b ∧ b ≤ 1 ∧
    ∃ (p : ℕ) (c e₁ e₂ e₃ : Fin p → Space),
      (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧
      (∀ i, ∃ j, A i ⊆ Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ∧
      (∀ j j', (ncard {i | A i ⊆ Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)} : ℝ) ≤
        δ ^ (-ζ₃) * (ncard {i | A i ⊆ Prism a b (c j') (e₁ j') (e₂ j') (e₃ j')} : ℝ)) ∧
      Frostman (δ ^ (-ζ₃)) (fun j => Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ∧
      (∀ j (U : Set Space), Convex ℝ U →
        ENNReal.ofReal (ncard {i | A i ⊆ Prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ∧ A i ⊆ U} : ℝ) *
          volume (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ≤
        ENNReal.ofReal (δ ^ (-ζ₃) * (ncard {i | A i ⊆ Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)} : ℝ)) *
          volume U) ∧
      (∀ j (U : Set Space), Convex ℝ U →
        ENNReal.ofReal (ncard {j' | Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆
          Metric.thickening b (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ∧
          Prism a b (c j') (e₁ j') (e₂ j') (e₃ j') ⊆ U} : ℝ) *
          volume (Prism a b (c j) (e₁ j) (e₂ j) (e₃ j)) ≤
        ENNReal.ofReal (δ ^ (-ζ₃)) * volume U) ∧
      (∀ U : Set Space, Convex ℝ U →
        ENNReal.ofReal (ncard {j | Prism a b (c j) (e₁ j) (e₂ j) (e₃ j) ⊆ U} : ℝ) *
          ENNReal.ofReal ((a * b) ^ 2) ≤ ENNReal.ofReal (δ ^ (-ζ₃)) * volume U ^ 2)

lemma FlatPrismsQ.flatPrisms {ζ₂ ζ₃ δ : ℝ} {n : ℕ} {A : Fin n → Set Space}
    (h : FlatPrismsQ ζ₂ ζ₃ δ A) : FlatPrisms ζ₂ ζ₃ δ A := by
  obtain ⟨a, b, h1, h2, h3, p, c, e₁, e₂, e₃, h4, h5, h6, h7, h8, h9, -⟩ := h
  exact ⟨a, b, h1, h2, h3, p, c, e₁, e₂, e₃, h4, h5, h6, h7, h8, h9⟩

/-- The constant of the quadratic count at the local-factor level. -/
def quadLoss : ℝ := 4 * 27 ^ 3 * localContributorLoss ^ 2

/-- `flat_prisms_of_bounded_parent_cover` for the same prisms, with their quadratic count. -/
theorem flat_prisms_q_of_bounded_parent_cover {I : Type*} {n p : ℕ}
    (A : Fin n → Set Space) (P : Fin p → Set Space)
    (c e₁ e₂ e₃ : Fin p → Space) (label : Fin p → I) (neighbors : Fin p → Finset I)
    {δ ζ₂ ζ₃ a b K L D E M : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b)
    (hflat : a ≤ δ ^ (ζ₂ / 200) * b) (hb1 : b ≤ 1)
    (hn : 0 < n) (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (herrorL : L ≤ δ ^ (-ζ₃)) (herrorM : E * M ≤ δ ^ (-ζ₃))
    (herrorF : K * L * D ≤ δ ^ (-ζ₃))
    (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j])
    (hP : ∀ j, P j = Prism a b (c j) (e₁ j) (e₂ j) (e₃ j))
    (hF : Frostman K A)
    (hcover : ∀ i, ∃ j, A i ⊆ P j)
    (hbalance : ∀ j j', (contained A (P j) : ℝ) ≤ L * contained A (P j'))
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D)
    (hbelow : ∀ j U, Convex ℝ U →
      ENNReal.ofReal (ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * volume (P j) ≤
        ENNReal.ofReal (L * contained A (P j)) * volume U)
    (hneighbors : ∀ j, ((neighbors j).card : ℝ) ≤ E)
    (hlabel : ∀ j j', P j' ⊆ Metric.thickening b (P j) → label j' ∈ neighbors j)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal (ncard {j | label j = l ∧ P j ⊆ U} : ℝ) *
        ENNReal.ofReal (8 * a * b) ≤ ENNReal.ofReal M * volume U)
    (hQ : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (ncard {j | P j ⊆ U} : ℝ) * ENNReal.ofReal ((a * b) ^ 2) ≤
        ENNReal.ofReal (δ ^ (-ζ₃)) * volume U ^ 2) :
    FlatPrismsQ ζ₂ ζ₃ δ A := by
  have ha : 0 ≤ a := hδ.le.trans hδa
  have hb : 0 ≤ b := ha.trans hab
  have hFP : Frostman (δ ^ (-ζ₃)) P :=
    (frostman_of_balanced_cover A P hn hK hL hD hF hcover hbalance hdegree).mono herrorF
  have hbal (j j') : (contained A (P j) : ℝ) ≤
      δ ^ (-ζ₃) * contained A (P j') :=
    (hbalance j j').trans (mul_le_mul_of_nonneg_right herrorL (Nat.cast_nonneg _))
  have hlocal (j) (U : Set Space) (hU : Convex ℝ U) :
      ENNReal.ofReal (ncard {j' | P j' ⊆ Metric.thickening b (P j) ∧ P j' ⊆ U} : ℝ) *
        volume (P j) ≤ ENNReal.ofReal (δ ^ (-ζ₃)) * volume U := by
    have hvol : volume (P j) = ENNReal.ofReal (8 * a * b) := by
      rw [hP j]
      exact prism_volume ha hb _ _ _ _ (he j)
    rw [hvol]
    exact (local_kt_of_bounded_parent_labels P label neighbors hM hneighbors hlabel hparent j U hU).trans
      (mul_le_mul' (ENNReal.ofReal_le_ofReal herrorM) le_rfl)
  have hbelow' (j) (U : Set Space) (hU : Convex ℝ U) :
      ENNReal.ofReal (ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * volume (P j) ≤
        ENNReal.ofReal (δ ^ (-ζ₃) * contained A (P j)) * volume U :=
    (hbelow j U hU).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right herrorL (Nat.cast_nonneg _))) le_rfl)
  refine ⟨a, b, hδa, hflat, hb1, p, c, e₁, e₂, e₃, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← hP] using hcover
  · simpa only [← hP, contained] using hbal
  · simpa only [← hP] using hFP
  · simpa only [← hP, contained] using hbelow'
  · simpa only [← hP] using hlocal
  · simpa only [← hP] using hQ

/-- `flat_prisms_of_local_saturation` for the same prisms, with their quadratic count. -/
theorem flat_prisms_q_of_local_saturation {n p q : ℕ}
    (A : Fin n → Set Space) (P : Fin p → Set Space) (R : Fin q → Set Space)
    (label : Fin p → Fin q) (neighbors : Fin p → Finset (Fin q))
    (c e₁ e₂ e₃ : Fin p → Space) {δ ζ₂ ζ₃ a b w κ E L D M K : ℝ}
    (hδ : 0 < δ) (hδa : δ ≤ a) (hab : a ≤ b)
    (hflat : a ≤ δ ^ (ζ₂ / 200) * b) (hb1 : b ≤ 1)
    (hn : 0 < n) (hw : 0 < w) (hκ : 0 < κ) (hE : 0 < E)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j])
    (hP : ∀ j, P j = Prism a b (c j) (e₁ j) (e₂ j) (e₃ j))
    (hF : Frostman K A) (hcover : ∀ i, ∃ j, A i ⊆ P j)
    (hlocal : ∀ j U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * w) ≤
        ENNReal.ofReal (κ * E) * volume U)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ R l ∧ A i ⊆ U} : ℝ) * w) ≤
        ENNReal.ofReal κ * volume U)
    (hdegree : ∀ i, (ncard {j | A i ⊆ P j} : ℝ) ≤ D)
    (hsat : ∀ j, κ * (8 * a * b) ≤ L * (ncard {i | A i ⊆ R (label j) ∧ A i ⊆ P j} : ℝ) * w)
    (hneighbors : ∀ j, ((neighbors j).card : ℝ) ≤ M)
    (hlabel : ∀ j j', P j' ⊆ Metric.thickening b (P j) → label j' ∈ neighbors j)
    (herrorL : E * L ≤ δ ^ (-ζ₃)) (herrorM : M * (L * D) ≤ δ ^ (-ζ₃))
    (herrorF : K * (E * L) * D ≤ δ ^ (-ζ₃))
    (hQ : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (ncard {j | P j ⊆ U} : ℝ) * ENNReal.ofReal ((a * b) ^ 2) ≤
        ENNReal.ofReal (δ ^ (-ζ₃)) * volume U ^ 2) :
    FlatPrismsQ ζ₂ ζ₃ δ A := by
  have ha : 0 ≤ a := hδ.le.trans hδa
  have hb : 0 ≤ b := ha.trans hab
  have hPV (j) : Convex ℝ (P j) ∧ volume (P j) = ENNReal.ofReal (8 * a * b) := by
    rw [hP j]
    exact ⟨prism_convex _ _ _ _ _ _, prism_volume ha hb _ _ _ _ (he j)⟩
  obtain ⟨hbalance, hKT, hbelow⟩ := locally_saturated_cover_bounds A P R label
    hw (by positivity : 0 ≤ 8 * a * b) hκ hE hL hD hlocal hparent hPV hdegree hsat
  apply flat_prisms_q_of_bounded_parent_cover A P c e₁ e₂ e₃ label neighbors
    hδ hδa hab hflat hb1 hn hK (by positivity) hD (by positivity)
    herrorL herrorM herrorF he hP hF hcover hbalance hdegree
  · intro j U hU
    rw [(hPV j).2, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact hbelow j U hU
  · exact hneighbors
  · exact hlabel
  · intro l U hU
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact hKT l U hU
  · exact hQ

/-- `flat_refinement_of_local_saturated_cover` with the quadratic count of the output prisms,
for `NetSeparated` parents (`τ ≤ 1/100`). -/
theorem flat_refinement_q_of_local_saturated_cover {n p q : ℕ}
    {δ τ a b κ H D K ζ₂ ζ₃ : ℝ}
    (hδ : 0 < δ) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (hδa : δ ≤ a) (hab : a ≤ b) (hbτ : b ≤ τ)
    (hflat : a ≤ δ ^ (ζ₂ / 200) * b)
    (hκ : 0 < κ) (hH : 0 < H) (hD : 1 ≤ D) (hK : 0 ≤ K) (hn : 0 < n)
    (x v : Fin n → Space) (hv : ∀ i, ‖v i‖ = 1)
    (hF : Frostman K (fun i => Tube δ (x i) (v i)))
    (z w : Fin q → Space) (hw : ∀ l, ‖w l‖ = 1)
    (hsep : Distinct (fun l => Tube τ (z l) (w l)))
    (W : Fin p → Set Space) (label : Fin p → Fin q)
    (c e₁ e₂ e₃ : Fin p → Space) (he : ∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j])
    (hshape : ∀ j, W j ⊆ Tube τ (z (label j)) (w (label j)) ∩
      {y | |inner ℝ (e₁ j) (y - c j)| ≤ a ∧ |inner ℝ (e₂ j) (y - c j)| ≤ b})
    (hcover : ∀ i, ∃ j, Tube δ (x i) (v i) ⊆ W j)
    (hdegree : ∀ i, (ncard {j | Tube δ (x i) (v i) ⊆ W j} : ℝ) ≤ D)
    (hparent : ∀ l U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | Tube δ (x i) (v i) ⊆ Tube τ (z l) (w l) ∧
        Tube δ (x i) (v i) ⊆ U} : ℝ) * δ ^ 2) ≤ ENNReal.ofReal κ * volume U)
    (hsat : ∀ j, κ * (8 * a * b) ≤
      H * (contained (fun i => Tube δ (x i) (v i)) (W j) : ℝ) * δ ^ 2)
    (herrorL : localContributorLoss * (2 * H) ≤ δ ^ (-ζ₃))
    (herrorM : localNeighborLoss * ((2 * H) * (8 * (localContributorLoss * H) * D ^ 2)) ≤ δ ^ (-ζ₃))
    (herrorF : (2 * K) * (localContributorLoss * (2 * H)) *
      (8 * (localContributorLoss * H) * D ^ 2) ≤ δ ^ (-ζ₃))
    (hnet : WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.NetSeparated τ z w) (hτ100 : τ ≤ 1 / 100)
    (herrorQ : 27 ^ 3 * ((2 * H) * (8 * (localContributorLoss * H) * D ^ 2)) ^ 2 ≤
      64 * δ ^ (-ζ₃)) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ (n : ℝ) ≤ 2 * k ∧
      FlatPrismsQ ζ₂ ζ₃ δ (fun i => Tube δ (x (g i)) (v (g i))) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hb1 : b ≤ 1 := hbτ.trans (by linarith)
  have hE : 0 < localContributorLoss := by norm_num [localContributorLoss]
  obtain ⟨k, g, r, s, c', hg, _hs, hmass, hcenter, haxis, hcover', hdegree', hsat'⟩ :=
    normalize_local_saturated_cover hδ hτ hτhalf ha hab hbτ hκ hH hD
      x v hv z w hw hsep W label c e₁ e₂ e₃ he hshape hcover hdegree hparent hsat
  let A := fun i => Tube δ (x (g i)) (v (g i))
  let P := fun j => Prism a b (c' j) (e₁ (s j)) (e₂ (s j)) (e₃ (s j))
  let R := fun l => Tube τ (z l) (w l)
  have hk : 0 < k := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hk' : (0 : ℝ) < k := by linarith
    exact_mod_cast hk'
  have hF' : Frostman (2 * K) A := by
    simpa only [mul_comm K 2] using hF.restrict hK g hg hmass
  have hparent' : ∀ l U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ R l ∧ A i ⊆ U} : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal κ * volume U := by
    intro l U hU
    have hc : ncard {i | A i ⊆ R l ∧ A i ⊆ U} ≤
        ncard {i | Tube δ (x i) (v i) ⊆ R l ∧ Tube δ (x i) (v i) ⊆ U} :=
      Set.ncard_le_ncard_of_injOn g (fun _ h => h) hg.injOn
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc)
      (sq_nonneg δ))).trans (hparent l U hU)
  have hcoarse (i) : ∃ l, A i ⊆ R l := by
    obtain ⟨j, hj⟩ := hcover (g i)
    exact ⟨label j, fun y hy => (hshape j (hj hy)).1⟩
  have hlocal : ∀ j U, Convex ℝ U →
      ENNReal.ofReal ((ncard {i | A i ⊆ P j ∧ A i ⊆ U} : ℝ) * δ ^ 2) ≤
        ENNReal.ofReal (κ * localContributorLoss) * volume U := by
    intro j U hU
    convert parentwise_katzTao_in_prism hδ hτ hτhalf ha.le hab
      (by simpa using hbτ : b ≤ 1 * τ) zero_le_one hκ.le
      (x ∘ g) (v ∘ g) (fun i => hv (g i)) z w hw hsep hcoarse hparent'
      (c' j) (e₁ (s j)) (e₂ (s j)) (e₃ (s j)) (he (s j)) U hU using 1 <;>
      norm_num [A, P, localContributorLoss, mul_comm κ]
  obtain ⟨neighbors, hneighbors, hlabels⟩ := bounded_coarse_parent_neighbors_unit
    hτ (by linarith) (by norm_num : (0 : ℝ) ≤ 8) ha.le hab hbτ hb1
    z w hw hsep c' (e₁ ∘ s) (e₂ ∘ s) (e₃ ∘ s) (fun j => he (s j)) (label ∘ s)
    (fun j => (hcenter j).trans (by linarith)) haxis
  have hQ : ∀ U : Set Space, Convex ℝ U →
      ENNReal.ofReal (ncard {j | P j ⊆ U} : ℝ) * ENNReal.ofReal ((a * b) ^ 2) ≤
        ENNReal.ofReal (δ ^ (-ζ₃)) * volume U ^ 2 := by
    intro U hU
    have hq := quad_count_of_parents (s₀ := 8 * a * b) (H := 2 * H)
      (D := 8 * (localContributorLoss * H) * D ^ 2) hδ hτ hτ100 hκ (by positivity)
      (by positivity) (mul_pos (mul_pos (by norm_num) ha) (ha.trans_le hab))
      (x ∘ g) (v ∘ g) (fun i => hv (g i)) z w hw hnet
      P (label ∘ s) hparent' hdegree' hsat' U hU
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have h64 : ENNReal.ofReal ((ncard {j | P j ⊆ U} : ℝ) * (a * b) ^ 2) =
        ENNReal.ofReal (1 / 64) *
          ENNReal.ofReal ((ncard {j | P j ⊆ U} : ℝ) * (8 * a * b) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    have hc : 27 ^ 3 * ((2 * H) * (8 * (localContributorLoss * H) * D ^ 2)) ^ 2 / 64 ≤
        δ ^ (-ζ₃) := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    rw [h64]
    calc ENNReal.ofReal (1 / 64) *
          ENNReal.ofReal ((ncard {j | P j ⊆ U} : ℝ) * (8 * a * b) ^ 2)
        ≤ ENNReal.ofReal (1 / 64) * (ENNReal.ofReal (27 ^ 3 * ((2 * H) *
            (8 * (localContributorLoss * H) * D ^ 2)) ^ 2) * volume U ^ 2) :=
          mul_le_mul' le_rfl hq
      _ = ENNReal.ofReal (27 ^ 3 * ((2 * H) * (8 * (localContributorLoss * H) * D ^ 2)) ^ 2 /
            64) * volume U ^ 2 := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
          congr 2
          ring
      _ ≤ ENNReal.ofReal (δ ^ (-ζ₃)) * volume U ^ 2 :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl
  refine ⟨k, g, hg, hmass, ?_⟩
  apply flat_prisms_q_of_local_saturation A P R (label ∘ s) neighbors
    c' (e₁ ∘ s) (e₂ ∘ s) (e₃ ∘ s)
    hδ hδa hab hflat hb1 hk (sq_pos_of_pos hδ) hκ hE
    (by positivity : 0 ≤ 2 * H)
    (by positivity : 0 ≤ 8 * (localContributorLoss * H) * D ^ 2)
    (by positivity : 0 ≤ 2 * K)
    (fun j => he (s j)) (fun _ => rfl) hF' hcover' hlocal hparent' hdegree' hsat'
    ?_ hlabels herrorL herrorM herrorF hQ
  intro j
  convert hneighbors j using 1 <;> norm_num [localNeighborLoss]

/-- `LocalFactor` whose parents form a `NetSeparated` net. -/
def LocalFactorN (ν δ τ a b : ℝ) {n : ℕ} (A : Fin n → Set Space) : Prop :=
  ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ 0 < k ∧ δ ^ ν * n ≤ k ∧
    ∃ (q : ℕ) (z w : Fin q → Space), (∀ l, ‖w l‖ = 1) ∧ WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.NetSeparated τ z w ∧
      Distinct (fun l => Tube τ (z l) (w l)) ∧
      ∃ κ : ℝ, 0 < κ ∧
        (∀ l U, Convex ℝ U →
          ENNReal.ofReal ((ncard {i | A (g i) ⊆ Tube τ (z l) (w l) ∧ A (g i) ⊆ U} : ℝ) * δ ^ 2) ≤
            ENNReal.ofReal κ * volume U) ∧
        ∃ (p : ℕ) (W : Fin p → Set Space) (label : Fin p → Fin q)
          (c e₁ e₂ e₃ : Fin p → Space),
          (∀ j, Orthonormal ℝ ![e₁ j, e₂ j, e₃ j]) ∧
          (∀ j, W j ⊆ Tube τ (z (label j)) (w (label j)) ∩
            {y | |inner ℝ (e₁ j) (y - c j)| ≤ a ∧ |inner ℝ (e₂ j) (y - c j)| ≤ b}) ∧
          (∀ i, ∃ j, A (g i) ⊆ W j) ∧
          (∀ i, (ncard {j | A (g i) ⊆ W j} : ℝ) ≤ δ ^ (-ν)) ∧
          (∀ j, δ ^ ν * κ * (8 * a * b) ≤
            (contained (fun i => A (g i)) (W j) : ℝ) * δ ^ 2)

/-- `flat_refinement_of_local_factor` with the quadratic count, for `NetSeparated` parents. -/
theorem flat_refinement_q_of_local_factor {n : ℕ} (x v : Fin n → Space)
    {ν δ τ ζ ζ₂ ζ₃ θ a b : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2)
    (hν : 0 ≤ ν) (hζ : 0 ≤ ζ)
    (hδa : δ ≤ a) (hab : a ≤ b) (hbτ : b ≤ τ)
    (hflat : a ≤ δ ^ (ζ₂ / 200) * b)
    (herror : localFlatLoss * δ ^ (ζ₃ - ζ - 5 * ν) ≤ 1)
    (hretain : 2 * δ ^ (θ - ν) ≤ 1)
    (hv : ∀ i, ‖v i‖ = 1)
    (hF : Frostman (δ ^ (-ζ)) (fun i => Tube δ (x i) (v i)))
    (hτ100 : τ ≤ 1 / 100) (herrorQ : quadLoss * δ ^ (ζ₃ - 8 * ν) ≤ 1)
    (hfactor : LocalFactorN ν δ τ a b (fun i => Tube δ (x i) (v i))) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ δ ^ θ * n ≤ k ∧
      FlatPrismsQ ζ₂ ζ₃ δ (fun i => Tube δ (x (g i)) (v (g i))) := by
  obtain ⟨k, g, hg, hk, hsize, q, z, w, hw, hnet, hsep, κ, hκ, hparent,
    p, W, label, c, e₁, e₂, e₃, he, hshape, hcover, hdegree, hsat⟩ := hfactor
  have hFg := hF.restrict_power hδ g hg hsize
  have hprod : δ ^ (-ν) * δ ^ ν = 1 := by rw [← Real.rpow_add hδ]; simp
  have hsat' (j) : κ * (8 * a * b) ≤ δ ^ (-ν) *
      (contained (fun i => Tube δ (x (g i)) (v (g i))) (W j) : ℝ) * δ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left (hsat j) (Real.rpow_nonneg hδ.le (-ν))
    simpa only [← mul_assoc, hprod, one_mul] using hh
  have herr : localFlatLoss * δ ^ (ζ₃ - (ζ + ν) - 4 * ν) ≤ 1 := by
    convert herror using 1 <;> congr 2 <;> ring
  obtain ⟨hE₁, hE₂, hE₃⟩ := local_factor_error_bounds hδ hδ1 hν (add_nonneg hζ hν) herr
  have hEQ : 27 ^ 3 * ((2 * δ ^ (-ν)) * (8 * (localContributorLoss * δ ^ (-ν)) *
      (δ ^ (-ν)) ^ 2)) ^ 2 ≤ 64 * δ ^ (-ζ₃) := by
    have h8 : (δ ^ (-ν)) ^ 8 = δ ^ (-(8 * ν)) := by
      rw [← Real.rpow_mul_natCast hδ.le]
      congr 1
      push_cast
      ring
    have hex : -(8 * ν) - -ζ₃ = ζ₃ - 8 * ν := by ring
    have habs := mul_rpow_le_of_absorbed (α := -(8 * ν)) (β := -ζ₃) (C := quadLoss) hδ
      (by rw [hex]; exact herrorQ)
    calc 27 ^ 3 * ((2 * δ ^ (-ν)) * (8 * (localContributorLoss * δ ^ (-ν)) *
          (δ ^ (-ν)) ^ 2)) ^ 2
        = 64 * (quadLoss * (δ ^ (-ν)) ^ 8) := by unfold quadLoss; ring
      _ = 64 * (quadLoss * δ ^ (-(8 * ν))) := by rw [h8]
      _ ≤ 64 * δ ^ (-ζ₃) := by linarith
  obtain ⟨m, f, hf, hmass, hC⟩ := flat_refinement_q_of_local_saturated_cover
    hδ hτ hτhalf hδa hab hbτ hflat hκ (Real.rpow_pos_of_pos hδ _)
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hν))
    (Real.rpow_nonneg hδ.le _) hk (x ∘ g) (v ∘ g) (fun i => hv (g i)) hFg
    z w hw hsep W label c e₁ e₂ e₃ he hshape hcover hdegree hparent hsat' hE₁ hE₂ hE₃
    hnet hτ100 hEQ
  refine ⟨m, g ∘ f, hg.comp hf, ?_, hC⟩
  have hp : 2 * δ ^ θ ≤ δ ^ ν := mul_rpow_le_of_absorbed hδ hretain
  have hh := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg n)
  nlinarith only [hh, hsize, hmass]

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
