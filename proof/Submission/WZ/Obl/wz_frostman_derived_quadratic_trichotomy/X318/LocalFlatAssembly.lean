-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalFlatAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalNormalization
import Submission.WZ.Obl.wz_frostman_derived_quadratic_trichotomy.X318.LocalSaturation

-- Copied from session x0318 (x0210 lineage) (o070 branch, commit 7b9811e, file LocalFlatAssembly.lean), namespace renamed.
namespace WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318

open Set MeasureTheory

def localContributorLoss : ℝ := 576000000 * 7 ^ 4

def localNeighborLoss : ℝ := 147456000000 * 53 ^ 6

/-- The local flat exit, including normalization, retention, and the literal
neighborhood condition in branch C. -/
theorem flat_refinement_of_local_saturated_cover {n p q : ℕ}
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
      (8 * (localContributorLoss * H) * D ^ 2) ≤ δ ^ (-ζ₃)) :
    ∃ (k : ℕ) (g : Fin k → Fin n), Function.Injective g ∧ (n : ℝ) ≤ 2 * k ∧
      FlatPrisms ζ₂ ζ₃ δ (fun i => Tube δ (x (g i)) (v (g i))) := by
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
  refine ⟨k, g, hg, hmass, ?_⟩
  apply flat_prisms_of_local_saturation A P R (label ∘ s) neighbors
    c' (e₁ ∘ s) (e₂ ∘ s) (e₃ ∘ s)
    hδ hδa hab hflat hb1 hk (sq_pos_of_pos hδ) hκ hE
    (by positivity : 0 ≤ 2 * H)
    (by positivity : 0 ≤ 8 * (localContributorLoss * H) * D ^ 2)
    (by positivity : 0 ≤ 2 * K)
    (fun j => he (s j)) (fun _ => rfl) hF' hcover' hlocal hparent' hdegree' hsat'
    ?_ hlabels herrorL herrorM herrorF
  intro j
  convert hneighbors j using 1 <;> norm_num [localNeighborLoss]

end WangZahlLot.Obl.wz_frostman_derived_quadratic_trichotomy.X318
